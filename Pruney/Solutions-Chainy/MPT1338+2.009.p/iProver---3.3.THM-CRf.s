%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:01 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 2.94s
% Verified   : 
% Statistics : Number of formulae       :  191 (2189 expanded)
%              Number of clauses        :  118 ( 608 expanded)
%              Number of leaves         :   21 ( 650 expanded)
%              Depth                    :   28
%              Number of atoms          :  642 (15672 expanded)
%              Number of equality atoms :  278 (5369 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   20 (   2 average)
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
               => ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0)
                  & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1) ) ) ) ) ) ),
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
                 => ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0)
                    & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

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
    inference(ennf_transformation,[],[f18])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f46,plain,(
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

fof(f45,plain,(
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

fof(f44,plain,
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

fof(f47,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f41,f46,f45,f44])).

fof(f80,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f47])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f72,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f77,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f75,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f81,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f78,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f79,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f47])).

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
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f82,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f10,axiom,(
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

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f54,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f83,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f76,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f4,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1487,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_24,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_33,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_370,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_33])).

cnf(c_371,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_370])).

cnf(c_35,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_375,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_35])).

cnf(c_376,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_375])).

cnf(c_1525,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1487,c_371,c_376])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1494,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2681,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1525,c_1494])).

cnf(c_29,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1518,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_29,c_371,c_376])).

cnf(c_2782,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2681,c_1518])).

cnf(c_2848,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2782,c_1525])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_8,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_18,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_382,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_8,c_18])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_386,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_382,c_18,c_8,c_7])).

cnf(c_387,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_386])).

cnf(c_468,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(resolution,[status(thm)],[c_20,c_387])).

cnf(c_472,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_468,c_20,c_7,c_382])).

cnf(c_473,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(renaming,[status(thm)],[c_472])).

cnf(c_1483,plain,
    ( k1_relat_1(X0) = X1
    | k1_xboole_0 = X2
    | v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_473])).

cnf(c_4212,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2848,c_1483])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1486,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1515,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1486,c_371,c_376])).

cnf(c_2849,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2782,c_1515])).

cnf(c_2875,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2849])).

cnf(c_4221,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4212])).

cnf(c_4381,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4212,c_32,c_2875,c_4221])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_28,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_599,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_28])).

cnf(c_600,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_599])).

cnf(c_604,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_600,c_32])).

cnf(c_605,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_604])).

cnf(c_1478,plain,
    ( k2_relset_1(X0,X1,sK2) != X1
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_605])).

cnf(c_2426,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1518,c_1478])).

cnf(c_2774,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2426,c_1515,c_1525])).

cnf(c_2844,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2782,c_2774])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1488,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4353,plain,
    ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(sK2)
    | k2_struct_0(sK0) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2844,c_1488])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_575,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_28])).

cnf(c_576,plain,
    ( v1_funct_2(k2_funct_1(sK2),X0,X1)
    | ~ v1_funct_2(sK2,X1,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X1,X0,sK2) != X0 ),
    inference(unflattening,[status(thm)],[c_575])).

cnf(c_580,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_2(sK2,X1,X0)
    | v1_funct_2(k2_funct_1(sK2),X0,X1)
    | k2_relset_1(X1,X0,sK2) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_576,c_32])).

cnf(c_581,plain,
    ( v1_funct_2(k2_funct_1(sK2),X0,X1)
    | ~ v1_funct_2(sK2,X1,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | k2_relset_1(X1,X0,sK2) != X0 ),
    inference(renaming,[status(thm)],[c_580])).

cnf(c_1479,plain,
    ( k2_relset_1(X0,X1,sK2) != X1
    | v1_funct_2(k2_funct_1(sK2),X1,X0) = iProver_top
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_581])).

cnf(c_2086,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1518,c_1479])).

cnf(c_2235,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2086,c_1515,c_1525])).

cnf(c_2847,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2782,c_2235])).

cnf(c_5047,plain,
    ( k2_struct_0(sK0) = k1_xboole_0
    | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4353,c_2847])).

cnf(c_5048,plain,
    ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(sK2)
    | k2_struct_0(sK0) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5047])).

cnf(c_3879,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_2844,c_1494])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_637,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_28])).

cnf(c_638,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_637])).

cnf(c_640,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_638,c_32])).

cnf(c_677,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_640])).

cnf(c_678,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_677])).

cnf(c_1477,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_678])).

cnf(c_1708,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_678])).

cnf(c_2429,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1477,c_30,c_1708])).

cnf(c_3881,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_3879,c_2429])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_527,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_28])).

cnf(c_528,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_527])).

cnf(c_532,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_528,c_32])).

cnf(c_533,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_532])).

cnf(c_1481,plain,
    ( k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_533])).

cnf(c_2245,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1518,c_1481])).

cnf(c_2339,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2245,c_1515,c_1525])).

cnf(c_27,negated_conjecture,
    ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1596,plain,
    ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_27,c_371,c_376])).

cnf(c_2342,plain,
    ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_2339,c_1596])).

cnf(c_2845,plain,
    ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2)
    | k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_2782,c_2342])).

cnf(c_4066,plain,
    ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2)
    | k2_struct_0(sK0) != k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_3881,c_2845])).

cnf(c_5053,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_struct_0(sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5048,c_4066])).

cnf(c_5830,plain,
    ( k2_struct_0(sK0) = k1_xboole_0
    | k2_relat_1(sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4381,c_5053])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1495,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3869,plain,
    ( v1_xboole_0(k2_struct_0(sK0)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2848,c_1495])).

cnf(c_6363,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5830,c_3869])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_112,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6780,plain,
    ( v1_xboole_0(sK2) = iProver_top
    | k2_relat_1(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6363,c_112])).

cnf(c_6781,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | v1_xboole_0(sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_6780])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1496,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6786,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6781,c_1496])).

cnf(c_25,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_357,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_34])).

cnf(c_358,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_357])).

cnf(c_360,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_358,c_33])).

cnf(c_1484,plain,
    ( v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_360])).

cnf(c_1512,plain,
    ( v1_xboole_0(k2_struct_0(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1484,c_371])).

cnf(c_2850,plain,
    ( v1_xboole_0(k2_relat_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2782,c_1512])).

cnf(c_6813,plain,
    ( sK2 = k1_xboole_0
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6786,c_2850])).

cnf(c_6900,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6813,c_112])).

cnf(c_6936,plain,
    ( k2_struct_0(sK1) = k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_6900,c_2782])).

cnf(c_4,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1859,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4,c_2])).

cnf(c_6988,plain,
    ( k2_struct_0(sK1) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6936,c_1859])).

cnf(c_1076,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1958,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_struct_0(sK1))
    | k2_struct_0(sK1) != X0 ),
    inference(instantiation,[status(thm)],[c_1076])).

cnf(c_1960,plain,
    ( v1_xboole_0(k2_struct_0(sK1))
    | ~ v1_xboole_0(k1_xboole_0)
    | k2_struct_0(sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1958])).

cnf(c_1647,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1512])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6988,c_1960,c_1647,c_0])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:31:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.94/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.00  
% 2.94/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.94/1.00  
% 2.94/1.00  ------  iProver source info
% 2.94/1.00  
% 2.94/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.94/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.94/1.00  git: non_committed_changes: false
% 2.94/1.00  git: last_make_outside_of_git: false
% 2.94/1.00  
% 2.94/1.00  ------ 
% 2.94/1.00  
% 2.94/1.00  ------ Input Options
% 2.94/1.00  
% 2.94/1.00  --out_options                           all
% 2.94/1.00  --tptp_safe_out                         true
% 2.94/1.00  --problem_path                          ""
% 2.94/1.00  --include_path                          ""
% 2.94/1.00  --clausifier                            res/vclausify_rel
% 2.94/1.00  --clausifier_options                    --mode clausify
% 2.94/1.00  --stdin                                 false
% 2.94/1.00  --stats_out                             all
% 2.94/1.00  
% 2.94/1.00  ------ General Options
% 2.94/1.00  
% 2.94/1.00  --fof                                   false
% 2.94/1.00  --time_out_real                         305.
% 2.94/1.00  --time_out_virtual                      -1.
% 2.94/1.00  --symbol_type_check                     false
% 2.94/1.00  --clausify_out                          false
% 2.94/1.00  --sig_cnt_out                           false
% 2.94/1.00  --trig_cnt_out                          false
% 2.94/1.00  --trig_cnt_out_tolerance                1.
% 2.94/1.00  --trig_cnt_out_sk_spl                   false
% 2.94/1.00  --abstr_cl_out                          false
% 2.94/1.00  
% 2.94/1.00  ------ Global Options
% 2.94/1.00  
% 2.94/1.00  --schedule                              default
% 2.94/1.00  --add_important_lit                     false
% 2.94/1.00  --prop_solver_per_cl                    1000
% 2.94/1.00  --min_unsat_core                        false
% 2.94/1.00  --soft_assumptions                      false
% 2.94/1.00  --soft_lemma_size                       3
% 2.94/1.00  --prop_impl_unit_size                   0
% 2.94/1.00  --prop_impl_unit                        []
% 2.94/1.00  --share_sel_clauses                     true
% 2.94/1.00  --reset_solvers                         false
% 2.94/1.00  --bc_imp_inh                            [conj_cone]
% 2.94/1.00  --conj_cone_tolerance                   3.
% 2.94/1.00  --extra_neg_conj                        none
% 2.94/1.00  --large_theory_mode                     true
% 2.94/1.00  --prolific_symb_bound                   200
% 2.94/1.00  --lt_threshold                          2000
% 2.94/1.00  --clause_weak_htbl                      true
% 2.94/1.00  --gc_record_bc_elim                     false
% 2.94/1.00  
% 2.94/1.00  ------ Preprocessing Options
% 2.94/1.00  
% 2.94/1.00  --preprocessing_flag                    true
% 2.94/1.00  --time_out_prep_mult                    0.1
% 2.94/1.00  --splitting_mode                        input
% 2.94/1.00  --splitting_grd                         true
% 2.94/1.00  --splitting_cvd                         false
% 2.94/1.00  --splitting_cvd_svl                     false
% 2.94/1.00  --splitting_nvd                         32
% 2.94/1.00  --sub_typing                            true
% 2.94/1.00  --prep_gs_sim                           true
% 2.94/1.00  --prep_unflatten                        true
% 2.94/1.00  --prep_res_sim                          true
% 2.94/1.00  --prep_upred                            true
% 2.94/1.00  --prep_sem_filter                       exhaustive
% 2.94/1.00  --prep_sem_filter_out                   false
% 2.94/1.00  --pred_elim                             true
% 2.94/1.00  --res_sim_input                         true
% 2.94/1.00  --eq_ax_congr_red                       true
% 2.94/1.00  --pure_diseq_elim                       true
% 2.94/1.00  --brand_transform                       false
% 2.94/1.00  --non_eq_to_eq                          false
% 2.94/1.00  --prep_def_merge                        true
% 2.94/1.00  --prep_def_merge_prop_impl              false
% 2.94/1.00  --prep_def_merge_mbd                    true
% 2.94/1.00  --prep_def_merge_tr_red                 false
% 2.94/1.00  --prep_def_merge_tr_cl                  false
% 2.94/1.00  --smt_preprocessing                     true
% 2.94/1.00  --smt_ac_axioms                         fast
% 2.94/1.00  --preprocessed_out                      false
% 2.94/1.00  --preprocessed_stats                    false
% 2.94/1.00  
% 2.94/1.00  ------ Abstraction refinement Options
% 2.94/1.00  
% 2.94/1.00  --abstr_ref                             []
% 2.94/1.00  --abstr_ref_prep                        false
% 2.94/1.00  --abstr_ref_until_sat                   false
% 2.94/1.00  --abstr_ref_sig_restrict                funpre
% 2.94/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.94/1.00  --abstr_ref_under                       []
% 2.94/1.00  
% 2.94/1.00  ------ SAT Options
% 2.94/1.00  
% 2.94/1.00  --sat_mode                              false
% 2.94/1.00  --sat_fm_restart_options                ""
% 2.94/1.00  --sat_gr_def                            false
% 2.94/1.00  --sat_epr_types                         true
% 2.94/1.00  --sat_non_cyclic_types                  false
% 2.94/1.00  --sat_finite_models                     false
% 2.94/1.00  --sat_fm_lemmas                         false
% 2.94/1.00  --sat_fm_prep                           false
% 2.94/1.00  --sat_fm_uc_incr                        true
% 2.94/1.00  --sat_out_model                         small
% 2.94/1.00  --sat_out_clauses                       false
% 2.94/1.00  
% 2.94/1.00  ------ QBF Options
% 2.94/1.00  
% 2.94/1.00  --qbf_mode                              false
% 2.94/1.00  --qbf_elim_univ                         false
% 2.94/1.00  --qbf_dom_inst                          none
% 2.94/1.00  --qbf_dom_pre_inst                      false
% 2.94/1.00  --qbf_sk_in                             false
% 2.94/1.00  --qbf_pred_elim                         true
% 2.94/1.00  --qbf_split                             512
% 2.94/1.00  
% 2.94/1.00  ------ BMC1 Options
% 2.94/1.00  
% 2.94/1.00  --bmc1_incremental                      false
% 2.94/1.00  --bmc1_axioms                           reachable_all
% 2.94/1.00  --bmc1_min_bound                        0
% 2.94/1.00  --bmc1_max_bound                        -1
% 2.94/1.00  --bmc1_max_bound_default                -1
% 2.94/1.00  --bmc1_symbol_reachability              true
% 2.94/1.00  --bmc1_property_lemmas                  false
% 2.94/1.00  --bmc1_k_induction                      false
% 2.94/1.00  --bmc1_non_equiv_states                 false
% 2.94/1.00  --bmc1_deadlock                         false
% 2.94/1.00  --bmc1_ucm                              false
% 2.94/1.00  --bmc1_add_unsat_core                   none
% 2.94/1.00  --bmc1_unsat_core_children              false
% 2.94/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.94/1.00  --bmc1_out_stat                         full
% 2.94/1.00  --bmc1_ground_init                      false
% 2.94/1.00  --bmc1_pre_inst_next_state              false
% 2.94/1.00  --bmc1_pre_inst_state                   false
% 2.94/1.00  --bmc1_pre_inst_reach_state             false
% 2.94/1.00  --bmc1_out_unsat_core                   false
% 2.94/1.00  --bmc1_aig_witness_out                  false
% 2.94/1.00  --bmc1_verbose                          false
% 2.94/1.00  --bmc1_dump_clauses_tptp                false
% 2.94/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.94/1.00  --bmc1_dump_file                        -
% 2.94/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.94/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.94/1.00  --bmc1_ucm_extend_mode                  1
% 2.94/1.00  --bmc1_ucm_init_mode                    2
% 2.94/1.00  --bmc1_ucm_cone_mode                    none
% 2.94/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.94/1.00  --bmc1_ucm_relax_model                  4
% 2.94/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.94/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.94/1.00  --bmc1_ucm_layered_model                none
% 2.94/1.00  --bmc1_ucm_max_lemma_size               10
% 2.94/1.00  
% 2.94/1.00  ------ AIG Options
% 2.94/1.00  
% 2.94/1.00  --aig_mode                              false
% 2.94/1.00  
% 2.94/1.00  ------ Instantiation Options
% 2.94/1.00  
% 2.94/1.00  --instantiation_flag                    true
% 2.94/1.00  --inst_sos_flag                         false
% 2.94/1.00  --inst_sos_phase                        true
% 2.94/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.94/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.94/1.00  --inst_lit_sel_side                     num_symb
% 2.94/1.00  --inst_solver_per_active                1400
% 2.94/1.00  --inst_solver_calls_frac                1.
% 2.94/1.00  --inst_passive_queue_type               priority_queues
% 2.94/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.94/1.00  --inst_passive_queues_freq              [25;2]
% 2.94/1.00  --inst_dismatching                      true
% 2.94/1.00  --inst_eager_unprocessed_to_passive     true
% 2.94/1.00  --inst_prop_sim_given                   true
% 2.94/1.00  --inst_prop_sim_new                     false
% 2.94/1.00  --inst_subs_new                         false
% 2.94/1.00  --inst_eq_res_simp                      false
% 2.94/1.00  --inst_subs_given                       false
% 2.94/1.00  --inst_orphan_elimination               true
% 2.94/1.00  --inst_learning_loop_flag               true
% 2.94/1.00  --inst_learning_start                   3000
% 2.94/1.00  --inst_learning_factor                  2
% 2.94/1.00  --inst_start_prop_sim_after_learn       3
% 2.94/1.00  --inst_sel_renew                        solver
% 2.94/1.00  --inst_lit_activity_flag                true
% 2.94/1.00  --inst_restr_to_given                   false
% 2.94/1.00  --inst_activity_threshold               500
% 2.94/1.00  --inst_out_proof                        true
% 2.94/1.00  
% 2.94/1.00  ------ Resolution Options
% 2.94/1.00  
% 2.94/1.00  --resolution_flag                       true
% 2.94/1.00  --res_lit_sel                           adaptive
% 2.94/1.00  --res_lit_sel_side                      none
% 2.94/1.00  --res_ordering                          kbo
% 2.94/1.00  --res_to_prop_solver                    active
% 2.94/1.00  --res_prop_simpl_new                    false
% 2.94/1.00  --res_prop_simpl_given                  true
% 2.94/1.00  --res_passive_queue_type                priority_queues
% 2.94/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.94/1.00  --res_passive_queues_freq               [15;5]
% 2.94/1.00  --res_forward_subs                      full
% 2.94/1.00  --res_backward_subs                     full
% 2.94/1.00  --res_forward_subs_resolution           true
% 2.94/1.00  --res_backward_subs_resolution          true
% 2.94/1.00  --res_orphan_elimination                true
% 2.94/1.00  --res_time_limit                        2.
% 2.94/1.00  --res_out_proof                         true
% 2.94/1.00  
% 2.94/1.00  ------ Superposition Options
% 2.94/1.00  
% 2.94/1.00  --superposition_flag                    true
% 2.94/1.00  --sup_passive_queue_type                priority_queues
% 2.94/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.94/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.94/1.00  --demod_completeness_check              fast
% 2.94/1.00  --demod_use_ground                      true
% 2.94/1.00  --sup_to_prop_solver                    passive
% 2.94/1.00  --sup_prop_simpl_new                    true
% 2.94/1.00  --sup_prop_simpl_given                  true
% 2.94/1.00  --sup_fun_splitting                     false
% 2.94/1.00  --sup_smt_interval                      50000
% 2.94/1.00  
% 2.94/1.00  ------ Superposition Simplification Setup
% 2.94/1.00  
% 2.94/1.00  --sup_indices_passive                   []
% 2.94/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.94/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/1.00  --sup_full_bw                           [BwDemod]
% 2.94/1.00  --sup_immed_triv                        [TrivRules]
% 2.94/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.94/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/1.00  --sup_immed_bw_main                     []
% 2.94/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.94/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.94/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.94/1.00  
% 2.94/1.00  ------ Combination Options
% 2.94/1.00  
% 2.94/1.00  --comb_res_mult                         3
% 2.94/1.00  --comb_sup_mult                         2
% 2.94/1.00  --comb_inst_mult                        10
% 2.94/1.00  
% 2.94/1.00  ------ Debug Options
% 2.94/1.00  
% 2.94/1.00  --dbg_backtrace                         false
% 2.94/1.00  --dbg_dump_prop_clauses                 false
% 2.94/1.00  --dbg_dump_prop_clauses_file            -
% 2.94/1.00  --dbg_out_stat                          false
% 2.94/1.00  ------ Parsing...
% 2.94/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.94/1.00  
% 2.94/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.94/1.00  
% 2.94/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.94/1.00  
% 2.94/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.94/1.00  ------ Proving...
% 2.94/1.00  ------ Problem Properties 
% 2.94/1.00  
% 2.94/1.00  
% 2.94/1.00  clauses                                 29
% 2.94/1.00  conjectures                             5
% 2.94/1.00  EPR                                     3
% 2.94/1.00  Horn                                    24
% 2.94/1.00  unary                                   11
% 2.94/1.00  binary                                  5
% 2.94/1.00  lits                                    71
% 2.94/1.00  lits eq                                 29
% 2.94/1.00  fd_pure                                 0
% 2.94/1.00  fd_pseudo                               0
% 2.94/1.00  fd_cond                                 4
% 2.94/1.00  fd_pseudo_cond                          1
% 2.94/1.00  AC symbols                              0
% 2.94/1.00  
% 2.94/1.00  ------ Schedule dynamic 5 is on 
% 2.94/1.00  
% 2.94/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.94/1.00  
% 2.94/1.00  
% 2.94/1.00  ------ 
% 2.94/1.00  Current options:
% 2.94/1.00  ------ 
% 2.94/1.00  
% 2.94/1.00  ------ Input Options
% 2.94/1.00  
% 2.94/1.00  --out_options                           all
% 2.94/1.00  --tptp_safe_out                         true
% 2.94/1.00  --problem_path                          ""
% 2.94/1.00  --include_path                          ""
% 2.94/1.00  --clausifier                            res/vclausify_rel
% 2.94/1.00  --clausifier_options                    --mode clausify
% 2.94/1.00  --stdin                                 false
% 2.94/1.00  --stats_out                             all
% 2.94/1.00  
% 2.94/1.00  ------ General Options
% 2.94/1.00  
% 2.94/1.00  --fof                                   false
% 2.94/1.00  --time_out_real                         305.
% 2.94/1.00  --time_out_virtual                      -1.
% 2.94/1.00  --symbol_type_check                     false
% 2.94/1.00  --clausify_out                          false
% 2.94/1.00  --sig_cnt_out                           false
% 2.94/1.00  --trig_cnt_out                          false
% 2.94/1.00  --trig_cnt_out_tolerance                1.
% 2.94/1.00  --trig_cnt_out_sk_spl                   false
% 2.94/1.00  --abstr_cl_out                          false
% 2.94/1.00  
% 2.94/1.00  ------ Global Options
% 2.94/1.00  
% 2.94/1.00  --schedule                              default
% 2.94/1.00  --add_important_lit                     false
% 2.94/1.00  --prop_solver_per_cl                    1000
% 2.94/1.00  --min_unsat_core                        false
% 2.94/1.00  --soft_assumptions                      false
% 2.94/1.00  --soft_lemma_size                       3
% 2.94/1.00  --prop_impl_unit_size                   0
% 2.94/1.00  --prop_impl_unit                        []
% 2.94/1.00  --share_sel_clauses                     true
% 2.94/1.00  --reset_solvers                         false
% 2.94/1.00  --bc_imp_inh                            [conj_cone]
% 2.94/1.00  --conj_cone_tolerance                   3.
% 2.94/1.00  --extra_neg_conj                        none
% 2.94/1.00  --large_theory_mode                     true
% 2.94/1.00  --prolific_symb_bound                   200
% 2.94/1.00  --lt_threshold                          2000
% 2.94/1.00  --clause_weak_htbl                      true
% 2.94/1.00  --gc_record_bc_elim                     false
% 2.94/1.00  
% 2.94/1.00  ------ Preprocessing Options
% 2.94/1.00  
% 2.94/1.00  --preprocessing_flag                    true
% 2.94/1.00  --time_out_prep_mult                    0.1
% 2.94/1.00  --splitting_mode                        input
% 2.94/1.00  --splitting_grd                         true
% 2.94/1.00  --splitting_cvd                         false
% 2.94/1.00  --splitting_cvd_svl                     false
% 2.94/1.00  --splitting_nvd                         32
% 2.94/1.00  --sub_typing                            true
% 2.94/1.00  --prep_gs_sim                           true
% 2.94/1.00  --prep_unflatten                        true
% 2.94/1.00  --prep_res_sim                          true
% 2.94/1.00  --prep_upred                            true
% 2.94/1.00  --prep_sem_filter                       exhaustive
% 2.94/1.00  --prep_sem_filter_out                   false
% 2.94/1.00  --pred_elim                             true
% 2.94/1.00  --res_sim_input                         true
% 2.94/1.00  --eq_ax_congr_red                       true
% 2.94/1.00  --pure_diseq_elim                       true
% 2.94/1.00  --brand_transform                       false
% 2.94/1.00  --non_eq_to_eq                          false
% 2.94/1.00  --prep_def_merge                        true
% 2.94/1.00  --prep_def_merge_prop_impl              false
% 2.94/1.00  --prep_def_merge_mbd                    true
% 2.94/1.00  --prep_def_merge_tr_red                 false
% 2.94/1.00  --prep_def_merge_tr_cl                  false
% 2.94/1.00  --smt_preprocessing                     true
% 2.94/1.00  --smt_ac_axioms                         fast
% 2.94/1.00  --preprocessed_out                      false
% 2.94/1.00  --preprocessed_stats                    false
% 2.94/1.00  
% 2.94/1.00  ------ Abstraction refinement Options
% 2.94/1.00  
% 2.94/1.00  --abstr_ref                             []
% 2.94/1.00  --abstr_ref_prep                        false
% 2.94/1.00  --abstr_ref_until_sat                   false
% 2.94/1.00  --abstr_ref_sig_restrict                funpre
% 2.94/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.94/1.00  --abstr_ref_under                       []
% 2.94/1.00  
% 2.94/1.00  ------ SAT Options
% 2.94/1.00  
% 2.94/1.00  --sat_mode                              false
% 2.94/1.00  --sat_fm_restart_options                ""
% 2.94/1.00  --sat_gr_def                            false
% 2.94/1.00  --sat_epr_types                         true
% 2.94/1.00  --sat_non_cyclic_types                  false
% 2.94/1.00  --sat_finite_models                     false
% 2.94/1.00  --sat_fm_lemmas                         false
% 2.94/1.00  --sat_fm_prep                           false
% 2.94/1.00  --sat_fm_uc_incr                        true
% 2.94/1.00  --sat_out_model                         small
% 2.94/1.00  --sat_out_clauses                       false
% 2.94/1.00  
% 2.94/1.00  ------ QBF Options
% 2.94/1.00  
% 2.94/1.00  --qbf_mode                              false
% 2.94/1.00  --qbf_elim_univ                         false
% 2.94/1.00  --qbf_dom_inst                          none
% 2.94/1.00  --qbf_dom_pre_inst                      false
% 2.94/1.00  --qbf_sk_in                             false
% 2.94/1.00  --qbf_pred_elim                         true
% 2.94/1.00  --qbf_split                             512
% 2.94/1.00  
% 2.94/1.00  ------ BMC1 Options
% 2.94/1.00  
% 2.94/1.00  --bmc1_incremental                      false
% 2.94/1.00  --bmc1_axioms                           reachable_all
% 2.94/1.00  --bmc1_min_bound                        0
% 2.94/1.00  --bmc1_max_bound                        -1
% 2.94/1.00  --bmc1_max_bound_default                -1
% 2.94/1.00  --bmc1_symbol_reachability              true
% 2.94/1.00  --bmc1_property_lemmas                  false
% 2.94/1.00  --bmc1_k_induction                      false
% 2.94/1.00  --bmc1_non_equiv_states                 false
% 2.94/1.00  --bmc1_deadlock                         false
% 2.94/1.00  --bmc1_ucm                              false
% 2.94/1.00  --bmc1_add_unsat_core                   none
% 2.94/1.00  --bmc1_unsat_core_children              false
% 2.94/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.94/1.00  --bmc1_out_stat                         full
% 2.94/1.00  --bmc1_ground_init                      false
% 2.94/1.00  --bmc1_pre_inst_next_state              false
% 2.94/1.00  --bmc1_pre_inst_state                   false
% 2.94/1.00  --bmc1_pre_inst_reach_state             false
% 2.94/1.00  --bmc1_out_unsat_core                   false
% 2.94/1.00  --bmc1_aig_witness_out                  false
% 2.94/1.00  --bmc1_verbose                          false
% 2.94/1.00  --bmc1_dump_clauses_tptp                false
% 2.94/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.94/1.00  --bmc1_dump_file                        -
% 2.94/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.94/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.94/1.00  --bmc1_ucm_extend_mode                  1
% 2.94/1.00  --bmc1_ucm_init_mode                    2
% 2.94/1.00  --bmc1_ucm_cone_mode                    none
% 2.94/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.94/1.00  --bmc1_ucm_relax_model                  4
% 2.94/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.94/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.94/1.00  --bmc1_ucm_layered_model                none
% 2.94/1.00  --bmc1_ucm_max_lemma_size               10
% 2.94/1.00  
% 2.94/1.00  ------ AIG Options
% 2.94/1.00  
% 2.94/1.00  --aig_mode                              false
% 2.94/1.00  
% 2.94/1.00  ------ Instantiation Options
% 2.94/1.00  
% 2.94/1.00  --instantiation_flag                    true
% 2.94/1.00  --inst_sos_flag                         false
% 2.94/1.00  --inst_sos_phase                        true
% 2.94/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.94/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.94/1.00  --inst_lit_sel_side                     none
% 2.94/1.00  --inst_solver_per_active                1400
% 2.94/1.00  --inst_solver_calls_frac                1.
% 2.94/1.00  --inst_passive_queue_type               priority_queues
% 2.94/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.94/1.00  --inst_passive_queues_freq              [25;2]
% 2.94/1.00  --inst_dismatching                      true
% 2.94/1.00  --inst_eager_unprocessed_to_passive     true
% 2.94/1.00  --inst_prop_sim_given                   true
% 2.94/1.00  --inst_prop_sim_new                     false
% 2.94/1.00  --inst_subs_new                         false
% 2.94/1.00  --inst_eq_res_simp                      false
% 2.94/1.00  --inst_subs_given                       false
% 2.94/1.00  --inst_orphan_elimination               true
% 2.94/1.00  --inst_learning_loop_flag               true
% 2.94/1.00  --inst_learning_start                   3000
% 2.94/1.00  --inst_learning_factor                  2
% 2.94/1.00  --inst_start_prop_sim_after_learn       3
% 2.94/1.00  --inst_sel_renew                        solver
% 2.94/1.00  --inst_lit_activity_flag                true
% 2.94/1.00  --inst_restr_to_given                   false
% 2.94/1.00  --inst_activity_threshold               500
% 2.94/1.00  --inst_out_proof                        true
% 2.94/1.00  
% 2.94/1.00  ------ Resolution Options
% 2.94/1.00  
% 2.94/1.00  --resolution_flag                       false
% 2.94/1.00  --res_lit_sel                           adaptive
% 2.94/1.00  --res_lit_sel_side                      none
% 2.94/1.00  --res_ordering                          kbo
% 2.94/1.00  --res_to_prop_solver                    active
% 2.94/1.00  --res_prop_simpl_new                    false
% 2.94/1.00  --res_prop_simpl_given                  true
% 2.94/1.00  --res_passive_queue_type                priority_queues
% 2.94/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.94/1.00  --res_passive_queues_freq               [15;5]
% 2.94/1.00  --res_forward_subs                      full
% 2.94/1.00  --res_backward_subs                     full
% 2.94/1.00  --res_forward_subs_resolution           true
% 2.94/1.00  --res_backward_subs_resolution          true
% 2.94/1.00  --res_orphan_elimination                true
% 2.94/1.00  --res_time_limit                        2.
% 2.94/1.00  --res_out_proof                         true
% 2.94/1.00  
% 2.94/1.00  ------ Superposition Options
% 2.94/1.00  
% 2.94/1.00  --superposition_flag                    true
% 2.94/1.00  --sup_passive_queue_type                priority_queues
% 2.94/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.94/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.94/1.00  --demod_completeness_check              fast
% 2.94/1.00  --demod_use_ground                      true
% 2.94/1.00  --sup_to_prop_solver                    passive
% 2.94/1.00  --sup_prop_simpl_new                    true
% 2.94/1.00  --sup_prop_simpl_given                  true
% 2.94/1.00  --sup_fun_splitting                     false
% 2.94/1.00  --sup_smt_interval                      50000
% 2.94/1.00  
% 2.94/1.00  ------ Superposition Simplification Setup
% 2.94/1.00  
% 2.94/1.00  --sup_indices_passive                   []
% 2.94/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.94/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/1.00  --sup_full_bw                           [BwDemod]
% 2.94/1.00  --sup_immed_triv                        [TrivRules]
% 2.94/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.94/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/1.00  --sup_immed_bw_main                     []
% 2.94/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.94/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.94/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.94/1.00  
% 2.94/1.00  ------ Combination Options
% 2.94/1.00  
% 2.94/1.00  --comb_res_mult                         3
% 2.94/1.00  --comb_sup_mult                         2
% 2.94/1.00  --comb_inst_mult                        10
% 2.94/1.00  
% 2.94/1.00  ------ Debug Options
% 2.94/1.00  
% 2.94/1.00  --dbg_backtrace                         false
% 2.94/1.00  --dbg_dump_prop_clauses                 false
% 2.94/1.00  --dbg_dump_prop_clauses_file            -
% 2.94/1.00  --dbg_out_stat                          false
% 2.94/1.00  
% 2.94/1.00  
% 2.94/1.00  
% 2.94/1.00  
% 2.94/1.00  ------ Proving...
% 2.94/1.00  
% 2.94/1.00  
% 2.94/1.00  % SZS status Theorem for theBenchmark.p
% 2.94/1.00  
% 2.94/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.94/1.00  
% 2.94/1.00  fof(f17,conjecture,(
% 2.94/1.00    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 2.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/1.00  
% 2.94/1.00  fof(f18,negated_conjecture,(
% 2.94/1.00    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 2.94/1.00    inference(negated_conjecture,[],[f17])).
% 2.94/1.00  
% 2.94/1.00  fof(f40,plain,(
% 2.94/1.00    ? [X0] : (? [X1] : (? [X2] : (((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 2.94/1.00    inference(ennf_transformation,[],[f18])).
% 2.94/1.00  
% 2.94/1.00  fof(f41,plain,(
% 2.94/1.00    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 2.94/1.00    inference(flattening,[],[f40])).
% 2.94/1.00  
% 2.94/1.00  fof(f46,plain,(
% 2.94/1.00    ( ! [X0,X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.94/1.00    introduced(choice_axiom,[])).
% 2.94/1.00  
% 2.94/1.00  fof(f45,plain,(
% 2.94/1.00    ( ! [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(sK1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 2.94/1.00    introduced(choice_axiom,[])).
% 2.94/1.00  
% 2.94/1.00  fof(f44,plain,(
% 2.94/1.00    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 2.94/1.00    introduced(choice_axiom,[])).
% 2.94/1.00  
% 2.94/1.00  fof(f47,plain,(
% 2.94/1.00    (((k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.94/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f41,f46,f45,f44])).
% 2.94/1.00  
% 2.94/1.00  fof(f80,plain,(
% 2.94/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.94/1.00    inference(cnf_transformation,[],[f47])).
% 2.94/1.00  
% 2.94/1.00  fof(f14,axiom,(
% 2.94/1.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/1.00  
% 2.94/1.00  fof(f35,plain,(
% 2.94/1.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.94/1.00    inference(ennf_transformation,[],[f14])).
% 2.94/1.00  
% 2.94/1.00  fof(f72,plain,(
% 2.94/1.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.94/1.00    inference(cnf_transformation,[],[f35])).
% 2.94/1.00  
% 2.94/1.00  fof(f77,plain,(
% 2.94/1.00    l1_struct_0(sK1)),
% 2.94/1.00    inference(cnf_transformation,[],[f47])).
% 2.94/1.00  
% 2.94/1.00  fof(f75,plain,(
% 2.94/1.00    l1_struct_0(sK0)),
% 2.94/1.00    inference(cnf_transformation,[],[f47])).
% 2.94/1.00  
% 2.94/1.00  fof(f9,axiom,(
% 2.94/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/1.00  
% 2.94/1.00  fof(f26,plain,(
% 2.94/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.94/1.00    inference(ennf_transformation,[],[f9])).
% 2.94/1.00  
% 2.94/1.00  fof(f58,plain,(
% 2.94/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.94/1.00    inference(cnf_transformation,[],[f26])).
% 2.94/1.00  
% 2.94/1.00  fof(f81,plain,(
% 2.94/1.00    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 2.94/1.00    inference(cnf_transformation,[],[f47])).
% 2.94/1.00  
% 2.94/1.00  fof(f12,axiom,(
% 2.94/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/1.00  
% 2.94/1.00  fof(f31,plain,(
% 2.94/1.00    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.94/1.00    inference(ennf_transformation,[],[f12])).
% 2.94/1.00  
% 2.94/1.00  fof(f32,plain,(
% 2.94/1.00    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.94/1.00    inference(flattening,[],[f31])).
% 2.94/1.00  
% 2.94/1.00  fof(f67,plain,(
% 2.94/1.00    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.94/1.00    inference(cnf_transformation,[],[f32])).
% 2.94/1.00  
% 2.94/1.00  fof(f7,axiom,(
% 2.94/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/1.00  
% 2.94/1.00  fof(f19,plain,(
% 2.94/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.94/1.00    inference(pure_predicate_removal,[],[f7])).
% 2.94/1.00  
% 2.94/1.00  fof(f24,plain,(
% 2.94/1.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.94/1.00    inference(ennf_transformation,[],[f19])).
% 2.94/1.00  
% 2.94/1.00  fof(f56,plain,(
% 2.94/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.94/1.00    inference(cnf_transformation,[],[f24])).
% 2.94/1.00  
% 2.94/1.00  fof(f11,axiom,(
% 2.94/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/1.00  
% 2.94/1.00  fof(f29,plain,(
% 2.94/1.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.94/1.00    inference(ennf_transformation,[],[f11])).
% 2.94/1.00  
% 2.94/1.00  fof(f30,plain,(
% 2.94/1.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.94/1.00    inference(flattening,[],[f29])).
% 2.94/1.00  
% 2.94/1.00  fof(f43,plain,(
% 2.94/1.00    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.94/1.00    inference(nnf_transformation,[],[f30])).
% 2.94/1.00  
% 2.94/1.00  fof(f65,plain,(
% 2.94/1.00    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.94/1.00    inference(cnf_transformation,[],[f43])).
% 2.94/1.00  
% 2.94/1.00  fof(f6,axiom,(
% 2.94/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/1.00  
% 2.94/1.00  fof(f23,plain,(
% 2.94/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.94/1.00    inference(ennf_transformation,[],[f6])).
% 2.94/1.00  
% 2.94/1.00  fof(f55,plain,(
% 2.94/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.94/1.00    inference(cnf_transformation,[],[f23])).
% 2.94/1.00  
% 2.94/1.00  fof(f78,plain,(
% 2.94/1.00    v1_funct_1(sK2)),
% 2.94/1.00    inference(cnf_transformation,[],[f47])).
% 2.94/1.00  
% 2.94/1.00  fof(f79,plain,(
% 2.94/1.00    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.94/1.00    inference(cnf_transformation,[],[f47])).
% 2.94/1.00  
% 2.94/1.00  fof(f13,axiom,(
% 2.94/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/1.00  
% 2.94/1.00  fof(f33,plain,(
% 2.94/1.00    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.94/1.00    inference(ennf_transformation,[],[f13])).
% 2.94/1.00  
% 2.94/1.00  fof(f34,plain,(
% 2.94/1.00    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.94/1.00    inference(flattening,[],[f33])).
% 2.94/1.00  
% 2.94/1.00  fof(f71,plain,(
% 2.94/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.94/1.00    inference(cnf_transformation,[],[f34])).
% 2.94/1.00  
% 2.94/1.00  fof(f82,plain,(
% 2.94/1.00    v2_funct_1(sK2)),
% 2.94/1.00    inference(cnf_transformation,[],[f47])).
% 2.94/1.00  
% 2.94/1.00  fof(f10,axiom,(
% 2.94/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/1.00  
% 2.94/1.00  fof(f27,plain,(
% 2.94/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.94/1.00    inference(ennf_transformation,[],[f10])).
% 2.94/1.00  
% 2.94/1.00  fof(f28,plain,(
% 2.94/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.94/1.00    inference(flattening,[],[f27])).
% 2.94/1.00  
% 2.94/1.00  fof(f42,plain,(
% 2.94/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.94/1.00    inference(nnf_transformation,[],[f28])).
% 2.94/1.00  
% 2.94/1.00  fof(f59,plain,(
% 2.94/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.94/1.00    inference(cnf_transformation,[],[f42])).
% 2.94/1.00  
% 2.94/1.00  fof(f70,plain,(
% 2.94/1.00    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.94/1.00    inference(cnf_transformation,[],[f34])).
% 2.94/1.00  
% 2.94/1.00  fof(f5,axiom,(
% 2.94/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 2.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/1.00  
% 2.94/1.00  fof(f21,plain,(
% 2.94/1.00    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.94/1.00    inference(ennf_transformation,[],[f5])).
% 2.94/1.00  
% 2.94/1.00  fof(f22,plain,(
% 2.94/1.00    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.94/1.00    inference(flattening,[],[f21])).
% 2.94/1.00  
% 2.94/1.00  fof(f54,plain,(
% 2.94/1.00    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.94/1.00    inference(cnf_transformation,[],[f22])).
% 2.94/1.00  
% 2.94/1.00  fof(f16,axiom,(
% 2.94/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/1.00  
% 2.94/1.00  fof(f38,plain,(
% 2.94/1.00    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.94/1.00    inference(ennf_transformation,[],[f16])).
% 2.94/1.00  
% 2.94/1.00  fof(f39,plain,(
% 2.94/1.00    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.94/1.00    inference(flattening,[],[f38])).
% 2.94/1.00  
% 2.94/1.00  fof(f74,plain,(
% 2.94/1.00    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.94/1.00    inference(cnf_transformation,[],[f39])).
% 2.94/1.00  
% 2.94/1.00  fof(f83,plain,(
% 2.94/1.00    k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)),
% 2.94/1.00    inference(cnf_transformation,[],[f47])).
% 2.94/1.00  
% 2.94/1.00  fof(f8,axiom,(
% 2.94/1.00    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 2.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/1.00  
% 2.94/1.00  fof(f25,plain,(
% 2.94/1.00    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 2.94/1.00    inference(ennf_transformation,[],[f8])).
% 2.94/1.00  
% 2.94/1.00  fof(f57,plain,(
% 2.94/1.00    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 2.94/1.00    inference(cnf_transformation,[],[f25])).
% 2.94/1.00  
% 2.94/1.00  fof(f1,axiom,(
% 2.94/1.00    v1_xboole_0(k1_xboole_0)),
% 2.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/1.00  
% 2.94/1.00  fof(f48,plain,(
% 2.94/1.00    v1_xboole_0(k1_xboole_0)),
% 2.94/1.00    inference(cnf_transformation,[],[f1])).
% 2.94/1.00  
% 2.94/1.00  fof(f2,axiom,(
% 2.94/1.00    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/1.00  
% 2.94/1.00  fof(f20,plain,(
% 2.94/1.00    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.94/1.00    inference(ennf_transformation,[],[f2])).
% 2.94/1.00  
% 2.94/1.00  fof(f49,plain,(
% 2.94/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.94/1.00    inference(cnf_transformation,[],[f20])).
% 2.94/1.00  
% 2.94/1.00  fof(f15,axiom,(
% 2.94/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/1.00  
% 2.94/1.00  fof(f36,plain,(
% 2.94/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.94/1.00    inference(ennf_transformation,[],[f15])).
% 2.94/1.00  
% 2.94/1.00  fof(f37,plain,(
% 2.94/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.94/1.00    inference(flattening,[],[f36])).
% 2.94/1.00  
% 2.94/1.00  fof(f73,plain,(
% 2.94/1.00    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.94/1.00    inference(cnf_transformation,[],[f37])).
% 2.94/1.00  
% 2.94/1.00  fof(f76,plain,(
% 2.94/1.00    ~v2_struct_0(sK1)),
% 2.94/1.00    inference(cnf_transformation,[],[f47])).
% 2.94/1.00  
% 2.94/1.00  fof(f4,axiom,(
% 2.94/1.00    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 2.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/1.00  
% 2.94/1.00  fof(f52,plain,(
% 2.94/1.00    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 2.94/1.00    inference(cnf_transformation,[],[f4])).
% 2.94/1.00  
% 2.94/1.00  fof(f3,axiom,(
% 2.94/1.00    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/1.00  
% 2.94/1.00  fof(f51,plain,(
% 2.94/1.00    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.94/1.00    inference(cnf_transformation,[],[f3])).
% 2.94/1.00  
% 2.94/1.00  cnf(c_30,negated_conjecture,
% 2.94/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.94/1.00      inference(cnf_transformation,[],[f80]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_1487,plain,
% 2.94/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.94/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_24,plain,
% 2.94/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.94/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_33,negated_conjecture,
% 2.94/1.00      ( l1_struct_0(sK1) ),
% 2.94/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_370,plain,
% 2.94/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.94/1.00      inference(resolution_lifted,[status(thm)],[c_24,c_33]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_371,plain,
% 2.94/1.00      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.94/1.00      inference(unflattening,[status(thm)],[c_370]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_35,negated_conjecture,
% 2.94/1.00      ( l1_struct_0(sK0) ),
% 2.94/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_375,plain,
% 2.94/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.94/1.00      inference(resolution_lifted,[status(thm)],[c_24,c_35]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_376,plain,
% 2.94/1.00      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.94/1.00      inference(unflattening,[status(thm)],[c_375]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_1525,plain,
% 2.94/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.94/1.00      inference(light_normalisation,[status(thm)],[c_1487,c_371,c_376]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_10,plain,
% 2.94/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.94/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_1494,plain,
% 2.94/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.94/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.94/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_2681,plain,
% 2.94/1.00      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 2.94/1.00      inference(superposition,[status(thm)],[c_1525,c_1494]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_29,negated_conjecture,
% 2.94/1.00      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.94/1.00      inference(cnf_transformation,[],[f81]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_1518,plain,
% 2.94/1.00      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.94/1.00      inference(light_normalisation,[status(thm)],[c_29,c_371,c_376]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_2782,plain,
% 2.94/1.00      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 2.94/1.00      inference(demodulation,[status(thm)],[c_2681,c_1518]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_2848,plain,
% 2.94/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 2.94/1.00      inference(demodulation,[status(thm)],[c_2782,c_1525]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_20,plain,
% 2.94/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.94/1.00      | v1_partfun1(X0,X1)
% 2.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/1.00      | ~ v1_funct_1(X0)
% 2.94/1.00      | k1_xboole_0 = X2 ),
% 2.94/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_8,plain,
% 2.94/1.00      ( v4_relat_1(X0,X1)
% 2.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.94/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_18,plain,
% 2.94/1.00      ( ~ v1_partfun1(X0,X1)
% 2.94/1.00      | ~ v4_relat_1(X0,X1)
% 2.94/1.00      | ~ v1_relat_1(X0)
% 2.94/1.00      | k1_relat_1(X0) = X1 ),
% 2.94/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_382,plain,
% 2.94/1.00      ( ~ v1_partfun1(X0,X1)
% 2.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/1.00      | ~ v1_relat_1(X0)
% 2.94/1.00      | k1_relat_1(X0) = X1 ),
% 2.94/1.00      inference(resolution,[status(thm)],[c_8,c_18]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_7,plain,
% 2.94/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/1.00      | v1_relat_1(X0) ),
% 2.94/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_386,plain,
% 2.94/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/1.00      | ~ v1_partfun1(X0,X1)
% 2.94/1.00      | k1_relat_1(X0) = X1 ),
% 2.94/1.00      inference(global_propositional_subsumption,
% 2.94/1.00                [status(thm)],
% 2.94/1.00                [c_382,c_18,c_8,c_7]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_387,plain,
% 2.94/1.00      ( ~ v1_partfun1(X0,X1)
% 2.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/1.00      | k1_relat_1(X0) = X1 ),
% 2.94/1.00      inference(renaming,[status(thm)],[c_386]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_468,plain,
% 2.94/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.94/1.00      | ~ v1_funct_1(X0)
% 2.94/1.00      | k1_relat_1(X0) = X1
% 2.94/1.00      | k1_xboole_0 = X2 ),
% 2.94/1.00      inference(resolution,[status(thm)],[c_20,c_387]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_472,plain,
% 2.94/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/1.00      | ~ v1_funct_2(X0,X1,X2)
% 2.94/1.00      | ~ v1_funct_1(X0)
% 2.94/1.00      | k1_relat_1(X0) = X1
% 2.94/1.00      | k1_xboole_0 = X2 ),
% 2.94/1.00      inference(global_propositional_subsumption,
% 2.94/1.00                [status(thm)],
% 2.94/1.00                [c_468,c_20,c_7,c_382]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_473,plain,
% 2.94/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/1.00      | ~ v1_funct_1(X0)
% 2.94/1.00      | k1_relat_1(X0) = X1
% 2.94/1.00      | k1_xboole_0 = X2 ),
% 2.94/1.00      inference(renaming,[status(thm)],[c_472]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_1483,plain,
% 2.94/1.00      ( k1_relat_1(X0) = X1
% 2.94/1.00      | k1_xboole_0 = X2
% 2.94/1.00      | v1_funct_2(X0,X1,X2) != iProver_top
% 2.94/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.94/1.00      | v1_funct_1(X0) != iProver_top ),
% 2.94/1.00      inference(predicate_to_equality,[status(thm)],[c_473]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_4212,plain,
% 2.94/1.00      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.94/1.00      | k2_relat_1(sK2) = k1_xboole_0
% 2.94/1.00      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.94/1.00      | v1_funct_1(sK2) != iProver_top ),
% 2.94/1.00      inference(superposition,[status(thm)],[c_2848,c_1483]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_32,negated_conjecture,
% 2.94/1.00      ( v1_funct_1(sK2) ),
% 2.94/1.00      inference(cnf_transformation,[],[f78]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_31,negated_conjecture,
% 2.94/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.94/1.00      inference(cnf_transformation,[],[f79]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_1486,plain,
% 2.94/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.94/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_1515,plain,
% 2.94/1.00      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.94/1.00      inference(light_normalisation,[status(thm)],[c_1486,c_371,c_376]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_2849,plain,
% 2.94/1.00      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
% 2.94/1.00      inference(demodulation,[status(thm)],[c_2782,c_1515]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_2875,plain,
% 2.94/1.00      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
% 2.94/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2849]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_4221,plain,
% 2.94/1.00      ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
% 2.94/1.00      | ~ v1_funct_1(sK2)
% 2.94/1.00      | k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.94/1.00      | k2_relat_1(sK2) = k1_xboole_0 ),
% 2.94/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_4212]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_4381,plain,
% 2.94/1.00      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.94/1.00      | k2_relat_1(sK2) = k1_xboole_0 ),
% 2.94/1.00      inference(global_propositional_subsumption,
% 2.94/1.00                [status(thm)],
% 2.94/1.00                [c_4212,c_32,c_2875,c_4221]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_21,plain,
% 2.94/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/1.00      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.94/1.00      | ~ v1_funct_1(X0)
% 2.94/1.00      | ~ v2_funct_1(X0)
% 2.94/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.94/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_28,negated_conjecture,
% 2.94/1.00      ( v2_funct_1(sK2) ),
% 2.94/1.00      inference(cnf_transformation,[],[f82]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_599,plain,
% 2.94/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/1.00      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.94/1.00      | ~ v1_funct_1(X0)
% 2.94/1.00      | k2_relset_1(X1,X2,X0) != X2
% 2.94/1.00      | sK2 != X0 ),
% 2.94/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_28]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_600,plain,
% 2.94/1.00      ( ~ v1_funct_2(sK2,X0,X1)
% 2.94/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.94/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.94/1.00      | ~ v1_funct_1(sK2)
% 2.94/1.00      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.94/1.00      inference(unflattening,[status(thm)],[c_599]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_604,plain,
% 2.94/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.94/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.94/1.00      | ~ v1_funct_2(sK2,X0,X1)
% 2.94/1.00      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.94/1.00      inference(global_propositional_subsumption,
% 2.94/1.00                [status(thm)],
% 2.94/1.00                [c_600,c_32]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_605,plain,
% 2.94/1.00      ( ~ v1_funct_2(sK2,X0,X1)
% 2.94/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.94/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.94/1.00      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.94/1.00      inference(renaming,[status(thm)],[c_604]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_1478,plain,
% 2.94/1.00      ( k2_relset_1(X0,X1,sK2) != X1
% 2.94/1.00      | v1_funct_2(sK2,X0,X1) != iProver_top
% 2.94/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
% 2.94/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.94/1.00      inference(predicate_to_equality,[status(thm)],[c_605]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_2426,plain,
% 2.94/1.00      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.94/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
% 2.94/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 2.94/1.00      inference(superposition,[status(thm)],[c_1518,c_1478]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_2774,plain,
% 2.94/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top ),
% 2.94/1.00      inference(global_propositional_subsumption,
% 2.94/1.00                [status(thm)],
% 2.94/1.00                [c_2426,c_1515,c_1525]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_2844,plain,
% 2.94/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
% 2.94/1.00      inference(demodulation,[status(thm)],[c_2782,c_2774]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_16,plain,
% 2.94/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.94/1.00      | k1_xboole_0 = X2 ),
% 2.94/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_1488,plain,
% 2.94/1.00      ( k1_relset_1(X0,X1,X2) = X0
% 2.94/1.00      | k1_xboole_0 = X1
% 2.94/1.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 2.94/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.94/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_4353,plain,
% 2.94/1.00      ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(sK2)
% 2.94/1.00      | k2_struct_0(sK0) = k1_xboole_0
% 2.94/1.00      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top ),
% 2.94/1.00      inference(superposition,[status(thm)],[c_2844,c_1488]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_22,plain,
% 2.94/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.94/1.00      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 2.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/1.00      | ~ v1_funct_1(X0)
% 2.94/1.00      | ~ v2_funct_1(X0)
% 2.94/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.94/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_575,plain,
% 2.94/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.94/1.00      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 2.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/1.00      | ~ v1_funct_1(X0)
% 2.94/1.00      | k2_relset_1(X1,X2,X0) != X2
% 2.94/1.00      | sK2 != X0 ),
% 2.94/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_28]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_576,plain,
% 2.94/1.00      ( v1_funct_2(k2_funct_1(sK2),X0,X1)
% 2.94/1.00      | ~ v1_funct_2(sK2,X1,X0)
% 2.94/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.94/1.00      | ~ v1_funct_1(sK2)
% 2.94/1.00      | k2_relset_1(X1,X0,sK2) != X0 ),
% 2.94/1.00      inference(unflattening,[status(thm)],[c_575]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_580,plain,
% 2.94/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.94/1.00      | ~ v1_funct_2(sK2,X1,X0)
% 2.94/1.00      | v1_funct_2(k2_funct_1(sK2),X0,X1)
% 2.94/1.00      | k2_relset_1(X1,X0,sK2) != X0 ),
% 2.94/1.00      inference(global_propositional_subsumption,
% 2.94/1.00                [status(thm)],
% 2.94/1.00                [c_576,c_32]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_581,plain,
% 2.94/1.00      ( v1_funct_2(k2_funct_1(sK2),X0,X1)
% 2.94/1.00      | ~ v1_funct_2(sK2,X1,X0)
% 2.94/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.94/1.00      | k2_relset_1(X1,X0,sK2) != X0 ),
% 2.94/1.00      inference(renaming,[status(thm)],[c_580]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_1479,plain,
% 2.94/1.00      ( k2_relset_1(X0,X1,sK2) != X1
% 2.94/1.00      | v1_funct_2(k2_funct_1(sK2),X1,X0) = iProver_top
% 2.94/1.00      | v1_funct_2(sK2,X0,X1) != iProver_top
% 2.94/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.94/1.00      inference(predicate_to_equality,[status(thm)],[c_581]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_2086,plain,
% 2.94/1.00      ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top
% 2.94/1.00      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.94/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 2.94/1.00      inference(superposition,[status(thm)],[c_1518,c_1479]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_2235,plain,
% 2.94/1.00      ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top ),
% 2.94/1.00      inference(global_propositional_subsumption,
% 2.94/1.00                [status(thm)],
% 2.94/1.00                [c_2086,c_1515,c_1525]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_2847,plain,
% 2.94/1.00      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top ),
% 2.94/1.00      inference(demodulation,[status(thm)],[c_2782,c_2235]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_5047,plain,
% 2.94/1.00      ( k2_struct_0(sK0) = k1_xboole_0
% 2.94/1.00      | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.94/1.00      inference(global_propositional_subsumption,
% 2.94/1.00                [status(thm)],
% 2.94/1.00                [c_4353,c_2847]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_5048,plain,
% 2.94/1.00      ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(sK2)
% 2.94/1.00      | k2_struct_0(sK0) = k1_xboole_0 ),
% 2.94/1.00      inference(renaming,[status(thm)],[c_5047]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_3879,plain,
% 2.94/1.00      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 2.94/1.00      inference(superposition,[status(thm)],[c_2844,c_1494]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_5,plain,
% 2.94/1.00      ( ~ v1_relat_1(X0)
% 2.94/1.00      | ~ v1_funct_1(X0)
% 2.94/1.00      | ~ v2_funct_1(X0)
% 2.94/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.94/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_637,plain,
% 2.94/1.00      ( ~ v1_relat_1(X0)
% 2.94/1.00      | ~ v1_funct_1(X0)
% 2.94/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 2.94/1.00      | sK2 != X0 ),
% 2.94/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_28]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_638,plain,
% 2.94/1.00      ( ~ v1_relat_1(sK2)
% 2.94/1.00      | ~ v1_funct_1(sK2)
% 2.94/1.00      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.94/1.00      inference(unflattening,[status(thm)],[c_637]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_640,plain,
% 2.94/1.00      ( ~ v1_relat_1(sK2)
% 2.94/1.00      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.94/1.00      inference(global_propositional_subsumption,
% 2.94/1.00                [status(thm)],
% 2.94/1.00                [c_638,c_32]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_677,plain,
% 2.94/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/1.00      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.94/1.00      | sK2 != X0 ),
% 2.94/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_640]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_678,plain,
% 2.94/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.94/1.00      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.94/1.00      inference(unflattening,[status(thm)],[c_677]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_1477,plain,
% 2.94/1.00      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.94/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.94/1.00      inference(predicate_to_equality,[status(thm)],[c_678]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_1708,plain,
% 2.94/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.94/1.00      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.94/1.00      inference(instantiation,[status(thm)],[c_678]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_2429,plain,
% 2.94/1.00      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.94/1.00      inference(global_propositional_subsumption,
% 2.94/1.00                [status(thm)],
% 2.94/1.00                [c_1477,c_30,c_1708]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_3881,plain,
% 2.94/1.00      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.94/1.00      inference(light_normalisation,[status(thm)],[c_3879,c_2429]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_26,plain,
% 2.94/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/1.00      | ~ v1_funct_1(X0)
% 2.94/1.00      | ~ v2_funct_1(X0)
% 2.94/1.00      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.94/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.94/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_527,plain,
% 2.94/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/1.00      | ~ v1_funct_1(X0)
% 2.94/1.00      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.94/1.00      | k2_relset_1(X1,X2,X0) != X2
% 2.94/1.00      | sK2 != X0 ),
% 2.94/1.00      inference(resolution_lifted,[status(thm)],[c_26,c_28]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_528,plain,
% 2.94/1.00      ( ~ v1_funct_2(sK2,X0,X1)
% 2.94/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.94/1.00      | ~ v1_funct_1(sK2)
% 2.94/1.00      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.94/1.00      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.94/1.00      inference(unflattening,[status(thm)],[c_527]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_532,plain,
% 2.94/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.94/1.00      | ~ v1_funct_2(sK2,X0,X1)
% 2.94/1.00      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.94/1.00      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.94/1.00      inference(global_propositional_subsumption,
% 2.94/1.00                [status(thm)],
% 2.94/1.00                [c_528,c_32]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_533,plain,
% 2.94/1.00      ( ~ v1_funct_2(sK2,X0,X1)
% 2.94/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.94/1.00      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.94/1.00      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.94/1.00      inference(renaming,[status(thm)],[c_532]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_1481,plain,
% 2.94/1.00      ( k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.94/1.00      | k2_relset_1(X0,X1,sK2) != X1
% 2.94/1.00      | v1_funct_2(sK2,X0,X1) != iProver_top
% 2.94/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.94/1.00      inference(predicate_to_equality,[status(thm)],[c_533]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_2245,plain,
% 2.94/1.00      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 2.94/1.00      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.94/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 2.94/1.00      inference(superposition,[status(thm)],[c_1518,c_1481]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_2339,plain,
% 2.94/1.00      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 2.94/1.00      inference(global_propositional_subsumption,
% 2.94/1.00                [status(thm)],
% 2.94/1.00                [c_2245,c_1515,c_1525]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_27,negated_conjecture,
% 2.94/1.00      ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 2.94/1.00      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
% 2.94/1.00      inference(cnf_transformation,[],[f83]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_1596,plain,
% 2.94/1.00      ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 2.94/1.00      | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
% 2.94/1.00      inference(light_normalisation,[status(thm)],[c_27,c_371,c_376]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_2342,plain,
% 2.94/1.00      ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK1)
% 2.94/1.00      | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
% 2.94/1.00      inference(demodulation,[status(thm)],[c_2339,c_1596]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_2845,plain,
% 2.94/1.00      ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2)
% 2.94/1.00      | k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
% 2.94/1.00      inference(demodulation,[status(thm)],[c_2782,c_2342]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_4066,plain,
% 2.94/1.00      ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2)
% 2.94/1.00      | k2_struct_0(sK0) != k1_relat_1(sK2) ),
% 2.94/1.00      inference(demodulation,[status(thm)],[c_3881,c_2845]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_5053,plain,
% 2.94/1.00      ( k2_struct_0(sK0) != k1_relat_1(sK2)
% 2.94/1.00      | k2_struct_0(sK0) = k1_xboole_0 ),
% 2.94/1.00      inference(superposition,[status(thm)],[c_5048,c_4066]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_5830,plain,
% 2.94/1.00      ( k2_struct_0(sK0) = k1_xboole_0 | k2_relat_1(sK2) = k1_xboole_0 ),
% 2.94/1.00      inference(superposition,[status(thm)],[c_4381,c_5053]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_9,plain,
% 2.94/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/1.00      | ~ v1_xboole_0(X1)
% 2.94/1.00      | v1_xboole_0(X0) ),
% 2.94/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_1495,plain,
% 2.94/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.94/1.00      | v1_xboole_0(X1) != iProver_top
% 2.94/1.00      | v1_xboole_0(X0) = iProver_top ),
% 2.94/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_3869,plain,
% 2.94/1.00      ( v1_xboole_0(k2_struct_0(sK0)) != iProver_top
% 2.94/1.00      | v1_xboole_0(sK2) = iProver_top ),
% 2.94/1.00      inference(superposition,[status(thm)],[c_2848,c_1495]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_6363,plain,
% 2.94/1.00      ( k2_relat_1(sK2) = k1_xboole_0
% 2.94/1.00      | v1_xboole_0(sK2) = iProver_top
% 2.94/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.94/1.00      inference(superposition,[status(thm)],[c_5830,c_3869]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_0,plain,
% 2.94/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 2.94/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_112,plain,
% 2.94/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.94/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_6780,plain,
% 2.94/1.00      ( v1_xboole_0(sK2) = iProver_top | k2_relat_1(sK2) = k1_xboole_0 ),
% 2.94/1.00      inference(global_propositional_subsumption,
% 2.94/1.00                [status(thm)],
% 2.94/1.00                [c_6363,c_112]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_6781,plain,
% 2.94/1.00      ( k2_relat_1(sK2) = k1_xboole_0 | v1_xboole_0(sK2) = iProver_top ),
% 2.94/1.00      inference(renaming,[status(thm)],[c_6780]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_1,plain,
% 2.94/1.00      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.94/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_1496,plain,
% 2.94/1.00      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.94/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_6786,plain,
% 2.94/1.00      ( k2_relat_1(sK2) = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 2.94/1.00      inference(superposition,[status(thm)],[c_6781,c_1496]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_25,plain,
% 2.94/1.00      ( v2_struct_0(X0)
% 2.94/1.00      | ~ l1_struct_0(X0)
% 2.94/1.00      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.94/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_34,negated_conjecture,
% 2.94/1.00      ( ~ v2_struct_0(sK1) ),
% 2.94/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_357,plain,
% 2.94/1.00      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK1 != X0 ),
% 2.94/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_34]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_358,plain,
% 2.94/1.00      ( ~ l1_struct_0(sK1) | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.94/1.00      inference(unflattening,[status(thm)],[c_357]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_360,plain,
% 2.94/1.00      ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.94/1.00      inference(global_propositional_subsumption,
% 2.94/1.00                [status(thm)],
% 2.94/1.00                [c_358,c_33]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_1484,plain,
% 2.94/1.00      ( v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
% 2.94/1.00      inference(predicate_to_equality,[status(thm)],[c_360]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_1512,plain,
% 2.94/1.00      ( v1_xboole_0(k2_struct_0(sK1)) != iProver_top ),
% 2.94/1.00      inference(light_normalisation,[status(thm)],[c_1484,c_371]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_2850,plain,
% 2.94/1.00      ( v1_xboole_0(k2_relat_1(sK2)) != iProver_top ),
% 2.94/1.00      inference(demodulation,[status(thm)],[c_2782,c_1512]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_6813,plain,
% 2.94/1.00      ( sK2 = k1_xboole_0 | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.94/1.00      inference(superposition,[status(thm)],[c_6786,c_2850]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_6900,plain,
% 2.94/1.00      ( sK2 = k1_xboole_0 ),
% 2.94/1.00      inference(global_propositional_subsumption,
% 2.94/1.00                [status(thm)],
% 2.94/1.00                [c_6813,c_112]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_6936,plain,
% 2.94/1.00      ( k2_struct_0(sK1) = k2_relat_1(k1_xboole_0) ),
% 2.94/1.00      inference(demodulation,[status(thm)],[c_6900,c_2782]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_4,plain,
% 2.94/1.01      ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.94/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_2,plain,
% 2.94/1.01      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 2.94/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_1859,plain,
% 2.94/1.01      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.94/1.01      inference(superposition,[status(thm)],[c_4,c_2]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_6988,plain,
% 2.94/1.01      ( k2_struct_0(sK1) = k1_xboole_0 ),
% 2.94/1.01      inference(light_normalisation,[status(thm)],[c_6936,c_1859]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_1076,plain,
% 2.94/1.01      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.94/1.01      theory(equality) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_1958,plain,
% 2.94/1.01      ( ~ v1_xboole_0(X0)
% 2.94/1.01      | v1_xboole_0(k2_struct_0(sK1))
% 2.94/1.01      | k2_struct_0(sK1) != X0 ),
% 2.94/1.01      inference(instantiation,[status(thm)],[c_1076]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_1960,plain,
% 2.94/1.01      ( v1_xboole_0(k2_struct_0(sK1))
% 2.94/1.01      | ~ v1_xboole_0(k1_xboole_0)
% 2.94/1.01      | k2_struct_0(sK1) != k1_xboole_0 ),
% 2.94/1.01      inference(instantiation,[status(thm)],[c_1958]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_1647,plain,
% 2.94/1.01      ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 2.94/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_1512]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(contradiction,plain,
% 2.94/1.01      ( $false ),
% 2.94/1.01      inference(minisat,[status(thm)],[c_6988,c_1960,c_1647,c_0]) ).
% 2.94/1.01  
% 2.94/1.01  
% 2.94/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.94/1.01  
% 2.94/1.01  ------                               Statistics
% 2.94/1.01  
% 2.94/1.01  ------ General
% 2.94/1.01  
% 2.94/1.01  abstr_ref_over_cycles:                  0
% 2.94/1.01  abstr_ref_under_cycles:                 0
% 2.94/1.01  gc_basic_clause_elim:                   0
% 2.94/1.01  forced_gc_time:                         0
% 2.94/1.01  parsing_time:                           0.011
% 2.94/1.01  unif_index_cands_time:                  0.
% 2.94/1.01  unif_index_add_time:                    0.
% 2.94/1.01  orderings_time:                         0.
% 2.94/1.01  out_proof_time:                         0.014
% 2.94/1.01  total_time:                             0.237
% 2.94/1.01  num_of_symbols:                         56
% 2.94/1.01  num_of_terms:                           7235
% 2.94/1.01  
% 2.94/1.01  ------ Preprocessing
% 2.94/1.01  
% 2.94/1.01  num_of_splits:                          0
% 2.94/1.01  num_of_split_atoms:                     0
% 2.94/1.01  num_of_reused_defs:                     0
% 2.94/1.01  num_eq_ax_congr_red:                    4
% 2.94/1.01  num_of_sem_filtered_clauses:            1
% 2.94/1.01  num_of_subtypes:                        0
% 2.94/1.01  monotx_restored_types:                  0
% 2.94/1.01  sat_num_of_epr_types:                   0
% 2.94/1.01  sat_num_of_non_cyclic_types:            0
% 2.94/1.01  sat_guarded_non_collapsed_types:        0
% 2.94/1.01  num_pure_diseq_elim:                    0
% 2.94/1.01  simp_replaced_by:                       0
% 2.94/1.01  res_preprocessed:                       158
% 2.94/1.01  prep_upred:                             0
% 2.94/1.01  prep_unflattend:                        25
% 2.94/1.01  smt_new_axioms:                         0
% 2.94/1.01  pred_elim_cands:                        4
% 2.94/1.01  pred_elim:                              6
% 2.94/1.01  pred_elim_cl:                           7
% 2.94/1.01  pred_elim_cycles:                       9
% 2.94/1.01  merged_defs:                            0
% 2.94/1.01  merged_defs_ncl:                        0
% 2.94/1.01  bin_hyper_res:                          0
% 2.94/1.01  prep_cycles:                            4
% 2.94/1.01  pred_elim_time:                         0.013
% 2.94/1.01  splitting_time:                         0.
% 2.94/1.01  sem_filter_time:                        0.
% 2.94/1.01  monotx_time:                            0.001
% 2.94/1.01  subtype_inf_time:                       0.
% 2.94/1.01  
% 2.94/1.01  ------ Problem properties
% 2.94/1.01  
% 2.94/1.01  clauses:                                29
% 2.94/1.01  conjectures:                            5
% 2.94/1.01  epr:                                    3
% 2.94/1.01  horn:                                   24
% 2.94/1.01  ground:                                 10
% 2.94/1.01  unary:                                  11
% 2.94/1.01  binary:                                 5
% 2.94/1.01  lits:                                   71
% 2.94/1.01  lits_eq:                                29
% 2.94/1.01  fd_pure:                                0
% 2.94/1.01  fd_pseudo:                              0
% 2.94/1.01  fd_cond:                                4
% 2.94/1.01  fd_pseudo_cond:                         1
% 2.94/1.01  ac_symbols:                             0
% 2.94/1.01  
% 2.94/1.01  ------ Propositional Solver
% 2.94/1.01  
% 2.94/1.01  prop_solver_calls:                      29
% 2.94/1.01  prop_fast_solver_calls:                 1144
% 2.94/1.01  smt_solver_calls:                       0
% 2.94/1.01  smt_fast_solver_calls:                  0
% 2.94/1.01  prop_num_of_clauses:                    2394
% 2.94/1.01  prop_preprocess_simplified:             7693
% 2.94/1.01  prop_fo_subsumed:                       32
% 2.94/1.01  prop_solver_time:                       0.
% 2.94/1.01  smt_solver_time:                        0.
% 2.94/1.01  smt_fast_solver_time:                   0.
% 2.94/1.01  prop_fast_solver_time:                  0.
% 2.94/1.01  prop_unsat_core_time:                   0.
% 2.94/1.01  
% 2.94/1.01  ------ QBF
% 2.94/1.01  
% 2.94/1.01  qbf_q_res:                              0
% 2.94/1.01  qbf_num_tautologies:                    0
% 2.94/1.01  qbf_prep_cycles:                        0
% 2.94/1.01  
% 2.94/1.01  ------ BMC1
% 2.94/1.01  
% 2.94/1.01  bmc1_current_bound:                     -1
% 2.94/1.01  bmc1_last_solved_bound:                 -1
% 2.94/1.01  bmc1_unsat_core_size:                   -1
% 2.94/1.01  bmc1_unsat_core_parents_size:           -1
% 2.94/1.01  bmc1_merge_next_fun:                    0
% 2.94/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.94/1.01  
% 2.94/1.01  ------ Instantiation
% 2.94/1.01  
% 2.94/1.01  inst_num_of_clauses:                    863
% 2.94/1.01  inst_num_in_passive:                    459
% 2.94/1.01  inst_num_in_active:                     353
% 2.94/1.01  inst_num_in_unprocessed:                51
% 2.94/1.01  inst_num_of_loops:                      370
% 2.94/1.01  inst_num_of_learning_restarts:          0
% 2.94/1.01  inst_num_moves_active_passive:          14
% 2.94/1.01  inst_lit_activity:                      0
% 2.94/1.01  inst_lit_activity_moves:                0
% 2.94/1.01  inst_num_tautologies:                   0
% 2.94/1.01  inst_num_prop_implied:                  0
% 2.94/1.01  inst_num_existing_simplified:           0
% 2.94/1.01  inst_num_eq_res_simplified:             0
% 2.94/1.01  inst_num_child_elim:                    0
% 2.94/1.01  inst_num_of_dismatching_blockings:      60
% 2.94/1.01  inst_num_of_non_proper_insts:           563
% 2.94/1.01  inst_num_of_duplicates:                 0
% 2.94/1.01  inst_inst_num_from_inst_to_res:         0
% 2.94/1.01  inst_dismatching_checking_time:         0.
% 2.94/1.01  
% 2.94/1.01  ------ Resolution
% 2.94/1.01  
% 2.94/1.01  res_num_of_clauses:                     0
% 2.94/1.01  res_num_in_passive:                     0
% 2.94/1.01  res_num_in_active:                      0
% 2.94/1.01  res_num_of_loops:                       162
% 2.94/1.01  res_forward_subset_subsumed:            59
% 2.94/1.01  res_backward_subset_subsumed:           2
% 2.94/1.01  res_forward_subsumed:                   0
% 2.94/1.01  res_backward_subsumed:                  0
% 2.94/1.01  res_forward_subsumption_resolution:     1
% 2.94/1.01  res_backward_subsumption_resolution:    0
% 2.94/1.01  res_clause_to_clause_subsumption:       179
% 2.94/1.01  res_orphan_elimination:                 0
% 2.94/1.01  res_tautology_del:                      34
% 2.94/1.01  res_num_eq_res_simplified:              0
% 2.94/1.01  res_num_sel_changes:                    0
% 2.94/1.01  res_moves_from_active_to_pass:          0
% 2.94/1.01  
% 2.94/1.01  ------ Superposition
% 2.94/1.01  
% 2.94/1.01  sup_time_total:                         0.
% 2.94/1.01  sup_time_generating:                    0.
% 2.94/1.01  sup_time_sim_full:                      0.
% 2.94/1.01  sup_time_sim_immed:                     0.
% 2.94/1.01  
% 2.94/1.01  sup_num_of_clauses:                     41
% 2.94/1.01  sup_num_in_active:                      18
% 2.94/1.01  sup_num_in_passive:                     23
% 2.94/1.01  sup_num_of_loops:                       72
% 2.94/1.01  sup_fw_superposition:                   16
% 2.94/1.01  sup_bw_superposition:                   84
% 2.94/1.01  sup_immediate_simplified:               79
% 2.94/1.01  sup_given_eliminated:                   0
% 2.94/1.01  comparisons_done:                       0
% 2.94/1.01  comparisons_avoided:                    24
% 2.94/1.01  
% 2.94/1.01  ------ Simplifications
% 2.94/1.01  
% 2.94/1.01  
% 2.94/1.01  sim_fw_subset_subsumed:                 58
% 2.94/1.01  sim_bw_subset_subsumed:                 4
% 2.94/1.01  sim_fw_subsumed:                        1
% 2.94/1.01  sim_bw_subsumed:                        1
% 2.94/1.01  sim_fw_subsumption_res:                 1
% 2.94/1.01  sim_bw_subsumption_res:                 0
% 2.94/1.01  sim_tautology_del:                      1
% 2.94/1.01  sim_eq_tautology_del:                   3
% 2.94/1.01  sim_eq_res_simp:                        0
% 2.94/1.01  sim_fw_demodulated:                     0
% 2.94/1.01  sim_bw_demodulated:                     54
% 2.94/1.01  sim_light_normalised:                   24
% 2.94/1.01  sim_joinable_taut:                      0
% 2.94/1.01  sim_joinable_simp:                      0
% 2.94/1.01  sim_ac_normalised:                      0
% 2.94/1.01  sim_smt_subsumption:                    0
% 2.94/1.01  
%------------------------------------------------------------------------------
