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

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :  224 (5201 expanded)
%              Number of clauses        :  141 (1543 expanded)
%              Number of leaves         :   22 (1379 expanded)
%              Depth                    :   28
%              Number of atoms          :  649 (33388 expanded)
%              Number of equality atoms :  275 (10506 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
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

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f19,conjecture,(
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

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f48,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

fof(f53,plain,(
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

fof(f52,plain,(
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

fof(f51,plain,
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

fof(f54,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f49,f53,f52,f51])).

fof(f84,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f54])).

fof(f83,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f85,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f54])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f77,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f80,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f82,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f78,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f81,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f58,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f76,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f60,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f87,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f62,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f61,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f59,plain,(
    ! [X0] :
      ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f86,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f88,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_16,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_403,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_10,c_16])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_407,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_403,c_16,c_10,c_9])).

cnf(c_408,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_407])).

cnf(c_534,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(resolution,[status(thm)],[c_18,c_408])).

cnf(c_538,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_534,c_18,c_408])).

cnf(c_539,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(renaming,[status(thm)],[c_538])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_621,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | u1_struct_0(sK0) != X1
    | u1_struct_0(sK1) != X2
    | k1_relat_1(X0) = X1
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_539,c_29])).

cnf(c_622,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | k1_relat_1(sK2) = u1_struct_0(sK0)
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_621])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_624,plain,
    ( k1_relat_1(sK2) = u1_struct_0(sK0)
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_622,c_30,c_28])).

cnf(c_815,plain,
    ( k1_relat_1(sK2) = u1_struct_0(sK0)
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_624])).

cnf(c_22,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_33,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_396,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_33])).

cnf(c_397,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_396])).

cnf(c_820,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_397])).

cnf(c_31,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_391,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_31])).

cnf(c_392,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_391])).

cnf(c_821,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_392])).

cnf(c_1275,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k2_struct_0(sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_815,c_820,c_821])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_23,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_364,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_23])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_382,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_364,c_32])).

cnf(c_383,plain,
    ( ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_382])).

cnf(c_366,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_364])).

cnf(c_385,plain,
    ( u1_struct_0(sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_383,c_32,c_31,c_366])).

cnf(c_822,plain,
    ( u1_struct_0(sK1) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_385])).

cnf(c_1263,plain,
    ( k2_struct_0(sK1) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_821,c_822])).

cnf(c_1278,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1275,c_1263])).

cnf(c_824,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1250,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_824])).

cnf(c_1272,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1250,c_820,c_821])).

cnf(c_1279,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1278,c_1272])).

cnf(c_832,plain,
    ( ~ m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(X0_59,X1_59)))
    | v1_relat_1(X0_58) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1244,plain,
    ( m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(X0_59,X1_59))) != iProver_top
    | v1_relat_1(X0_58) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_832])).

cnf(c_1612,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1279,c_1244])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_835,plain,
    ( ~ v1_relat_1(X0_58)
    | k1_relat_1(k4_relat_1(X0_58)) = k2_relat_1(X0_58) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1241,plain,
    ( k1_relat_1(k4_relat_1(X0_58)) = k2_relat_1(X0_58)
    | v1_relat_1(X0_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_835])).

cnf(c_1649,plain,
    ( k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1612,c_1241])).

cnf(c_19,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_827,plain,
    ( m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_58),k2_relat_1(X0_58))))
    | ~ v1_funct_1(X0_58)
    | ~ v1_relat_1(X0_58) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1249,plain,
    ( m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_58),k2_relat_1(X0_58)))) = iProver_top
    | v1_funct_1(X0_58) != iProver_top
    | v1_relat_1(X0_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_827])).

cnf(c_2116,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k4_relat_1(sK2))))) = iProver_top
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1649,c_1249])).

cnf(c_37,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_39,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1415,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_832])).

cnf(c_1416,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1415])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_26,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_509,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_26])).

cnf(c_510,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_509])).

cnf(c_512,plain,
    ( ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_510,c_30])).

cnf(c_817,plain,
    ( ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_512])).

cnf(c_1254,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_817])).

cnf(c_1436,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1254,c_28,c_817,c_1415])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_834,plain,
    ( ~ v1_funct_1(X0_58)
    | v1_funct_1(k2_funct_1(X0_58))
    | ~ v1_relat_1(X0_58) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1242,plain,
    ( v1_funct_1(X0_58) != iProver_top
    | v1_funct_1(k2_funct_1(X0_58)) = iProver_top
    | v1_relat_1(X0_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_834])).

cnf(c_1462,plain,
    ( v1_funct_1(k4_relat_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1436,c_1242])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_833,plain,
    ( ~ v1_funct_1(X0_58)
    | ~ v1_relat_1(X0_58)
    | v1_relat_1(k2_funct_1(X0_58)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1243,plain,
    ( v1_funct_1(X0_58) != iProver_top
    | v1_relat_1(X0_58) != iProver_top
    | v1_relat_1(k2_funct_1(X0_58)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_833])).

cnf(c_1692,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1436,c_1243])).

cnf(c_3303,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k4_relat_1(sK2))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2116,c_37,c_39,c_1416,c_1462,c_1692])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_836,plain,
    ( ~ v1_relat_1(X0_58)
    | k2_relat_1(k4_relat_1(X0_58)) = k1_relat_1(X0_58) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1240,plain,
    ( k2_relat_1(k4_relat_1(X0_58)) = k1_relat_1(X0_58)
    | v1_relat_1(X0_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_836])).

cnf(c_1650,plain,
    ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1612,c_1240])).

cnf(c_3307,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3303,c_1650])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_829,plain,
    ( ~ m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(X0_59,X1_59)))
    | k8_relset_1(X0_59,X1_59,X0_58,X1_59) = k1_relset_1(X0_59,X1_59,X0_58) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1247,plain,
    ( k8_relset_1(X0_59,X1_59,X0_58,X1_59) = k1_relset_1(X0_59,X1_59,X0_58)
    | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(X0_59,X1_59))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_829])).

cnf(c_3312,plain,
    ( k8_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2),k1_relat_1(sK2)) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) ),
    inference(superposition,[status(thm)],[c_3307,c_1247])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_830,plain,
    ( ~ m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(X0_59,X1_59)))
    | k8_relset_1(X0_59,X1_59,X0_58,X2_59) = k10_relat_1(X0_58,X2_59) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1246,plain,
    ( k8_relset_1(X0_59,X1_59,X0_58,X2_59) = k10_relat_1(X0_58,X2_59)
    | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(X0_59,X1_59))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_830])).

cnf(c_3313,plain,
    ( k8_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2),X0_59) = k10_relat_1(k4_relat_1(sK2),X0_59) ),
    inference(superposition,[status(thm)],[c_3307,c_1246])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k10_relat_1(k2_funct_1(X0),X1) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_491,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k10_relat_1(k2_funct_1(X0),X1) = k9_relat_1(X0,X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_26])).

cnf(c_492,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k10_relat_1(k2_funct_1(sK2),X0) = k9_relat_1(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_491])).

cnf(c_496,plain,
    ( ~ v1_relat_1(sK2)
    | k10_relat_1(k2_funct_1(sK2),X0) = k9_relat_1(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_492,c_30])).

cnf(c_818,plain,
    ( ~ v1_relat_1(sK2)
    | k10_relat_1(k2_funct_1(sK2),X0_59) = k9_relat_1(sK2,X0_59) ),
    inference(subtyping,[status(esa)],[c_496])).

cnf(c_1253,plain,
    ( k10_relat_1(k2_funct_1(sK2),X0_59) = k9_relat_1(sK2,X0_59)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_818])).

cnf(c_1441,plain,
    ( k10_relat_1(k2_funct_1(sK2),X0_59) = k9_relat_1(sK2,X0_59) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1253,c_28,c_818,c_1415])).

cnf(c_1444,plain,
    ( k10_relat_1(k4_relat_1(sK2),X0_59) = k9_relat_1(sK2,X0_59) ),
    inference(light_normalisation,[status(thm)],[c_1441,c_1436])).

cnf(c_3320,plain,
    ( k8_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2),X0_59) = k9_relat_1(sK2,X0_59) ),
    inference(light_normalisation,[status(thm)],[c_3313,c_1444])).

cnf(c_3322,plain,
    ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = k9_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(demodulation,[status(thm)],[c_3312,c_3320])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_831,plain,
    ( ~ m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(X0_59,X1_59)))
    | k2_relset_1(X0_59,X1_59,X0_58) = k2_relat_1(X0_58) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1245,plain,
    ( k2_relset_1(X0_59,X1_59,X0_58) = k2_relat_1(X0_58)
    | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(X0_59,X1_59))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_831])).

cnf(c_1764,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1279,c_1245])).

cnf(c_27,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_825,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_1269,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_825,c_820,c_821])).

cnf(c_1280,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_1278,c_1269])).

cnf(c_1954,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1764,c_1280])).

cnf(c_25,negated_conjecture,
    ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_826,negated_conjecture,
    ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1281,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1278,c_820])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_467,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_26])).

cnf(c_468,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_467])).

cnf(c_472,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_468,c_30])).

cnf(c_473,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_472])).

cnf(c_651,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1
    | u1_struct_0(sK0) != X0
    | u1_struct_0(sK1) != X1
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_473])).

cnf(c_652,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_651])).

cnf(c_654,plain,
    ( k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_652,c_28])).

cnf(c_813,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_654])).

cnf(c_1349,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_813,c_821,c_1280,c_1281])).

cnf(c_1350,plain,
    ( k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(equality_resolution_simp,[status(thm)],[c_1349])).

cnf(c_1364,plain,
    ( k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) != k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_826,c_821,c_1278,c_1281,c_1350])).

cnf(c_1439,plain,
    ( k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k4_relat_1(sK2)) != k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k4_relat_1(sK2)) != k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1436,c_1364])).

cnf(c_1960,plain,
    ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) != k2_relat_1(sK2)
    | k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) != k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1954,c_1439])).

cnf(c_3582,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) != k1_relat_1(sK2)
    | k9_relat_1(sK2,k1_relat_1(sK2)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_3322,c_1960])).

cnf(c_1641,plain,
    ( v1_funct_1(k4_relat_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1462,c_37,c_39,c_1416])).

cnf(c_2066,plain,
    ( k2_relset_1(k1_relat_1(X0_58),k2_relat_1(X0_58),X0_58) = k2_relat_1(X0_58)
    | v1_funct_1(X0_58) != iProver_top
    | v1_relat_1(X0_58) != iProver_top ),
    inference(superposition,[status(thm)],[c_1249,c_1245])).

cnf(c_3215,plain,
    ( k2_relset_1(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2)),k4_relat_1(sK2)) = k2_relat_1(k4_relat_1(sK2))
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1641,c_2066])).

cnf(c_3218,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3215,c_1649,c_1650])).

cnf(c_1958,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1954,c_1279])).

cnf(c_2,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_423,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_10,c_2])).

cnf(c_427,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_423,c_10,c_9,c_2])).

cnf(c_819,plain,
    ( ~ m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(X0_59,X1_59)))
    | k7_relat_1(X0_58,X0_59) = X0_58 ),
    inference(subtyping,[status(esa)],[c_427])).

cnf(c_1252,plain,
    ( k7_relat_1(X0_58,X0_59) = X0_58
    | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(X0_59,X1_59))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_819])).

cnf(c_2440,plain,
    ( k7_relat_1(sK2,k1_relat_1(sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_1958,c_1252])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_837,plain,
    ( ~ v1_relat_1(X0_58)
    | k2_relat_1(k7_relat_1(X0_58,X0_59)) = k9_relat_1(X0_58,X0_59) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1239,plain,
    ( k2_relat_1(k7_relat_1(X0_58,X0_59)) = k9_relat_1(X0_58,X0_59)
    | v1_relat_1(X0_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_837])).

cnf(c_1648,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0_59)) = k9_relat_1(sK2,X0_59) ),
    inference(superposition,[status(thm)],[c_1612,c_1239])).

cnf(c_2928,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2440,c_1648])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3582,c_3218,c_2928,c_1692,c_1416,c_39,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:14:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.76/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.01  
% 2.76/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.76/1.01  
% 2.76/1.01  ------  iProver source info
% 2.76/1.01  
% 2.76/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.76/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.76/1.01  git: non_committed_changes: false
% 2.76/1.01  git: last_make_outside_of_git: false
% 2.76/1.01  
% 2.76/1.01  ------ 
% 2.76/1.01  
% 2.76/1.01  ------ Input Options
% 2.76/1.01  
% 2.76/1.01  --out_options                           all
% 2.76/1.01  --tptp_safe_out                         true
% 2.76/1.01  --problem_path                          ""
% 2.76/1.01  --include_path                          ""
% 2.76/1.01  --clausifier                            res/vclausify_rel
% 2.76/1.01  --clausifier_options                    --mode clausify
% 2.76/1.01  --stdin                                 false
% 2.76/1.01  --stats_out                             all
% 2.76/1.01  
% 2.76/1.01  ------ General Options
% 2.76/1.01  
% 2.76/1.01  --fof                                   false
% 2.76/1.01  --time_out_real                         305.
% 2.76/1.01  --time_out_virtual                      -1.
% 2.76/1.01  --symbol_type_check                     false
% 2.76/1.01  --clausify_out                          false
% 2.76/1.01  --sig_cnt_out                           false
% 2.76/1.01  --trig_cnt_out                          false
% 2.76/1.01  --trig_cnt_out_tolerance                1.
% 2.76/1.01  --trig_cnt_out_sk_spl                   false
% 2.76/1.01  --abstr_cl_out                          false
% 2.76/1.01  
% 2.76/1.01  ------ Global Options
% 2.76/1.01  
% 2.76/1.01  --schedule                              default
% 2.76/1.01  --add_important_lit                     false
% 2.76/1.01  --prop_solver_per_cl                    1000
% 2.76/1.01  --min_unsat_core                        false
% 2.76/1.01  --soft_assumptions                      false
% 2.76/1.01  --soft_lemma_size                       3
% 2.76/1.01  --prop_impl_unit_size                   0
% 2.76/1.01  --prop_impl_unit                        []
% 2.76/1.01  --share_sel_clauses                     true
% 2.76/1.01  --reset_solvers                         false
% 2.76/1.01  --bc_imp_inh                            [conj_cone]
% 2.76/1.01  --conj_cone_tolerance                   3.
% 2.76/1.01  --extra_neg_conj                        none
% 2.76/1.01  --large_theory_mode                     true
% 2.76/1.01  --prolific_symb_bound                   200
% 2.76/1.01  --lt_threshold                          2000
% 2.76/1.01  --clause_weak_htbl                      true
% 2.76/1.01  --gc_record_bc_elim                     false
% 2.76/1.01  
% 2.76/1.01  ------ Preprocessing Options
% 2.76/1.01  
% 2.76/1.01  --preprocessing_flag                    true
% 2.76/1.01  --time_out_prep_mult                    0.1
% 2.76/1.01  --splitting_mode                        input
% 2.76/1.01  --splitting_grd                         true
% 2.76/1.01  --splitting_cvd                         false
% 2.76/1.01  --splitting_cvd_svl                     false
% 2.76/1.01  --splitting_nvd                         32
% 2.76/1.01  --sub_typing                            true
% 2.76/1.01  --prep_gs_sim                           true
% 2.76/1.01  --prep_unflatten                        true
% 2.76/1.01  --prep_res_sim                          true
% 2.76/1.01  --prep_upred                            true
% 2.76/1.01  --prep_sem_filter                       exhaustive
% 2.76/1.01  --prep_sem_filter_out                   false
% 2.76/1.01  --pred_elim                             true
% 2.76/1.01  --res_sim_input                         true
% 2.76/1.01  --eq_ax_congr_red                       true
% 2.76/1.01  --pure_diseq_elim                       true
% 2.76/1.01  --brand_transform                       false
% 2.76/1.01  --non_eq_to_eq                          false
% 2.76/1.01  --prep_def_merge                        true
% 2.76/1.01  --prep_def_merge_prop_impl              false
% 2.76/1.01  --prep_def_merge_mbd                    true
% 2.76/1.01  --prep_def_merge_tr_red                 false
% 2.76/1.01  --prep_def_merge_tr_cl                  false
% 2.76/1.01  --smt_preprocessing                     true
% 2.76/1.01  --smt_ac_axioms                         fast
% 2.76/1.01  --preprocessed_out                      false
% 2.76/1.01  --preprocessed_stats                    false
% 2.76/1.01  
% 2.76/1.01  ------ Abstraction refinement Options
% 2.76/1.01  
% 2.76/1.01  --abstr_ref                             []
% 2.76/1.01  --abstr_ref_prep                        false
% 2.76/1.01  --abstr_ref_until_sat                   false
% 2.76/1.01  --abstr_ref_sig_restrict                funpre
% 2.76/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.76/1.01  --abstr_ref_under                       []
% 2.76/1.01  
% 2.76/1.01  ------ SAT Options
% 2.76/1.01  
% 2.76/1.01  --sat_mode                              false
% 2.76/1.01  --sat_fm_restart_options                ""
% 2.76/1.01  --sat_gr_def                            false
% 2.76/1.01  --sat_epr_types                         true
% 2.76/1.01  --sat_non_cyclic_types                  false
% 2.76/1.01  --sat_finite_models                     false
% 2.76/1.01  --sat_fm_lemmas                         false
% 2.76/1.01  --sat_fm_prep                           false
% 2.76/1.01  --sat_fm_uc_incr                        true
% 2.76/1.01  --sat_out_model                         small
% 2.76/1.01  --sat_out_clauses                       false
% 2.76/1.01  
% 2.76/1.01  ------ QBF Options
% 2.76/1.01  
% 2.76/1.01  --qbf_mode                              false
% 2.76/1.01  --qbf_elim_univ                         false
% 2.76/1.01  --qbf_dom_inst                          none
% 2.76/1.01  --qbf_dom_pre_inst                      false
% 2.76/1.01  --qbf_sk_in                             false
% 2.76/1.01  --qbf_pred_elim                         true
% 2.76/1.01  --qbf_split                             512
% 2.76/1.01  
% 2.76/1.01  ------ BMC1 Options
% 2.76/1.01  
% 2.76/1.01  --bmc1_incremental                      false
% 2.76/1.01  --bmc1_axioms                           reachable_all
% 2.76/1.01  --bmc1_min_bound                        0
% 2.76/1.01  --bmc1_max_bound                        -1
% 2.76/1.01  --bmc1_max_bound_default                -1
% 2.76/1.01  --bmc1_symbol_reachability              true
% 2.76/1.01  --bmc1_property_lemmas                  false
% 2.76/1.01  --bmc1_k_induction                      false
% 2.76/1.01  --bmc1_non_equiv_states                 false
% 2.76/1.01  --bmc1_deadlock                         false
% 2.76/1.01  --bmc1_ucm                              false
% 2.76/1.01  --bmc1_add_unsat_core                   none
% 2.76/1.01  --bmc1_unsat_core_children              false
% 2.76/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.76/1.01  --bmc1_out_stat                         full
% 2.76/1.01  --bmc1_ground_init                      false
% 2.76/1.01  --bmc1_pre_inst_next_state              false
% 2.76/1.01  --bmc1_pre_inst_state                   false
% 2.76/1.01  --bmc1_pre_inst_reach_state             false
% 2.76/1.01  --bmc1_out_unsat_core                   false
% 2.76/1.01  --bmc1_aig_witness_out                  false
% 2.76/1.01  --bmc1_verbose                          false
% 2.76/1.01  --bmc1_dump_clauses_tptp                false
% 2.76/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.76/1.01  --bmc1_dump_file                        -
% 2.76/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.76/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.76/1.01  --bmc1_ucm_extend_mode                  1
% 2.76/1.01  --bmc1_ucm_init_mode                    2
% 2.76/1.01  --bmc1_ucm_cone_mode                    none
% 2.76/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.76/1.01  --bmc1_ucm_relax_model                  4
% 2.76/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.76/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.76/1.01  --bmc1_ucm_layered_model                none
% 2.76/1.01  --bmc1_ucm_max_lemma_size               10
% 2.76/1.01  
% 2.76/1.01  ------ AIG Options
% 2.76/1.01  
% 2.76/1.01  --aig_mode                              false
% 2.76/1.01  
% 2.76/1.01  ------ Instantiation Options
% 2.76/1.01  
% 2.76/1.01  --instantiation_flag                    true
% 2.76/1.01  --inst_sos_flag                         false
% 2.76/1.01  --inst_sos_phase                        true
% 2.76/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.76/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.76/1.01  --inst_lit_sel_side                     num_symb
% 2.76/1.01  --inst_solver_per_active                1400
% 2.76/1.01  --inst_solver_calls_frac                1.
% 2.76/1.01  --inst_passive_queue_type               priority_queues
% 2.76/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.76/1.01  --inst_passive_queues_freq              [25;2]
% 2.76/1.01  --inst_dismatching                      true
% 2.76/1.01  --inst_eager_unprocessed_to_passive     true
% 2.76/1.01  --inst_prop_sim_given                   true
% 2.76/1.01  --inst_prop_sim_new                     false
% 2.76/1.01  --inst_subs_new                         false
% 2.76/1.01  --inst_eq_res_simp                      false
% 2.76/1.01  --inst_subs_given                       false
% 2.76/1.01  --inst_orphan_elimination               true
% 2.76/1.01  --inst_learning_loop_flag               true
% 2.76/1.01  --inst_learning_start                   3000
% 2.76/1.01  --inst_learning_factor                  2
% 2.76/1.01  --inst_start_prop_sim_after_learn       3
% 2.76/1.01  --inst_sel_renew                        solver
% 2.76/1.01  --inst_lit_activity_flag                true
% 2.76/1.01  --inst_restr_to_given                   false
% 2.76/1.01  --inst_activity_threshold               500
% 2.76/1.01  --inst_out_proof                        true
% 2.76/1.01  
% 2.76/1.01  ------ Resolution Options
% 2.76/1.01  
% 2.76/1.01  --resolution_flag                       true
% 2.76/1.01  --res_lit_sel                           adaptive
% 2.76/1.01  --res_lit_sel_side                      none
% 2.76/1.01  --res_ordering                          kbo
% 2.76/1.01  --res_to_prop_solver                    active
% 2.76/1.01  --res_prop_simpl_new                    false
% 2.76/1.01  --res_prop_simpl_given                  true
% 2.76/1.01  --res_passive_queue_type                priority_queues
% 2.76/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.76/1.01  --res_passive_queues_freq               [15;5]
% 2.76/1.01  --res_forward_subs                      full
% 2.76/1.01  --res_backward_subs                     full
% 2.76/1.01  --res_forward_subs_resolution           true
% 2.76/1.01  --res_backward_subs_resolution          true
% 2.76/1.01  --res_orphan_elimination                true
% 2.76/1.01  --res_time_limit                        2.
% 2.76/1.01  --res_out_proof                         true
% 2.76/1.01  
% 2.76/1.01  ------ Superposition Options
% 2.76/1.01  
% 2.76/1.01  --superposition_flag                    true
% 2.76/1.01  --sup_passive_queue_type                priority_queues
% 2.76/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.76/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.76/1.01  --demod_completeness_check              fast
% 2.76/1.01  --demod_use_ground                      true
% 2.76/1.01  --sup_to_prop_solver                    passive
% 2.76/1.01  --sup_prop_simpl_new                    true
% 2.76/1.01  --sup_prop_simpl_given                  true
% 2.76/1.01  --sup_fun_splitting                     false
% 2.76/1.01  --sup_smt_interval                      50000
% 2.76/1.01  
% 2.76/1.01  ------ Superposition Simplification Setup
% 2.76/1.01  
% 2.76/1.01  --sup_indices_passive                   []
% 2.76/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.76/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/1.01  --sup_full_bw                           [BwDemod]
% 2.76/1.01  --sup_immed_triv                        [TrivRules]
% 2.76/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.76/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/1.01  --sup_immed_bw_main                     []
% 2.76/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.76/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.76/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.76/1.01  
% 2.76/1.01  ------ Combination Options
% 2.76/1.01  
% 2.76/1.01  --comb_res_mult                         3
% 2.76/1.01  --comb_sup_mult                         2
% 2.76/1.01  --comb_inst_mult                        10
% 2.76/1.01  
% 2.76/1.01  ------ Debug Options
% 2.76/1.01  
% 2.76/1.01  --dbg_backtrace                         false
% 2.76/1.01  --dbg_dump_prop_clauses                 false
% 2.76/1.01  --dbg_dump_prop_clauses_file            -
% 2.76/1.01  --dbg_out_stat                          false
% 2.76/1.01  ------ Parsing...
% 2.76/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.76/1.01  
% 2.76/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 2.76/1.01  
% 2.76/1.01  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.76/1.01  
% 2.76/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.76/1.01  ------ Proving...
% 2.76/1.01  ------ Problem Properties 
% 2.76/1.01  
% 2.76/1.01  
% 2.76/1.01  clauses                                 26
% 2.76/1.01  conjectures                             4
% 2.76/1.01  EPR                                     1
% 2.76/1.01  Horn                                    24
% 2.76/1.01  unary                                   6
% 2.76/1.01  binary                                  16
% 2.76/1.01  lits                                    51
% 2.76/1.01  lits eq                                 23
% 2.76/1.01  fd_pure                                 0
% 2.76/1.01  fd_pseudo                               0
% 2.76/1.01  fd_cond                                 0
% 2.76/1.01  fd_pseudo_cond                          0
% 2.76/1.01  AC symbols                              0
% 2.76/1.01  
% 2.76/1.01  ------ Schedule dynamic 5 is on 
% 2.76/1.01  
% 2.76/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.76/1.01  
% 2.76/1.01  
% 2.76/1.01  ------ 
% 2.76/1.01  Current options:
% 2.76/1.01  ------ 
% 2.76/1.01  
% 2.76/1.01  ------ Input Options
% 2.76/1.01  
% 2.76/1.01  --out_options                           all
% 2.76/1.01  --tptp_safe_out                         true
% 2.76/1.01  --problem_path                          ""
% 2.76/1.01  --include_path                          ""
% 2.76/1.01  --clausifier                            res/vclausify_rel
% 2.76/1.01  --clausifier_options                    --mode clausify
% 2.76/1.01  --stdin                                 false
% 2.76/1.01  --stats_out                             all
% 2.76/1.01  
% 2.76/1.01  ------ General Options
% 2.76/1.01  
% 2.76/1.01  --fof                                   false
% 2.76/1.01  --time_out_real                         305.
% 2.76/1.01  --time_out_virtual                      -1.
% 2.76/1.01  --symbol_type_check                     false
% 2.76/1.01  --clausify_out                          false
% 2.76/1.01  --sig_cnt_out                           false
% 2.76/1.01  --trig_cnt_out                          false
% 2.76/1.01  --trig_cnt_out_tolerance                1.
% 2.76/1.01  --trig_cnt_out_sk_spl                   false
% 2.76/1.01  --abstr_cl_out                          false
% 2.76/1.01  
% 2.76/1.01  ------ Global Options
% 2.76/1.01  
% 2.76/1.01  --schedule                              default
% 2.76/1.01  --add_important_lit                     false
% 2.76/1.01  --prop_solver_per_cl                    1000
% 2.76/1.01  --min_unsat_core                        false
% 2.76/1.01  --soft_assumptions                      false
% 2.76/1.01  --soft_lemma_size                       3
% 2.76/1.01  --prop_impl_unit_size                   0
% 2.76/1.01  --prop_impl_unit                        []
% 2.76/1.01  --share_sel_clauses                     true
% 2.76/1.01  --reset_solvers                         false
% 2.76/1.01  --bc_imp_inh                            [conj_cone]
% 2.76/1.01  --conj_cone_tolerance                   3.
% 2.76/1.01  --extra_neg_conj                        none
% 2.76/1.01  --large_theory_mode                     true
% 2.76/1.01  --prolific_symb_bound                   200
% 2.76/1.01  --lt_threshold                          2000
% 2.76/1.01  --clause_weak_htbl                      true
% 2.76/1.01  --gc_record_bc_elim                     false
% 2.76/1.01  
% 2.76/1.01  ------ Preprocessing Options
% 2.76/1.01  
% 2.76/1.01  --preprocessing_flag                    true
% 2.76/1.01  --time_out_prep_mult                    0.1
% 2.76/1.01  --splitting_mode                        input
% 2.76/1.01  --splitting_grd                         true
% 2.76/1.01  --splitting_cvd                         false
% 2.76/1.01  --splitting_cvd_svl                     false
% 2.76/1.01  --splitting_nvd                         32
% 2.76/1.01  --sub_typing                            true
% 2.76/1.01  --prep_gs_sim                           true
% 2.76/1.01  --prep_unflatten                        true
% 2.76/1.01  --prep_res_sim                          true
% 2.76/1.01  --prep_upred                            true
% 2.76/1.01  --prep_sem_filter                       exhaustive
% 2.76/1.01  --prep_sem_filter_out                   false
% 2.76/1.01  --pred_elim                             true
% 2.76/1.01  --res_sim_input                         true
% 2.76/1.01  --eq_ax_congr_red                       true
% 2.76/1.01  --pure_diseq_elim                       true
% 2.76/1.01  --brand_transform                       false
% 2.76/1.01  --non_eq_to_eq                          false
% 2.76/1.01  --prep_def_merge                        true
% 2.76/1.01  --prep_def_merge_prop_impl              false
% 2.76/1.01  --prep_def_merge_mbd                    true
% 2.76/1.01  --prep_def_merge_tr_red                 false
% 2.76/1.01  --prep_def_merge_tr_cl                  false
% 2.76/1.01  --smt_preprocessing                     true
% 2.76/1.01  --smt_ac_axioms                         fast
% 2.76/1.01  --preprocessed_out                      false
% 2.76/1.01  --preprocessed_stats                    false
% 2.76/1.01  
% 2.76/1.01  ------ Abstraction refinement Options
% 2.76/1.01  
% 2.76/1.01  --abstr_ref                             []
% 2.76/1.01  --abstr_ref_prep                        false
% 2.76/1.01  --abstr_ref_until_sat                   false
% 2.76/1.01  --abstr_ref_sig_restrict                funpre
% 2.76/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.76/1.01  --abstr_ref_under                       []
% 2.76/1.01  
% 2.76/1.01  ------ SAT Options
% 2.76/1.01  
% 2.76/1.01  --sat_mode                              false
% 2.76/1.01  --sat_fm_restart_options                ""
% 2.76/1.01  --sat_gr_def                            false
% 2.76/1.01  --sat_epr_types                         true
% 2.76/1.01  --sat_non_cyclic_types                  false
% 2.76/1.01  --sat_finite_models                     false
% 2.76/1.01  --sat_fm_lemmas                         false
% 2.76/1.01  --sat_fm_prep                           false
% 2.76/1.01  --sat_fm_uc_incr                        true
% 2.76/1.01  --sat_out_model                         small
% 2.76/1.01  --sat_out_clauses                       false
% 2.76/1.01  
% 2.76/1.01  ------ QBF Options
% 2.76/1.01  
% 2.76/1.01  --qbf_mode                              false
% 2.76/1.01  --qbf_elim_univ                         false
% 2.76/1.01  --qbf_dom_inst                          none
% 2.76/1.01  --qbf_dom_pre_inst                      false
% 2.76/1.01  --qbf_sk_in                             false
% 2.76/1.01  --qbf_pred_elim                         true
% 2.76/1.01  --qbf_split                             512
% 2.76/1.01  
% 2.76/1.01  ------ BMC1 Options
% 2.76/1.01  
% 2.76/1.01  --bmc1_incremental                      false
% 2.76/1.01  --bmc1_axioms                           reachable_all
% 2.76/1.01  --bmc1_min_bound                        0
% 2.76/1.01  --bmc1_max_bound                        -1
% 2.76/1.01  --bmc1_max_bound_default                -1
% 2.76/1.01  --bmc1_symbol_reachability              true
% 2.76/1.01  --bmc1_property_lemmas                  false
% 2.76/1.01  --bmc1_k_induction                      false
% 2.76/1.01  --bmc1_non_equiv_states                 false
% 2.76/1.01  --bmc1_deadlock                         false
% 2.76/1.01  --bmc1_ucm                              false
% 2.76/1.01  --bmc1_add_unsat_core                   none
% 2.76/1.01  --bmc1_unsat_core_children              false
% 2.76/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.76/1.01  --bmc1_out_stat                         full
% 2.76/1.01  --bmc1_ground_init                      false
% 2.76/1.01  --bmc1_pre_inst_next_state              false
% 2.76/1.01  --bmc1_pre_inst_state                   false
% 2.76/1.01  --bmc1_pre_inst_reach_state             false
% 2.76/1.01  --bmc1_out_unsat_core                   false
% 2.76/1.01  --bmc1_aig_witness_out                  false
% 2.76/1.01  --bmc1_verbose                          false
% 2.76/1.01  --bmc1_dump_clauses_tptp                false
% 2.76/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.76/1.01  --bmc1_dump_file                        -
% 2.76/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.76/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.76/1.01  --bmc1_ucm_extend_mode                  1
% 2.76/1.01  --bmc1_ucm_init_mode                    2
% 2.76/1.01  --bmc1_ucm_cone_mode                    none
% 2.76/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.76/1.01  --bmc1_ucm_relax_model                  4
% 2.76/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.76/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.76/1.01  --bmc1_ucm_layered_model                none
% 2.76/1.01  --bmc1_ucm_max_lemma_size               10
% 2.76/1.01  
% 2.76/1.01  ------ AIG Options
% 2.76/1.01  
% 2.76/1.01  --aig_mode                              false
% 2.76/1.01  
% 2.76/1.01  ------ Instantiation Options
% 2.76/1.01  
% 2.76/1.01  --instantiation_flag                    true
% 2.76/1.01  --inst_sos_flag                         false
% 2.76/1.01  --inst_sos_phase                        true
% 2.76/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.76/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.76/1.01  --inst_lit_sel_side                     none
% 2.76/1.01  --inst_solver_per_active                1400
% 2.76/1.01  --inst_solver_calls_frac                1.
% 2.76/1.01  --inst_passive_queue_type               priority_queues
% 2.76/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.76/1.01  --inst_passive_queues_freq              [25;2]
% 2.76/1.01  --inst_dismatching                      true
% 2.76/1.01  --inst_eager_unprocessed_to_passive     true
% 2.76/1.01  --inst_prop_sim_given                   true
% 2.76/1.01  --inst_prop_sim_new                     false
% 2.76/1.01  --inst_subs_new                         false
% 2.76/1.01  --inst_eq_res_simp                      false
% 2.76/1.01  --inst_subs_given                       false
% 2.76/1.01  --inst_orphan_elimination               true
% 2.76/1.01  --inst_learning_loop_flag               true
% 2.76/1.01  --inst_learning_start                   3000
% 2.76/1.01  --inst_learning_factor                  2
% 2.76/1.01  --inst_start_prop_sim_after_learn       3
% 2.76/1.01  --inst_sel_renew                        solver
% 2.76/1.01  --inst_lit_activity_flag                true
% 2.76/1.01  --inst_restr_to_given                   false
% 2.76/1.01  --inst_activity_threshold               500
% 2.76/1.01  --inst_out_proof                        true
% 2.76/1.01  
% 2.76/1.01  ------ Resolution Options
% 2.76/1.01  
% 2.76/1.01  --resolution_flag                       false
% 2.76/1.01  --res_lit_sel                           adaptive
% 2.76/1.01  --res_lit_sel_side                      none
% 2.76/1.01  --res_ordering                          kbo
% 2.76/1.01  --res_to_prop_solver                    active
% 2.76/1.01  --res_prop_simpl_new                    false
% 2.76/1.01  --res_prop_simpl_given                  true
% 2.76/1.01  --res_passive_queue_type                priority_queues
% 2.76/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.76/1.01  --res_passive_queues_freq               [15;5]
% 2.76/1.01  --res_forward_subs                      full
% 2.76/1.01  --res_backward_subs                     full
% 2.76/1.01  --res_forward_subs_resolution           true
% 2.76/1.01  --res_backward_subs_resolution          true
% 2.76/1.01  --res_orphan_elimination                true
% 2.76/1.01  --res_time_limit                        2.
% 2.76/1.01  --res_out_proof                         true
% 2.76/1.01  
% 2.76/1.01  ------ Superposition Options
% 2.76/1.01  
% 2.76/1.01  --superposition_flag                    true
% 2.76/1.01  --sup_passive_queue_type                priority_queues
% 2.76/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.76/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.76/1.01  --demod_completeness_check              fast
% 2.76/1.01  --demod_use_ground                      true
% 2.76/1.01  --sup_to_prop_solver                    passive
% 2.76/1.01  --sup_prop_simpl_new                    true
% 2.76/1.01  --sup_prop_simpl_given                  true
% 2.76/1.01  --sup_fun_splitting                     false
% 2.76/1.01  --sup_smt_interval                      50000
% 2.76/1.01  
% 2.76/1.01  ------ Superposition Simplification Setup
% 2.76/1.01  
% 2.76/1.01  --sup_indices_passive                   []
% 2.76/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.76/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/1.01  --sup_full_bw                           [BwDemod]
% 2.76/1.01  --sup_immed_triv                        [TrivRules]
% 2.76/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.76/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/1.01  --sup_immed_bw_main                     []
% 2.76/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.76/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.76/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.76/1.01  
% 2.76/1.01  ------ Combination Options
% 2.76/1.01  
% 2.76/1.01  --comb_res_mult                         3
% 2.76/1.01  --comb_sup_mult                         2
% 2.76/1.01  --comb_inst_mult                        10
% 2.76/1.01  
% 2.76/1.01  ------ Debug Options
% 2.76/1.01  
% 2.76/1.01  --dbg_backtrace                         false
% 2.76/1.01  --dbg_dump_prop_clauses                 false
% 2.76/1.01  --dbg_dump_prop_clauses_file            -
% 2.76/1.01  --dbg_out_stat                          false
% 2.76/1.01  
% 2.76/1.01  
% 2.76/1.01  
% 2.76/1.01  
% 2.76/1.01  ------ Proving...
% 2.76/1.01  
% 2.76/1.01  
% 2.76/1.01  % SZS status Theorem for theBenchmark.p
% 2.76/1.01  
% 2.76/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.76/1.01  
% 2.76/1.01  fof(f14,axiom,(
% 2.76/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.76/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/1.01  
% 2.76/1.01  fof(f39,plain,(
% 2.76/1.01    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.76/1.01    inference(ennf_transformation,[],[f14])).
% 2.76/1.01  
% 2.76/1.01  fof(f40,plain,(
% 2.76/1.01    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.76/1.01    inference(flattening,[],[f39])).
% 2.76/1.01  
% 2.76/1.01  fof(f72,plain,(
% 2.76/1.01    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.76/1.01    inference(cnf_transformation,[],[f40])).
% 2.76/1.01  
% 2.76/1.01  fof(f9,axiom,(
% 2.76/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.76/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/1.01  
% 2.76/1.01  fof(f21,plain,(
% 2.76/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.76/1.01    inference(pure_predicate_removal,[],[f9])).
% 2.76/1.01  
% 2.76/1.01  fof(f33,plain,(
% 2.76/1.01    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.76/1.01    inference(ennf_transformation,[],[f21])).
% 2.76/1.01  
% 2.76/1.01  fof(f65,plain,(
% 2.76/1.01    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.76/1.01    inference(cnf_transformation,[],[f33])).
% 2.76/1.01  
% 2.76/1.01  fof(f13,axiom,(
% 2.76/1.01    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.76/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/1.01  
% 2.76/1.01  fof(f37,plain,(
% 2.76/1.01    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.76/1.01    inference(ennf_transformation,[],[f13])).
% 2.76/1.01  
% 2.76/1.01  fof(f38,plain,(
% 2.76/1.01    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.76/1.01    inference(flattening,[],[f37])).
% 2.76/1.01  
% 2.76/1.01  fof(f50,plain,(
% 2.76/1.01    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.76/1.01    inference(nnf_transformation,[],[f38])).
% 2.76/1.01  
% 2.76/1.01  fof(f70,plain,(
% 2.76/1.01    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.76/1.01    inference(cnf_transformation,[],[f50])).
% 2.76/1.01  
% 2.76/1.01  fof(f8,axiom,(
% 2.76/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.76/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/1.01  
% 2.76/1.01  fof(f32,plain,(
% 2.76/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.76/1.01    inference(ennf_transformation,[],[f8])).
% 2.76/1.01  
% 2.76/1.01  fof(f64,plain,(
% 2.76/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.76/1.01    inference(cnf_transformation,[],[f32])).
% 2.76/1.01  
% 2.76/1.01  fof(f19,conjecture,(
% 2.76/1.01    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 2.76/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/1.01  
% 2.76/1.01  fof(f20,negated_conjecture,(
% 2.76/1.01    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 2.76/1.01    inference(negated_conjecture,[],[f19])).
% 2.76/1.01  
% 2.76/1.01  fof(f48,plain,(
% 2.76/1.01    ? [X0] : (? [X1] : (? [X2] : (((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 2.76/1.01    inference(ennf_transformation,[],[f20])).
% 2.76/1.01  
% 2.76/1.01  fof(f49,plain,(
% 2.76/1.01    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 2.76/1.01    inference(flattening,[],[f48])).
% 2.76/1.01  
% 2.76/1.01  fof(f53,plain,(
% 2.76/1.01    ( ! [X0,X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.76/1.02    introduced(choice_axiom,[])).
% 2.76/1.02  
% 2.76/1.02  fof(f52,plain,(
% 2.76/1.02    ( ! [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(sK1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 2.76/1.02    introduced(choice_axiom,[])).
% 2.76/1.02  
% 2.76/1.02  fof(f51,plain,(
% 2.76/1.02    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 2.76/1.02    introduced(choice_axiom,[])).
% 2.76/1.02  
% 2.76/1.02  fof(f54,plain,(
% 2.76/1.02    (((k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.76/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f49,f53,f52,f51])).
% 2.76/1.02  
% 2.76/1.02  fof(f84,plain,(
% 2.76/1.02    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.76/1.02    inference(cnf_transformation,[],[f54])).
% 2.76/1.02  
% 2.76/1.02  fof(f83,plain,(
% 2.76/1.02    v1_funct_1(sK2)),
% 2.76/1.02    inference(cnf_transformation,[],[f54])).
% 2.76/1.02  
% 2.76/1.02  fof(f85,plain,(
% 2.76/1.02    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.76/1.02    inference(cnf_transformation,[],[f54])).
% 2.76/1.02  
% 2.76/1.02  fof(f16,axiom,(
% 2.76/1.02    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.76/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/1.02  
% 2.76/1.02  fof(f43,plain,(
% 2.76/1.02    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.76/1.02    inference(ennf_transformation,[],[f16])).
% 2.76/1.02  
% 2.76/1.02  fof(f77,plain,(
% 2.76/1.02    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.76/1.02    inference(cnf_transformation,[],[f43])).
% 2.76/1.02  
% 2.76/1.02  fof(f80,plain,(
% 2.76/1.02    l1_struct_0(sK0)),
% 2.76/1.02    inference(cnf_transformation,[],[f54])).
% 2.76/1.02  
% 2.76/1.02  fof(f82,plain,(
% 2.76/1.02    l1_struct_0(sK1)),
% 2.76/1.02    inference(cnf_transformation,[],[f54])).
% 2.76/1.02  
% 2.76/1.02  fof(f1,axiom,(
% 2.76/1.02    v1_xboole_0(k1_xboole_0)),
% 2.76/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/1.02  
% 2.76/1.02  fof(f55,plain,(
% 2.76/1.02    v1_xboole_0(k1_xboole_0)),
% 2.76/1.02    inference(cnf_transformation,[],[f1])).
% 2.76/1.02  
% 2.76/1.02  fof(f17,axiom,(
% 2.76/1.02    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.76/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/1.02  
% 2.76/1.02  fof(f44,plain,(
% 2.76/1.02    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.76/1.02    inference(ennf_transformation,[],[f17])).
% 2.76/1.02  
% 2.76/1.02  fof(f45,plain,(
% 2.76/1.02    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.76/1.02    inference(flattening,[],[f44])).
% 2.76/1.02  
% 2.76/1.02  fof(f78,plain,(
% 2.76/1.02    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.76/1.02    inference(cnf_transformation,[],[f45])).
% 2.76/1.02  
% 2.76/1.02  fof(f81,plain,(
% 2.76/1.02    ~v2_struct_0(sK1)),
% 2.76/1.02    inference(cnf_transformation,[],[f54])).
% 2.76/1.02  
% 2.76/1.02  fof(f4,axiom,(
% 2.76/1.02    ! [X0] : (v1_relat_1(X0) => (k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 2.76/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/1.02  
% 2.76/1.02  fof(f25,plain,(
% 2.76/1.02    ! [X0] : ((k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.76/1.02    inference(ennf_transformation,[],[f4])).
% 2.76/1.02  
% 2.76/1.02  fof(f58,plain,(
% 2.76/1.02    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.76/1.02    inference(cnf_transformation,[],[f25])).
% 2.76/1.02  
% 2.76/1.02  fof(f15,axiom,(
% 2.76/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.76/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/1.02  
% 2.76/1.02  fof(f41,plain,(
% 2.76/1.02    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.76/1.02    inference(ennf_transformation,[],[f15])).
% 2.76/1.02  
% 2.76/1.02  fof(f42,plain,(
% 2.76/1.02    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.76/1.02    inference(flattening,[],[f41])).
% 2.76/1.02  
% 2.76/1.02  fof(f76,plain,(
% 2.76/1.02    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.76/1.02    inference(cnf_transformation,[],[f42])).
% 2.76/1.02  
% 2.76/1.02  fof(f5,axiom,(
% 2.76/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 2.76/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/1.02  
% 2.76/1.02  fof(f26,plain,(
% 2.76/1.02    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.76/1.02    inference(ennf_transformation,[],[f5])).
% 2.76/1.02  
% 2.76/1.02  fof(f27,plain,(
% 2.76/1.02    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.76/1.02    inference(flattening,[],[f26])).
% 2.76/1.02  
% 2.76/1.02  fof(f60,plain,(
% 2.76/1.02    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.76/1.02    inference(cnf_transformation,[],[f27])).
% 2.76/1.02  
% 2.76/1.02  fof(f87,plain,(
% 2.76/1.02    v2_funct_1(sK2)),
% 2.76/1.02    inference(cnf_transformation,[],[f54])).
% 2.76/1.02  
% 2.76/1.02  fof(f6,axiom,(
% 2.76/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.76/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/1.02  
% 2.76/1.02  fof(f28,plain,(
% 2.76/1.02    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.76/1.02    inference(ennf_transformation,[],[f6])).
% 2.76/1.02  
% 2.76/1.02  fof(f29,plain,(
% 2.76/1.02    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.76/1.02    inference(flattening,[],[f28])).
% 2.76/1.02  
% 2.76/1.02  fof(f62,plain,(
% 2.76/1.02    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.76/1.02    inference(cnf_transformation,[],[f29])).
% 2.76/1.02  
% 2.76/1.02  fof(f61,plain,(
% 2.76/1.02    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.76/1.02    inference(cnf_transformation,[],[f29])).
% 2.76/1.02  
% 2.76/1.02  fof(f59,plain,(
% 2.76/1.02    ( ! [X0] : (k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.76/1.02    inference(cnf_transformation,[],[f25])).
% 2.76/1.02  
% 2.76/1.02  fof(f12,axiom,(
% 2.76/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 2.76/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/1.02  
% 2.76/1.02  fof(f36,plain,(
% 2.76/1.02    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.76/1.02    inference(ennf_transformation,[],[f12])).
% 2.76/1.02  
% 2.76/1.02  fof(f69,plain,(
% 2.76/1.02    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.76/1.02    inference(cnf_transformation,[],[f36])).
% 2.76/1.02  
% 2.76/1.02  fof(f11,axiom,(
% 2.76/1.02    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 2.76/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/1.02  
% 2.76/1.02  fof(f35,plain,(
% 2.76/1.02    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.76/1.02    inference(ennf_transformation,[],[f11])).
% 2.76/1.02  
% 2.76/1.02  fof(f67,plain,(
% 2.76/1.02    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.76/1.02    inference(cnf_transformation,[],[f35])).
% 2.76/1.02  
% 2.76/1.02  fof(f7,axiom,(
% 2.76/1.02    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 2.76/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/1.02  
% 2.76/1.02  fof(f30,plain,(
% 2.76/1.02    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.76/1.02    inference(ennf_transformation,[],[f7])).
% 2.76/1.02  
% 2.76/1.02  fof(f31,plain,(
% 2.76/1.02    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.76/1.02    inference(flattening,[],[f30])).
% 2.76/1.02  
% 2.76/1.02  fof(f63,plain,(
% 2.76/1.02    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.76/1.02    inference(cnf_transformation,[],[f31])).
% 2.76/1.02  
% 2.76/1.02  fof(f10,axiom,(
% 2.76/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.76/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/1.02  
% 2.76/1.02  fof(f34,plain,(
% 2.76/1.02    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.76/1.02    inference(ennf_transformation,[],[f10])).
% 2.76/1.02  
% 2.76/1.02  fof(f66,plain,(
% 2.76/1.02    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.76/1.02    inference(cnf_transformation,[],[f34])).
% 2.76/1.02  
% 2.76/1.02  fof(f86,plain,(
% 2.76/1.02    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 2.76/1.02    inference(cnf_transformation,[],[f54])).
% 2.76/1.02  
% 2.76/1.02  fof(f88,plain,(
% 2.76/1.02    k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)),
% 2.76/1.02    inference(cnf_transformation,[],[f54])).
% 2.76/1.02  
% 2.76/1.02  fof(f18,axiom,(
% 2.76/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.76/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/1.02  
% 2.76/1.02  fof(f46,plain,(
% 2.76/1.02    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.76/1.02    inference(ennf_transformation,[],[f18])).
% 2.76/1.02  
% 2.76/1.02  fof(f47,plain,(
% 2.76/1.02    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.76/1.02    inference(flattening,[],[f46])).
% 2.76/1.02  
% 2.76/1.02  fof(f79,plain,(
% 2.76/1.02    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.76/1.02    inference(cnf_transformation,[],[f47])).
% 2.76/1.02  
% 2.76/1.02  fof(f3,axiom,(
% 2.76/1.02    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.76/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/1.02  
% 2.76/1.02  fof(f23,plain,(
% 2.76/1.02    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.76/1.02    inference(ennf_transformation,[],[f3])).
% 2.76/1.02  
% 2.76/1.02  fof(f24,plain,(
% 2.76/1.02    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.76/1.02    inference(flattening,[],[f23])).
% 2.76/1.02  
% 2.76/1.02  fof(f57,plain,(
% 2.76/1.02    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.76/1.02    inference(cnf_transformation,[],[f24])).
% 2.76/1.02  
% 2.76/1.02  fof(f2,axiom,(
% 2.76/1.02    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.76/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/1.02  
% 2.76/1.02  fof(f22,plain,(
% 2.76/1.02    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.76/1.02    inference(ennf_transformation,[],[f2])).
% 2.76/1.02  
% 2.76/1.02  fof(f56,plain,(
% 2.76/1.02    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.76/1.02    inference(cnf_transformation,[],[f22])).
% 2.76/1.02  
% 2.76/1.02  cnf(c_18,plain,
% 2.76/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.76/1.02      | v1_partfun1(X0,X1)
% 2.76/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.76/1.02      | ~ v1_funct_1(X0)
% 2.76/1.02      | k1_xboole_0 = X2 ),
% 2.76/1.02      inference(cnf_transformation,[],[f72]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_10,plain,
% 2.76/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.76/1.02      | v4_relat_1(X0,X1) ),
% 2.76/1.02      inference(cnf_transformation,[],[f65]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_16,plain,
% 2.76/1.02      ( ~ v1_partfun1(X0,X1)
% 2.76/1.02      | ~ v4_relat_1(X0,X1)
% 2.76/1.02      | ~ v1_relat_1(X0)
% 2.76/1.02      | k1_relat_1(X0) = X1 ),
% 2.76/1.02      inference(cnf_transformation,[],[f70]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_403,plain,
% 2.76/1.02      ( ~ v1_partfun1(X0,X1)
% 2.76/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.76/1.02      | ~ v1_relat_1(X0)
% 2.76/1.02      | k1_relat_1(X0) = X1 ),
% 2.76/1.02      inference(resolution,[status(thm)],[c_10,c_16]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_9,plain,
% 2.76/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.76/1.02      | v1_relat_1(X0) ),
% 2.76/1.02      inference(cnf_transformation,[],[f64]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_407,plain,
% 2.76/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.76/1.02      | ~ v1_partfun1(X0,X1)
% 2.76/1.02      | k1_relat_1(X0) = X1 ),
% 2.76/1.02      inference(global_propositional_subsumption,
% 2.76/1.02                [status(thm)],
% 2.76/1.02                [c_403,c_16,c_10,c_9]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_408,plain,
% 2.76/1.02      ( ~ v1_partfun1(X0,X1)
% 2.76/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.76/1.02      | k1_relat_1(X0) = X1 ),
% 2.76/1.02      inference(renaming,[status(thm)],[c_407]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_534,plain,
% 2.76/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.76/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.76/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.76/1.02      | ~ v1_funct_1(X0)
% 2.76/1.02      | k1_relat_1(X0) = X1
% 2.76/1.02      | k1_xboole_0 = X2 ),
% 2.76/1.02      inference(resolution,[status(thm)],[c_18,c_408]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_538,plain,
% 2.76/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.76/1.02      | ~ v1_funct_2(X0,X1,X2)
% 2.76/1.02      | ~ v1_funct_1(X0)
% 2.76/1.02      | k1_relat_1(X0) = X1
% 2.76/1.02      | k1_xboole_0 = X2 ),
% 2.76/1.02      inference(global_propositional_subsumption,
% 2.76/1.02                [status(thm)],
% 2.76/1.02                [c_534,c_18,c_408]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_539,plain,
% 2.76/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.76/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.76/1.02      | ~ v1_funct_1(X0)
% 2.76/1.02      | k1_relat_1(X0) = X1
% 2.76/1.02      | k1_xboole_0 = X2 ),
% 2.76/1.02      inference(renaming,[status(thm)],[c_538]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_29,negated_conjecture,
% 2.76/1.02      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.76/1.02      inference(cnf_transformation,[],[f84]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_621,plain,
% 2.76/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.76/1.02      | ~ v1_funct_1(X0)
% 2.76/1.02      | u1_struct_0(sK0) != X1
% 2.76/1.02      | u1_struct_0(sK1) != X2
% 2.76/1.02      | k1_relat_1(X0) = X1
% 2.76/1.02      | sK2 != X0
% 2.76/1.02      | k1_xboole_0 = X2 ),
% 2.76/1.02      inference(resolution_lifted,[status(thm)],[c_539,c_29]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_622,plain,
% 2.76/1.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.76/1.02      | ~ v1_funct_1(sK2)
% 2.76/1.02      | k1_relat_1(sK2) = u1_struct_0(sK0)
% 2.76/1.02      | k1_xboole_0 = u1_struct_0(sK1) ),
% 2.76/1.02      inference(unflattening,[status(thm)],[c_621]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_30,negated_conjecture,
% 2.76/1.02      ( v1_funct_1(sK2) ),
% 2.76/1.02      inference(cnf_transformation,[],[f83]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_28,negated_conjecture,
% 2.76/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.76/1.02      inference(cnf_transformation,[],[f85]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_624,plain,
% 2.76/1.02      ( k1_relat_1(sK2) = u1_struct_0(sK0)
% 2.76/1.02      | k1_xboole_0 = u1_struct_0(sK1) ),
% 2.76/1.02      inference(global_propositional_subsumption,
% 2.76/1.02                [status(thm)],
% 2.76/1.02                [c_622,c_30,c_28]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_815,plain,
% 2.76/1.02      ( k1_relat_1(sK2) = u1_struct_0(sK0)
% 2.76/1.02      | k1_xboole_0 = u1_struct_0(sK1) ),
% 2.76/1.02      inference(subtyping,[status(esa)],[c_624]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_22,plain,
% 2.76/1.02      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.76/1.02      inference(cnf_transformation,[],[f77]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_33,negated_conjecture,
% 2.76/1.02      ( l1_struct_0(sK0) ),
% 2.76/1.02      inference(cnf_transformation,[],[f80]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_396,plain,
% 2.76/1.02      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.76/1.02      inference(resolution_lifted,[status(thm)],[c_22,c_33]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_397,plain,
% 2.76/1.02      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.76/1.02      inference(unflattening,[status(thm)],[c_396]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_820,plain,
% 2.76/1.02      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.76/1.02      inference(subtyping,[status(esa)],[c_397]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_31,negated_conjecture,
% 2.76/1.02      ( l1_struct_0(sK1) ),
% 2.76/1.02      inference(cnf_transformation,[],[f82]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_391,plain,
% 2.76/1.02      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.76/1.02      inference(resolution_lifted,[status(thm)],[c_22,c_31]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_392,plain,
% 2.76/1.02      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.76/1.02      inference(unflattening,[status(thm)],[c_391]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_821,plain,
% 2.76/1.02      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.76/1.02      inference(subtyping,[status(esa)],[c_392]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_1275,plain,
% 2.76/1.02      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.76/1.02      | k2_struct_0(sK1) = k1_xboole_0 ),
% 2.76/1.02      inference(demodulation,[status(thm)],[c_815,c_820,c_821]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_0,plain,
% 2.76/1.02      ( v1_xboole_0(k1_xboole_0) ),
% 2.76/1.02      inference(cnf_transformation,[],[f55]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_23,plain,
% 2.76/1.02      ( v2_struct_0(X0)
% 2.76/1.02      | ~ l1_struct_0(X0)
% 2.76/1.02      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.76/1.02      inference(cnf_transformation,[],[f78]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_364,plain,
% 2.76/1.02      ( v2_struct_0(X0)
% 2.76/1.02      | ~ l1_struct_0(X0)
% 2.76/1.02      | u1_struct_0(X0) != k1_xboole_0 ),
% 2.76/1.02      inference(resolution_lifted,[status(thm)],[c_0,c_23]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_32,negated_conjecture,
% 2.76/1.02      ( ~ v2_struct_0(sK1) ),
% 2.76/1.02      inference(cnf_transformation,[],[f81]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_382,plain,
% 2.76/1.02      ( ~ l1_struct_0(X0) | u1_struct_0(X0) != k1_xboole_0 | sK1 != X0 ),
% 2.76/1.02      inference(resolution_lifted,[status(thm)],[c_364,c_32]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_383,plain,
% 2.76/1.02      ( ~ l1_struct_0(sK1) | u1_struct_0(sK1) != k1_xboole_0 ),
% 2.76/1.02      inference(unflattening,[status(thm)],[c_382]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_366,plain,
% 2.76/1.02      ( v2_struct_0(sK1)
% 2.76/1.02      | ~ l1_struct_0(sK1)
% 2.76/1.02      | u1_struct_0(sK1) != k1_xboole_0 ),
% 2.76/1.02      inference(instantiation,[status(thm)],[c_364]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_385,plain,
% 2.76/1.02      ( u1_struct_0(sK1) != k1_xboole_0 ),
% 2.76/1.02      inference(global_propositional_subsumption,
% 2.76/1.02                [status(thm)],
% 2.76/1.02                [c_383,c_32,c_31,c_366]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_822,plain,
% 2.76/1.02      ( u1_struct_0(sK1) != k1_xboole_0 ),
% 2.76/1.02      inference(subtyping,[status(esa)],[c_385]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_1263,plain,
% 2.76/1.02      ( k2_struct_0(sK1) != k1_xboole_0 ),
% 2.76/1.02      inference(demodulation,[status(thm)],[c_821,c_822]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_1278,plain,
% 2.76/1.02      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.76/1.02      inference(forward_subsumption_resolution,
% 2.76/1.02                [status(thm)],
% 2.76/1.02                [c_1275,c_1263]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_824,negated_conjecture,
% 2.76/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.76/1.02      inference(subtyping,[status(esa)],[c_28]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_1250,plain,
% 2.76/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.76/1.02      inference(predicate_to_equality,[status(thm)],[c_824]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_1272,plain,
% 2.76/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.76/1.02      inference(light_normalisation,[status(thm)],[c_1250,c_820,c_821]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_1279,plain,
% 2.76/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) = iProver_top ),
% 2.76/1.02      inference(demodulation,[status(thm)],[c_1278,c_1272]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_832,plain,
% 2.76/1.02      ( ~ m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(X0_59,X1_59)))
% 2.76/1.02      | v1_relat_1(X0_58) ),
% 2.76/1.02      inference(subtyping,[status(esa)],[c_9]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_1244,plain,
% 2.76/1.02      ( m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(X0_59,X1_59))) != iProver_top
% 2.76/1.02      | v1_relat_1(X0_58) = iProver_top ),
% 2.76/1.02      inference(predicate_to_equality,[status(thm)],[c_832]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_1612,plain,
% 2.76/1.02      ( v1_relat_1(sK2) = iProver_top ),
% 2.76/1.02      inference(superposition,[status(thm)],[c_1279,c_1244]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_4,plain,
% 2.76/1.02      ( ~ v1_relat_1(X0) | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
% 2.76/1.02      inference(cnf_transformation,[],[f58]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_835,plain,
% 2.76/1.02      ( ~ v1_relat_1(X0_58)
% 2.76/1.02      | k1_relat_1(k4_relat_1(X0_58)) = k2_relat_1(X0_58) ),
% 2.76/1.02      inference(subtyping,[status(esa)],[c_4]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_1241,plain,
% 2.76/1.02      ( k1_relat_1(k4_relat_1(X0_58)) = k2_relat_1(X0_58)
% 2.76/1.02      | v1_relat_1(X0_58) != iProver_top ),
% 2.76/1.02      inference(predicate_to_equality,[status(thm)],[c_835]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_1649,plain,
% 2.76/1.02      ( k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2) ),
% 2.76/1.02      inference(superposition,[status(thm)],[c_1612,c_1241]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_19,plain,
% 2.76/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 2.76/1.02      | ~ v1_funct_1(X0)
% 2.76/1.02      | ~ v1_relat_1(X0) ),
% 2.76/1.02      inference(cnf_transformation,[],[f76]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_827,plain,
% 2.76/1.02      ( m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_58),k2_relat_1(X0_58))))
% 2.76/1.02      | ~ v1_funct_1(X0_58)
% 2.76/1.02      | ~ v1_relat_1(X0_58) ),
% 2.76/1.02      inference(subtyping,[status(esa)],[c_19]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_1249,plain,
% 2.76/1.02      ( m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_58),k2_relat_1(X0_58)))) = iProver_top
% 2.76/1.02      | v1_funct_1(X0_58) != iProver_top
% 2.76/1.02      | v1_relat_1(X0_58) != iProver_top ),
% 2.76/1.02      inference(predicate_to_equality,[status(thm)],[c_827]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_2116,plain,
% 2.76/1.02      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k4_relat_1(sK2))))) = iProver_top
% 2.76/1.02      | v1_funct_1(k4_relat_1(sK2)) != iProver_top
% 2.76/1.02      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 2.76/1.02      inference(superposition,[status(thm)],[c_1649,c_1249]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_37,plain,
% 2.76/1.02      ( v1_funct_1(sK2) = iProver_top ),
% 2.76/1.02      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_39,plain,
% 2.76/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.76/1.02      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_1415,plain,
% 2.76/1.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.76/1.02      | v1_relat_1(sK2) ),
% 2.76/1.02      inference(instantiation,[status(thm)],[c_832]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_1416,plain,
% 2.76/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.76/1.02      | v1_relat_1(sK2) = iProver_top ),
% 2.76/1.02      inference(predicate_to_equality,[status(thm)],[c_1415]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_5,plain,
% 2.76/1.02      ( ~ v1_funct_1(X0)
% 2.76/1.02      | ~ v2_funct_1(X0)
% 2.76/1.02      | ~ v1_relat_1(X0)
% 2.76/1.02      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 2.76/1.02      inference(cnf_transformation,[],[f60]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_26,negated_conjecture,
% 2.76/1.02      ( v2_funct_1(sK2) ),
% 2.76/1.02      inference(cnf_transformation,[],[f87]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_509,plain,
% 2.76/1.02      ( ~ v1_funct_1(X0)
% 2.76/1.02      | ~ v1_relat_1(X0)
% 2.76/1.02      | k2_funct_1(X0) = k4_relat_1(X0)
% 2.76/1.02      | sK2 != X0 ),
% 2.76/1.02      inference(resolution_lifted,[status(thm)],[c_5,c_26]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_510,plain,
% 2.76/1.02      ( ~ v1_funct_1(sK2)
% 2.76/1.02      | ~ v1_relat_1(sK2)
% 2.76/1.02      | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 2.76/1.02      inference(unflattening,[status(thm)],[c_509]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_512,plain,
% 2.76/1.02      ( ~ v1_relat_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 2.76/1.02      inference(global_propositional_subsumption,
% 2.76/1.02                [status(thm)],
% 2.76/1.02                [c_510,c_30]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_817,plain,
% 2.76/1.02      ( ~ v1_relat_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 2.76/1.02      inference(subtyping,[status(esa)],[c_512]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_1254,plain,
% 2.76/1.02      ( k2_funct_1(sK2) = k4_relat_1(sK2)
% 2.76/1.02      | v1_relat_1(sK2) != iProver_top ),
% 2.76/1.02      inference(predicate_to_equality,[status(thm)],[c_817]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_1436,plain,
% 2.76/1.02      ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 2.76/1.02      inference(global_propositional_subsumption,
% 2.76/1.02                [status(thm)],
% 2.76/1.02                [c_1254,c_28,c_817,c_1415]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_6,plain,
% 2.76/1.02      ( ~ v1_funct_1(X0)
% 2.76/1.02      | v1_funct_1(k2_funct_1(X0))
% 2.76/1.02      | ~ v1_relat_1(X0) ),
% 2.76/1.02      inference(cnf_transformation,[],[f62]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_834,plain,
% 2.76/1.02      ( ~ v1_funct_1(X0_58)
% 2.76/1.02      | v1_funct_1(k2_funct_1(X0_58))
% 2.76/1.02      | ~ v1_relat_1(X0_58) ),
% 2.76/1.02      inference(subtyping,[status(esa)],[c_6]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_1242,plain,
% 2.76/1.02      ( v1_funct_1(X0_58) != iProver_top
% 2.76/1.02      | v1_funct_1(k2_funct_1(X0_58)) = iProver_top
% 2.76/1.02      | v1_relat_1(X0_58) != iProver_top ),
% 2.76/1.02      inference(predicate_to_equality,[status(thm)],[c_834]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_1462,plain,
% 2.76/1.02      ( v1_funct_1(k4_relat_1(sK2)) = iProver_top
% 2.76/1.02      | v1_funct_1(sK2) != iProver_top
% 2.76/1.02      | v1_relat_1(sK2) != iProver_top ),
% 2.76/1.02      inference(superposition,[status(thm)],[c_1436,c_1242]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_7,plain,
% 2.76/1.02      ( ~ v1_funct_1(X0)
% 2.76/1.02      | ~ v1_relat_1(X0)
% 2.76/1.02      | v1_relat_1(k2_funct_1(X0)) ),
% 2.76/1.02      inference(cnf_transformation,[],[f61]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_833,plain,
% 2.76/1.02      ( ~ v1_funct_1(X0_58)
% 2.76/1.02      | ~ v1_relat_1(X0_58)
% 2.76/1.02      | v1_relat_1(k2_funct_1(X0_58)) ),
% 2.76/1.02      inference(subtyping,[status(esa)],[c_7]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_1243,plain,
% 2.76/1.02      ( v1_funct_1(X0_58) != iProver_top
% 2.76/1.02      | v1_relat_1(X0_58) != iProver_top
% 2.76/1.02      | v1_relat_1(k2_funct_1(X0_58)) = iProver_top ),
% 2.76/1.02      inference(predicate_to_equality,[status(thm)],[c_833]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_1692,plain,
% 2.76/1.02      ( v1_funct_1(sK2) != iProver_top
% 2.76/1.02      | v1_relat_1(k4_relat_1(sK2)) = iProver_top
% 2.76/1.02      | v1_relat_1(sK2) != iProver_top ),
% 2.76/1.02      inference(superposition,[status(thm)],[c_1436,c_1243]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_3303,plain,
% 2.76/1.02      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k4_relat_1(sK2))))) = iProver_top ),
% 2.76/1.02      inference(global_propositional_subsumption,
% 2.76/1.02                [status(thm)],
% 2.76/1.02                [c_2116,c_37,c_39,c_1416,c_1462,c_1692]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_3,plain,
% 2.76/1.02      ( ~ v1_relat_1(X0) | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
% 2.76/1.02      inference(cnf_transformation,[],[f59]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_836,plain,
% 2.76/1.02      ( ~ v1_relat_1(X0_58)
% 2.76/1.02      | k2_relat_1(k4_relat_1(X0_58)) = k1_relat_1(X0_58) ),
% 2.76/1.02      inference(subtyping,[status(esa)],[c_3]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_1240,plain,
% 2.76/1.02      ( k2_relat_1(k4_relat_1(X0_58)) = k1_relat_1(X0_58)
% 2.76/1.02      | v1_relat_1(X0_58) != iProver_top ),
% 2.76/1.02      inference(predicate_to_equality,[status(thm)],[c_836]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_1650,plain,
% 2.76/1.02      ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
% 2.76/1.02      inference(superposition,[status(thm)],[c_1612,c_1240]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_3307,plain,
% 2.76/1.02      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
% 2.76/1.02      inference(light_normalisation,[status(thm)],[c_3303,c_1650]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_13,plain,
% 2.76/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.76/1.02      | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
% 2.76/1.02      inference(cnf_transformation,[],[f69]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_829,plain,
% 2.76/1.02      ( ~ m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(X0_59,X1_59)))
% 2.76/1.02      | k8_relset_1(X0_59,X1_59,X0_58,X1_59) = k1_relset_1(X0_59,X1_59,X0_58) ),
% 2.76/1.02      inference(subtyping,[status(esa)],[c_13]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_1247,plain,
% 2.76/1.02      ( k8_relset_1(X0_59,X1_59,X0_58,X1_59) = k1_relset_1(X0_59,X1_59,X0_58)
% 2.76/1.02      | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(X0_59,X1_59))) != iProver_top ),
% 2.76/1.02      inference(predicate_to_equality,[status(thm)],[c_829]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_3312,plain,
% 2.76/1.02      ( k8_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2),k1_relat_1(sK2)) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) ),
% 2.76/1.02      inference(superposition,[status(thm)],[c_3307,c_1247]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_12,plain,
% 2.76/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.76/1.02      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 2.76/1.02      inference(cnf_transformation,[],[f67]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_830,plain,
% 2.76/1.02      ( ~ m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(X0_59,X1_59)))
% 2.76/1.02      | k8_relset_1(X0_59,X1_59,X0_58,X2_59) = k10_relat_1(X0_58,X2_59) ),
% 2.76/1.02      inference(subtyping,[status(esa)],[c_12]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_1246,plain,
% 2.76/1.02      ( k8_relset_1(X0_59,X1_59,X0_58,X2_59) = k10_relat_1(X0_58,X2_59)
% 2.76/1.02      | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(X0_59,X1_59))) != iProver_top ),
% 2.76/1.02      inference(predicate_to_equality,[status(thm)],[c_830]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_3313,plain,
% 2.76/1.02      ( k8_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2),X0_59) = k10_relat_1(k4_relat_1(sK2),X0_59) ),
% 2.76/1.02      inference(superposition,[status(thm)],[c_3307,c_1246]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_8,plain,
% 2.76/1.02      ( ~ v1_funct_1(X0)
% 2.76/1.02      | ~ v2_funct_1(X0)
% 2.76/1.02      | ~ v1_relat_1(X0)
% 2.76/1.02      | k10_relat_1(k2_funct_1(X0),X1) = k9_relat_1(X0,X1) ),
% 2.76/1.02      inference(cnf_transformation,[],[f63]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_491,plain,
% 2.76/1.02      ( ~ v1_funct_1(X0)
% 2.76/1.02      | ~ v1_relat_1(X0)
% 2.76/1.02      | k10_relat_1(k2_funct_1(X0),X1) = k9_relat_1(X0,X1)
% 2.76/1.02      | sK2 != X0 ),
% 2.76/1.02      inference(resolution_lifted,[status(thm)],[c_8,c_26]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_492,plain,
% 2.76/1.02      ( ~ v1_funct_1(sK2)
% 2.76/1.02      | ~ v1_relat_1(sK2)
% 2.76/1.02      | k10_relat_1(k2_funct_1(sK2),X0) = k9_relat_1(sK2,X0) ),
% 2.76/1.02      inference(unflattening,[status(thm)],[c_491]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_496,plain,
% 2.76/1.02      ( ~ v1_relat_1(sK2)
% 2.76/1.02      | k10_relat_1(k2_funct_1(sK2),X0) = k9_relat_1(sK2,X0) ),
% 2.76/1.02      inference(global_propositional_subsumption,
% 2.76/1.02                [status(thm)],
% 2.76/1.02                [c_492,c_30]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_818,plain,
% 2.76/1.02      ( ~ v1_relat_1(sK2)
% 2.76/1.02      | k10_relat_1(k2_funct_1(sK2),X0_59) = k9_relat_1(sK2,X0_59) ),
% 2.76/1.02      inference(subtyping,[status(esa)],[c_496]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_1253,plain,
% 2.76/1.02      ( k10_relat_1(k2_funct_1(sK2),X0_59) = k9_relat_1(sK2,X0_59)
% 2.76/1.02      | v1_relat_1(sK2) != iProver_top ),
% 2.76/1.02      inference(predicate_to_equality,[status(thm)],[c_818]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_1441,plain,
% 2.76/1.02      ( k10_relat_1(k2_funct_1(sK2),X0_59) = k9_relat_1(sK2,X0_59) ),
% 2.76/1.02      inference(global_propositional_subsumption,
% 2.76/1.02                [status(thm)],
% 2.76/1.02                [c_1253,c_28,c_818,c_1415]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_1444,plain,
% 2.76/1.02      ( k10_relat_1(k4_relat_1(sK2),X0_59) = k9_relat_1(sK2,X0_59) ),
% 2.76/1.02      inference(light_normalisation,[status(thm)],[c_1441,c_1436]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_3320,plain,
% 2.76/1.02      ( k8_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2),X0_59) = k9_relat_1(sK2,X0_59) ),
% 2.76/1.02      inference(light_normalisation,[status(thm)],[c_3313,c_1444]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_3322,plain,
% 2.76/1.02      ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = k9_relat_1(sK2,k1_relat_1(sK2)) ),
% 2.76/1.02      inference(demodulation,[status(thm)],[c_3312,c_3320]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_11,plain,
% 2.76/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.76/1.02      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.76/1.02      inference(cnf_transformation,[],[f66]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_831,plain,
% 2.76/1.02      ( ~ m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(X0_59,X1_59)))
% 2.76/1.02      | k2_relset_1(X0_59,X1_59,X0_58) = k2_relat_1(X0_58) ),
% 2.76/1.02      inference(subtyping,[status(esa)],[c_11]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_1245,plain,
% 2.76/1.02      ( k2_relset_1(X0_59,X1_59,X0_58) = k2_relat_1(X0_58)
% 2.76/1.02      | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(X0_59,X1_59))) != iProver_top ),
% 2.76/1.02      inference(predicate_to_equality,[status(thm)],[c_831]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_1764,plain,
% 2.76/1.02      ( k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 2.76/1.02      inference(superposition,[status(thm)],[c_1279,c_1245]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_27,negated_conjecture,
% 2.76/1.02      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.76/1.02      inference(cnf_transformation,[],[f86]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_825,negated_conjecture,
% 2.76/1.02      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.76/1.02      inference(subtyping,[status(esa)],[c_27]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_1269,plain,
% 2.76/1.02      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.76/1.02      inference(light_normalisation,[status(thm)],[c_825,c_820,c_821]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_1280,plain,
% 2.76/1.02      ( k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.76/1.02      inference(demodulation,[status(thm)],[c_1278,c_1269]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_1954,plain,
% 2.76/1.02      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 2.76/1.02      inference(demodulation,[status(thm)],[c_1764,c_1280]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_25,negated_conjecture,
% 2.76/1.02      ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 2.76/1.02      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
% 2.76/1.02      inference(cnf_transformation,[],[f88]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_826,negated_conjecture,
% 2.76/1.02      ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 2.76/1.02      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
% 2.76/1.02      inference(subtyping,[status(esa)],[c_25]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_1281,plain,
% 2.76/1.02      ( u1_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.76/1.02      inference(demodulation,[status(thm)],[c_1278,c_820]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_24,plain,
% 2.76/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.76/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.76/1.02      | ~ v1_funct_1(X0)
% 2.76/1.02      | ~ v2_funct_1(X0)
% 2.76/1.02      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.76/1.02      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.76/1.02      inference(cnf_transformation,[],[f79]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_467,plain,
% 2.76/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.76/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.76/1.02      | ~ v1_funct_1(X0)
% 2.76/1.02      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.76/1.02      | k2_relset_1(X1,X2,X0) != X2
% 2.76/1.02      | sK2 != X0 ),
% 2.76/1.02      inference(resolution_lifted,[status(thm)],[c_24,c_26]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_468,plain,
% 2.76/1.02      ( ~ v1_funct_2(sK2,X0,X1)
% 2.76/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.76/1.02      | ~ v1_funct_1(sK2)
% 2.76/1.02      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.76/1.02      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.76/1.02      inference(unflattening,[status(thm)],[c_467]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_472,plain,
% 2.76/1.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.76/1.02      | ~ v1_funct_2(sK2,X0,X1)
% 2.76/1.02      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.76/1.02      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.76/1.02      inference(global_propositional_subsumption,
% 2.76/1.02                [status(thm)],
% 2.76/1.02                [c_468,c_30]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_473,plain,
% 2.76/1.02      ( ~ v1_funct_2(sK2,X0,X1)
% 2.76/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.76/1.02      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.76/1.02      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.76/1.02      inference(renaming,[status(thm)],[c_472]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_651,plain,
% 2.76/1.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.76/1.02      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.76/1.02      | k2_relset_1(X0,X1,sK2) != X1
% 2.76/1.02      | u1_struct_0(sK0) != X0
% 2.76/1.02      | u1_struct_0(sK1) != X1
% 2.76/1.02      | sK2 != sK2 ),
% 2.76/1.02      inference(resolution_lifted,[status(thm)],[c_29,c_473]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_652,plain,
% 2.76/1.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.76/1.02      | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 2.76/1.02      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
% 2.76/1.02      inference(unflattening,[status(thm)],[c_651]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_654,plain,
% 2.76/1.02      ( k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 2.76/1.02      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
% 2.76/1.02      inference(global_propositional_subsumption,
% 2.76/1.02                [status(thm)],
% 2.76/1.02                [c_652,c_28]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_813,plain,
% 2.76/1.02      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
% 2.76/1.02      | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 2.76/1.02      inference(subtyping,[status(esa)],[c_654]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_1349,plain,
% 2.76/1.02      ( k2_struct_0(sK1) != k2_struct_0(sK1)
% 2.76/1.02      | k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 2.76/1.02      inference(light_normalisation,
% 2.76/1.02                [status(thm)],
% 2.76/1.02                [c_813,c_821,c_1280,c_1281]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_1350,plain,
% 2.76/1.02      ( k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 2.76/1.02      inference(equality_resolution_simp,[status(thm)],[c_1349]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_1364,plain,
% 2.76/1.02      ( k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) != k2_struct_0(sK1)
% 2.76/1.02      | k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2) ),
% 2.76/1.02      inference(light_normalisation,
% 2.76/1.02                [status(thm)],
% 2.76/1.02                [c_826,c_821,c_1278,c_1281,c_1350]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_1439,plain,
% 2.76/1.02      ( k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k4_relat_1(sK2)) != k2_struct_0(sK1)
% 2.76/1.02      | k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k4_relat_1(sK2)) != k1_relat_1(sK2) ),
% 2.76/1.02      inference(demodulation,[status(thm)],[c_1436,c_1364]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_1960,plain,
% 2.76/1.02      ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) != k2_relat_1(sK2)
% 2.76/1.02      | k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) != k1_relat_1(sK2) ),
% 2.76/1.02      inference(demodulation,[status(thm)],[c_1954,c_1439]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_3582,plain,
% 2.76/1.02      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) != k1_relat_1(sK2)
% 2.76/1.02      | k9_relat_1(sK2,k1_relat_1(sK2)) != k2_relat_1(sK2) ),
% 2.76/1.02      inference(demodulation,[status(thm)],[c_3322,c_1960]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_1641,plain,
% 2.76/1.02      ( v1_funct_1(k4_relat_1(sK2)) = iProver_top ),
% 2.76/1.02      inference(global_propositional_subsumption,
% 2.76/1.02                [status(thm)],
% 2.76/1.02                [c_1462,c_37,c_39,c_1416]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_2066,plain,
% 2.76/1.02      ( k2_relset_1(k1_relat_1(X0_58),k2_relat_1(X0_58),X0_58) = k2_relat_1(X0_58)
% 2.76/1.02      | v1_funct_1(X0_58) != iProver_top
% 2.76/1.02      | v1_relat_1(X0_58) != iProver_top ),
% 2.76/1.02      inference(superposition,[status(thm)],[c_1249,c_1245]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_3215,plain,
% 2.76/1.02      ( k2_relset_1(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2)),k4_relat_1(sK2)) = k2_relat_1(k4_relat_1(sK2))
% 2.76/1.02      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 2.76/1.02      inference(superposition,[status(thm)],[c_1641,c_2066]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_3218,plain,
% 2.76/1.02      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = k1_relat_1(sK2)
% 2.76/1.02      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 2.76/1.02      inference(light_normalisation,[status(thm)],[c_3215,c_1649,c_1650]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_1958,plain,
% 2.76/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
% 2.76/1.02      inference(demodulation,[status(thm)],[c_1954,c_1279]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_2,plain,
% 2.76/1.02      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.76/1.02      inference(cnf_transformation,[],[f57]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_423,plain,
% 2.76/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.76/1.02      | ~ v1_relat_1(X0)
% 2.76/1.02      | k7_relat_1(X0,X1) = X0 ),
% 2.76/1.02      inference(resolution,[status(thm)],[c_10,c_2]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_427,plain,
% 2.76/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.76/1.02      | k7_relat_1(X0,X1) = X0 ),
% 2.76/1.02      inference(global_propositional_subsumption,
% 2.76/1.02                [status(thm)],
% 2.76/1.02                [c_423,c_10,c_9,c_2]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_819,plain,
% 2.76/1.02      ( ~ m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(X0_59,X1_59)))
% 2.76/1.02      | k7_relat_1(X0_58,X0_59) = X0_58 ),
% 2.76/1.02      inference(subtyping,[status(esa)],[c_427]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_1252,plain,
% 2.76/1.02      ( k7_relat_1(X0_58,X0_59) = X0_58
% 2.76/1.02      | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(X0_59,X1_59))) != iProver_top ),
% 2.76/1.02      inference(predicate_to_equality,[status(thm)],[c_819]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_2440,plain,
% 2.76/1.02      ( k7_relat_1(sK2,k1_relat_1(sK2)) = sK2 ),
% 2.76/1.02      inference(superposition,[status(thm)],[c_1958,c_1252]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_1,plain,
% 2.76/1.02      ( ~ v1_relat_1(X0)
% 2.76/1.02      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 2.76/1.02      inference(cnf_transformation,[],[f56]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_837,plain,
% 2.76/1.02      ( ~ v1_relat_1(X0_58)
% 2.76/1.02      | k2_relat_1(k7_relat_1(X0_58,X0_59)) = k9_relat_1(X0_58,X0_59) ),
% 2.76/1.02      inference(subtyping,[status(esa)],[c_1]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_1239,plain,
% 2.76/1.02      ( k2_relat_1(k7_relat_1(X0_58,X0_59)) = k9_relat_1(X0_58,X0_59)
% 2.76/1.02      | v1_relat_1(X0_58) != iProver_top ),
% 2.76/1.02      inference(predicate_to_equality,[status(thm)],[c_837]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_1648,plain,
% 2.76/1.02      ( k2_relat_1(k7_relat_1(sK2,X0_59)) = k9_relat_1(sK2,X0_59) ),
% 2.76/1.02      inference(superposition,[status(thm)],[c_1612,c_1239]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(c_2928,plain,
% 2.76/1.02      ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
% 2.76/1.02      inference(superposition,[status(thm)],[c_2440,c_1648]) ).
% 2.76/1.02  
% 2.76/1.02  cnf(contradiction,plain,
% 2.76/1.02      ( $false ),
% 2.76/1.02      inference(minisat,
% 2.76/1.02                [status(thm)],
% 2.76/1.02                [c_3582,c_3218,c_2928,c_1692,c_1416,c_39,c_37]) ).
% 2.76/1.02  
% 2.76/1.02  
% 2.76/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.76/1.02  
% 2.76/1.02  ------                               Statistics
% 2.76/1.02  
% 2.76/1.02  ------ General
% 2.76/1.02  
% 2.76/1.02  abstr_ref_over_cycles:                  0
% 2.76/1.02  abstr_ref_under_cycles:                 0
% 2.76/1.02  gc_basic_clause_elim:                   0
% 2.76/1.02  forced_gc_time:                         0
% 2.76/1.02  parsing_time:                           0.012
% 2.76/1.02  unif_index_cands_time:                  0.
% 2.76/1.02  unif_index_add_time:                    0.
% 2.76/1.02  orderings_time:                         0.
% 2.76/1.02  out_proof_time:                         0.023
% 2.76/1.02  total_time:                             0.147
% 2.76/1.02  num_of_symbols:                         64
% 2.76/1.02  num_of_terms:                           3092
% 2.76/1.02  
% 2.76/1.02  ------ Preprocessing
% 2.76/1.02  
% 2.76/1.02  num_of_splits:                          1
% 2.76/1.02  num_of_split_atoms:                     1
% 2.76/1.02  num_of_reused_defs:                     0
% 2.76/1.02  num_eq_ax_congr_red:                    43
% 2.76/1.02  num_of_sem_filtered_clauses:            1
% 2.76/1.02  num_of_subtypes:                        5
% 2.76/1.02  monotx_restored_types:                  1
% 2.76/1.02  sat_num_of_epr_types:                   0
% 2.76/1.02  sat_num_of_non_cyclic_types:            0
% 2.76/1.02  sat_guarded_non_collapsed_types:        0
% 2.76/1.02  num_pure_diseq_elim:                    0
% 2.76/1.02  simp_replaced_by:                       0
% 2.76/1.02  res_preprocessed:                       151
% 2.76/1.02  prep_upred:                             0
% 2.76/1.02  prep_unflattend:                        27
% 2.76/1.02  smt_new_axioms:                         0
% 2.76/1.02  pred_elim_cands:                        3
% 2.76/1.02  pred_elim:                              7
% 2.76/1.02  pred_elim_cl:                           8
% 2.76/1.02  pred_elim_cycles:                       9
% 2.76/1.02  merged_defs:                            0
% 2.76/1.02  merged_defs_ncl:                        0
% 2.76/1.02  bin_hyper_res:                          0
% 2.76/1.02  prep_cycles:                            4
% 2.76/1.02  pred_elim_time:                         0.008
% 2.76/1.02  splitting_time:                         0.
% 2.76/1.02  sem_filter_time:                        0.
% 2.76/1.02  monotx_time:                            0.
% 2.76/1.02  subtype_inf_time:                       0.001
% 2.76/1.02  
% 2.76/1.02  ------ Problem properties
% 2.76/1.02  
% 2.76/1.02  clauses:                                26
% 2.76/1.02  conjectures:                            4
% 2.76/1.02  epr:                                    1
% 2.76/1.02  horn:                                   24
% 2.76/1.02  ground:                                 12
% 2.76/1.02  unary:                                  6
% 2.76/1.02  binary:                                 16
% 2.76/1.02  lits:                                   51
% 2.76/1.02  lits_eq:                                23
% 2.76/1.02  fd_pure:                                0
% 2.76/1.02  fd_pseudo:                              0
% 2.76/1.02  fd_cond:                                0
% 2.76/1.02  fd_pseudo_cond:                         0
% 2.76/1.02  ac_symbols:                             0
% 2.76/1.02  
% 2.76/1.02  ------ Propositional Solver
% 2.76/1.02  
% 2.76/1.02  prop_solver_calls:                      30
% 2.76/1.02  prop_fast_solver_calls:                 881
% 2.76/1.02  smt_solver_calls:                       0
% 2.76/1.02  smt_fast_solver_calls:                  0
% 2.76/1.02  prop_num_of_clauses:                    1268
% 2.76/1.02  prop_preprocess_simplified:             4733
% 2.76/1.02  prop_fo_subsumed:                       25
% 2.76/1.02  prop_solver_time:                       0.
% 2.76/1.02  smt_solver_time:                        0.
% 2.76/1.02  smt_fast_solver_time:                   0.
% 2.76/1.02  prop_fast_solver_time:                  0.
% 2.76/1.02  prop_unsat_core_time:                   0.
% 2.76/1.02  
% 2.76/1.02  ------ QBF
% 2.76/1.02  
% 2.76/1.02  qbf_q_res:                              0
% 2.76/1.02  qbf_num_tautologies:                    0
% 2.76/1.02  qbf_prep_cycles:                        0
% 2.76/1.02  
% 2.76/1.02  ------ BMC1
% 2.76/1.02  
% 2.76/1.02  bmc1_current_bound:                     -1
% 2.76/1.02  bmc1_last_solved_bound:                 -1
% 2.76/1.02  bmc1_unsat_core_size:                   -1
% 2.76/1.02  bmc1_unsat_core_parents_size:           -1
% 2.76/1.02  bmc1_merge_next_fun:                    0
% 2.76/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.76/1.02  
% 2.76/1.02  ------ Instantiation
% 2.76/1.02  
% 2.76/1.02  inst_num_of_clauses:                    504
% 2.76/1.02  inst_num_in_passive:                    89
% 2.76/1.02  inst_num_in_active:                     297
% 2.76/1.02  inst_num_in_unprocessed:                118
% 2.76/1.02  inst_num_of_loops:                      320
% 2.76/1.02  inst_num_of_learning_restarts:          0
% 2.76/1.02  inst_num_moves_active_passive:          16
% 2.76/1.02  inst_lit_activity:                      0
% 2.76/1.02  inst_lit_activity_moves:                0
% 2.76/1.02  inst_num_tautologies:                   0
% 2.76/1.02  inst_num_prop_implied:                  0
% 2.76/1.02  inst_num_existing_simplified:           0
% 2.76/1.02  inst_num_eq_res_simplified:             0
% 2.76/1.02  inst_num_child_elim:                    0
% 2.76/1.02  inst_num_of_dismatching_blockings:      83
% 2.76/1.02  inst_num_of_non_proper_insts:           505
% 2.76/1.02  inst_num_of_duplicates:                 0
% 2.76/1.02  inst_inst_num_from_inst_to_res:         0
% 2.76/1.02  inst_dismatching_checking_time:         0.
% 2.76/1.02  
% 2.76/1.02  ------ Resolution
% 2.76/1.02  
% 2.76/1.02  res_num_of_clauses:                     0
% 2.76/1.02  res_num_in_passive:                     0
% 2.76/1.02  res_num_in_active:                      0
% 2.76/1.02  res_num_of_loops:                       155
% 2.76/1.02  res_forward_subset_subsumed:            78
% 2.76/1.02  res_backward_subset_subsumed:           6
% 2.76/1.02  res_forward_subsumed:                   0
% 2.76/1.02  res_backward_subsumed:                  0
% 2.76/1.02  res_forward_subsumption_resolution:     3
% 2.76/1.02  res_backward_subsumption_resolution:    0
% 2.76/1.02  res_clause_to_clause_subsumption:       163
% 2.76/1.02  res_orphan_elimination:                 0
% 2.76/1.02  res_tautology_del:                      68
% 2.76/1.02  res_num_eq_res_simplified:              0
% 2.76/1.02  res_num_sel_changes:                    0
% 2.76/1.02  res_moves_from_active_to_pass:          0
% 2.76/1.02  
% 2.76/1.02  ------ Superposition
% 2.76/1.02  
% 2.76/1.02  sup_time_total:                         0.
% 2.76/1.02  sup_time_generating:                    0.
% 2.76/1.02  sup_time_sim_full:                      0.
% 2.76/1.02  sup_time_sim_immed:                     0.
% 2.76/1.02  
% 2.76/1.02  sup_num_of_clauses:                     85
% 2.76/1.02  sup_num_in_active:                      51
% 2.76/1.02  sup_num_in_passive:                     34
% 2.76/1.02  sup_num_of_loops:                       63
% 2.76/1.02  sup_fw_superposition:                   33
% 2.76/1.02  sup_bw_superposition:                   49
% 2.76/1.02  sup_immediate_simplified:               28
% 2.76/1.02  sup_given_eliminated:                   0
% 2.76/1.02  comparisons_done:                       0
% 2.76/1.02  comparisons_avoided:                    0
% 2.76/1.02  
% 2.76/1.02  ------ Simplifications
% 2.76/1.02  
% 2.76/1.02  
% 2.76/1.02  sim_fw_subset_subsumed:                 3
% 2.76/1.02  sim_bw_subset_subsumed:                 3
% 2.76/1.02  sim_fw_subsumed:                        1
% 2.76/1.02  sim_bw_subsumed:                        0
% 2.76/1.02  sim_fw_subsumption_res:                 1
% 2.76/1.02  sim_bw_subsumption_res:                 0
% 2.76/1.02  sim_tautology_del:                      4
% 2.76/1.02  sim_eq_tautology_del:                   4
% 2.76/1.02  sim_eq_res_simp:                        1
% 2.76/1.02  sim_fw_demodulated:                     3
% 2.76/1.02  sim_bw_demodulated:                     16
% 2.76/1.02  sim_light_normalised:                   35
% 2.76/1.02  sim_joinable_taut:                      0
% 2.76/1.02  sim_joinable_simp:                      0
% 2.76/1.02  sim_ac_normalised:                      0
% 2.76/1.02  sim_smt_subsumption:                    0
% 2.76/1.02  
%------------------------------------------------------------------------------
