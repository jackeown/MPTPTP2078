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
% DateTime   : Thu Dec  3 12:17:11 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :  158 (1691 expanded)
%              Number of clauses        :   96 ( 447 expanded)
%              Number of leaves         :   17 ( 520 expanded)
%              Depth                    :   19
%              Number of atoms          :  521 (12579 expanded)
%              Number of equality atoms :  232 (4325 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f32,plain,(
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
    inference(flattening,[],[f32])).

fof(f36,plain,(
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

fof(f35,plain,(
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

fof(f34,plain,
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

fof(f37,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f36,f35,f34])).

fof(f62,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f37])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f54,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f59,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f57,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f63,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f37])).

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

fof(f25,plain,(
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

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f64,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f60,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f43,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f69,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f43,f48])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f61,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f58,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f66,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f40,f48])).

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
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f42,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f65,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f41,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1148,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_15,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_24,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_295,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_24])).

cnf(c_296,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_295])).

cnf(c_26,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_300,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_26])).

cnf(c_301,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_300])).

cnf(c_1169,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1148,c_296,c_301])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1149,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1485,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1169,c_1149])).

cnf(c_20,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1166,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_20,c_296,c_301])).

cnf(c_1981,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1485,c_1166])).

cnf(c_1987,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1981,c_1485])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_19,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_415,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_19])).

cnf(c_416,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_415])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_420,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_416,c_23])).

cnf(c_421,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_420])).

cnf(c_1145,plain,
    ( k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_421])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_541,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_19])).

cnf(c_542,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(unflattening,[status(thm)],[c_541])).

cnf(c_544,plain,
    ( ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_542,c_23])).

cnf(c_1141,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_544])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1297,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1559,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1141,c_23,c_21,c_542,c_1297])).

cnf(c_2234,plain,
    ( k2_relset_1(X0,X1,sK2) != X1
    | k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1145,c_1559])).

cnf(c_2398,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | k6_partfun1(k2_struct_0(sK0)) = k6_partfun1(k1_relat_1(sK2))
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1987,c_2234])).

cnf(c_1991,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1981,c_1169])).

cnf(c_22,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1147,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1163,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1147,c_296,c_301])).

cnf(c_1992,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1981,c_1163])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_16,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_268,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_16])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_286,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_268,c_25])).

cnf(c_287,plain,
    ( ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_286])).

cnf(c_270,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_268])).

cnf(c_289,plain,
    ( u1_struct_0(sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_287,c_25,c_24,c_270])).

cnf(c_1156,plain,
    ( k2_struct_0(sK1) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_289,c_296])).

cnf(c_1993,plain,
    ( k2_relat_1(sK2) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1981,c_1156])).

cnf(c_2880,plain,
    ( k6_partfun1(k2_struct_0(sK0)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2398,c_1991,c_1992,c_1993])).

cnf(c_1,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2884,plain,
    ( k2_relat_1(k6_partfun1(k1_relat_1(sK2))) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_2880,c_1])).

cnf(c_2886,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2884,c_1])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_517,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_19])).

cnf(c_518,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_517])).

cnf(c_522,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_518,c_23])).

cnf(c_523,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_522])).

cnf(c_1142,plain,
    ( k2_relset_1(X0,X1,sK2) != X1
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_523])).

cnf(c_1788,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1166,c_1142])).

cnf(c_2104,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1788,c_1169,c_1163])).

cnf(c_2108,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2104,c_1981])).

cnf(c_2113,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_2108,c_1149])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_583,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_19])).

cnf(c_584,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_583])).

cnf(c_586,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_584,c_23])).

cnf(c_1138,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_586])).

cnf(c_1329,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1138,c_23,c_21,c_584,c_1297])).

cnf(c_2115,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_2113,c_1329])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_391,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_19])).

cnf(c_392,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_391])).

cnf(c_396,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_392,c_23])).

cnf(c_397,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_396])).

cnf(c_1146,plain,
    ( k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_397])).

cnf(c_1638,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1166,c_1146])).

cnf(c_1678,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1638,c_1169,c_1163])).

cnf(c_18,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1200,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_18,c_296,c_301])).

cnf(c_1681,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_1678,c_1200])).

cnf(c_1988,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1981,c_1681])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1150,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2112,plain,
    ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_2108,c_1150])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_569,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_19])).

cnf(c_570,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_569])).

cnf(c_572,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_570,c_23])).

cnf(c_1139,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_572])).

cnf(c_1357,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1139,c_23,c_21,c_570,c_1297])).

cnf(c_2118,plain,
    ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_2112,c_1357])).

cnf(c_2412,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1988,c_2118])).

cnf(c_2818,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2115,c_2412])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2886,c_2818])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:04:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.53/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/0.99  
% 2.53/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.53/0.99  
% 2.53/0.99  ------  iProver source info
% 2.53/0.99  
% 2.53/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.53/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.53/0.99  git: non_committed_changes: false
% 2.53/0.99  git: last_make_outside_of_git: false
% 2.53/0.99  
% 2.53/0.99  ------ 
% 2.53/0.99  
% 2.53/0.99  ------ Input Options
% 2.53/0.99  
% 2.53/0.99  --out_options                           all
% 2.53/0.99  --tptp_safe_out                         true
% 2.53/0.99  --problem_path                          ""
% 2.53/0.99  --include_path                          ""
% 2.53/0.99  --clausifier                            res/vclausify_rel
% 2.53/0.99  --clausifier_options                    --mode clausify
% 2.53/0.99  --stdin                                 false
% 2.53/0.99  --stats_out                             all
% 2.53/0.99  
% 2.53/0.99  ------ General Options
% 2.53/0.99  
% 2.53/0.99  --fof                                   false
% 2.53/0.99  --time_out_real                         305.
% 2.53/0.99  --time_out_virtual                      -1.
% 2.53/0.99  --symbol_type_check                     false
% 2.53/0.99  --clausify_out                          false
% 2.53/0.99  --sig_cnt_out                           false
% 2.53/0.99  --trig_cnt_out                          false
% 2.53/0.99  --trig_cnt_out_tolerance                1.
% 2.53/0.99  --trig_cnt_out_sk_spl                   false
% 2.53/0.99  --abstr_cl_out                          false
% 2.53/0.99  
% 2.53/0.99  ------ Global Options
% 2.53/0.99  
% 2.53/0.99  --schedule                              default
% 2.53/0.99  --add_important_lit                     false
% 2.53/0.99  --prop_solver_per_cl                    1000
% 2.53/0.99  --min_unsat_core                        false
% 2.53/0.99  --soft_assumptions                      false
% 2.53/0.99  --soft_lemma_size                       3
% 2.53/0.99  --prop_impl_unit_size                   0
% 2.53/0.99  --prop_impl_unit                        []
% 2.53/0.99  --share_sel_clauses                     true
% 2.53/0.99  --reset_solvers                         false
% 2.53/0.99  --bc_imp_inh                            [conj_cone]
% 2.53/0.99  --conj_cone_tolerance                   3.
% 2.53/0.99  --extra_neg_conj                        none
% 2.53/0.99  --large_theory_mode                     true
% 2.53/0.99  --prolific_symb_bound                   200
% 2.53/0.99  --lt_threshold                          2000
% 2.53/0.99  --clause_weak_htbl                      true
% 2.53/0.99  --gc_record_bc_elim                     false
% 2.53/0.99  
% 2.53/0.99  ------ Preprocessing Options
% 2.53/0.99  
% 2.53/0.99  --preprocessing_flag                    true
% 2.53/0.99  --time_out_prep_mult                    0.1
% 2.53/0.99  --splitting_mode                        input
% 2.53/0.99  --splitting_grd                         true
% 2.53/0.99  --splitting_cvd                         false
% 2.53/0.99  --splitting_cvd_svl                     false
% 2.53/0.99  --splitting_nvd                         32
% 2.53/0.99  --sub_typing                            true
% 2.53/0.99  --prep_gs_sim                           true
% 2.53/0.99  --prep_unflatten                        true
% 2.53/0.99  --prep_res_sim                          true
% 2.53/0.99  --prep_upred                            true
% 2.53/0.99  --prep_sem_filter                       exhaustive
% 2.53/0.99  --prep_sem_filter_out                   false
% 2.53/0.99  --pred_elim                             true
% 2.53/0.99  --res_sim_input                         true
% 2.53/0.99  --eq_ax_congr_red                       true
% 2.53/0.99  --pure_diseq_elim                       true
% 2.53/0.99  --brand_transform                       false
% 2.53/0.99  --non_eq_to_eq                          false
% 2.53/0.99  --prep_def_merge                        true
% 2.53/0.99  --prep_def_merge_prop_impl              false
% 2.53/0.99  --prep_def_merge_mbd                    true
% 2.53/0.99  --prep_def_merge_tr_red                 false
% 2.53/0.99  --prep_def_merge_tr_cl                  false
% 2.53/0.99  --smt_preprocessing                     true
% 2.53/0.99  --smt_ac_axioms                         fast
% 2.53/0.99  --preprocessed_out                      false
% 2.53/0.99  --preprocessed_stats                    false
% 2.53/0.99  
% 2.53/0.99  ------ Abstraction refinement Options
% 2.53/0.99  
% 2.53/0.99  --abstr_ref                             []
% 2.53/0.99  --abstr_ref_prep                        false
% 2.53/0.99  --abstr_ref_until_sat                   false
% 2.53/0.99  --abstr_ref_sig_restrict                funpre
% 2.53/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.53/0.99  --abstr_ref_under                       []
% 2.53/0.99  
% 2.53/0.99  ------ SAT Options
% 2.53/0.99  
% 2.53/0.99  --sat_mode                              false
% 2.53/0.99  --sat_fm_restart_options                ""
% 2.53/0.99  --sat_gr_def                            false
% 2.53/0.99  --sat_epr_types                         true
% 2.53/0.99  --sat_non_cyclic_types                  false
% 2.53/0.99  --sat_finite_models                     false
% 2.53/0.99  --sat_fm_lemmas                         false
% 2.53/0.99  --sat_fm_prep                           false
% 2.53/0.99  --sat_fm_uc_incr                        true
% 2.53/0.99  --sat_out_model                         small
% 2.53/0.99  --sat_out_clauses                       false
% 2.53/0.99  
% 2.53/0.99  ------ QBF Options
% 2.53/0.99  
% 2.53/0.99  --qbf_mode                              false
% 2.53/0.99  --qbf_elim_univ                         false
% 2.53/0.99  --qbf_dom_inst                          none
% 2.53/0.99  --qbf_dom_pre_inst                      false
% 2.53/0.99  --qbf_sk_in                             false
% 2.53/0.99  --qbf_pred_elim                         true
% 2.53/0.99  --qbf_split                             512
% 2.53/0.99  
% 2.53/0.99  ------ BMC1 Options
% 2.53/0.99  
% 2.53/0.99  --bmc1_incremental                      false
% 2.53/0.99  --bmc1_axioms                           reachable_all
% 2.53/0.99  --bmc1_min_bound                        0
% 2.53/0.99  --bmc1_max_bound                        -1
% 2.53/0.99  --bmc1_max_bound_default                -1
% 2.53/0.99  --bmc1_symbol_reachability              true
% 2.53/0.99  --bmc1_property_lemmas                  false
% 2.53/0.99  --bmc1_k_induction                      false
% 2.53/0.99  --bmc1_non_equiv_states                 false
% 2.53/0.99  --bmc1_deadlock                         false
% 2.53/0.99  --bmc1_ucm                              false
% 2.53/0.99  --bmc1_add_unsat_core                   none
% 2.53/0.99  --bmc1_unsat_core_children              false
% 2.53/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.53/0.99  --bmc1_out_stat                         full
% 2.53/0.99  --bmc1_ground_init                      false
% 2.53/0.99  --bmc1_pre_inst_next_state              false
% 2.53/0.99  --bmc1_pre_inst_state                   false
% 2.53/0.99  --bmc1_pre_inst_reach_state             false
% 2.53/0.99  --bmc1_out_unsat_core                   false
% 2.53/0.99  --bmc1_aig_witness_out                  false
% 2.53/0.99  --bmc1_verbose                          false
% 2.53/0.99  --bmc1_dump_clauses_tptp                false
% 2.53/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.53/0.99  --bmc1_dump_file                        -
% 2.53/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.53/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.53/0.99  --bmc1_ucm_extend_mode                  1
% 2.53/0.99  --bmc1_ucm_init_mode                    2
% 2.53/0.99  --bmc1_ucm_cone_mode                    none
% 2.53/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.53/0.99  --bmc1_ucm_relax_model                  4
% 2.53/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.53/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.53/0.99  --bmc1_ucm_layered_model                none
% 2.53/0.99  --bmc1_ucm_max_lemma_size               10
% 2.53/0.99  
% 2.53/0.99  ------ AIG Options
% 2.53/0.99  
% 2.53/0.99  --aig_mode                              false
% 2.53/0.99  
% 2.53/0.99  ------ Instantiation Options
% 2.53/0.99  
% 2.53/0.99  --instantiation_flag                    true
% 2.53/0.99  --inst_sos_flag                         false
% 2.53/0.99  --inst_sos_phase                        true
% 2.53/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.53/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.53/0.99  --inst_lit_sel_side                     num_symb
% 2.53/0.99  --inst_solver_per_active                1400
% 2.53/0.99  --inst_solver_calls_frac                1.
% 2.53/0.99  --inst_passive_queue_type               priority_queues
% 2.53/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.53/0.99  --inst_passive_queues_freq              [25;2]
% 2.53/0.99  --inst_dismatching                      true
% 2.53/0.99  --inst_eager_unprocessed_to_passive     true
% 2.53/0.99  --inst_prop_sim_given                   true
% 2.53/0.99  --inst_prop_sim_new                     false
% 2.53/0.99  --inst_subs_new                         false
% 2.53/0.99  --inst_eq_res_simp                      false
% 2.53/0.99  --inst_subs_given                       false
% 2.53/0.99  --inst_orphan_elimination               true
% 2.53/0.99  --inst_learning_loop_flag               true
% 2.53/0.99  --inst_learning_start                   3000
% 2.53/0.99  --inst_learning_factor                  2
% 2.53/0.99  --inst_start_prop_sim_after_learn       3
% 2.53/0.99  --inst_sel_renew                        solver
% 2.53/0.99  --inst_lit_activity_flag                true
% 2.53/0.99  --inst_restr_to_given                   false
% 2.53/0.99  --inst_activity_threshold               500
% 2.53/0.99  --inst_out_proof                        true
% 2.53/0.99  
% 2.53/0.99  ------ Resolution Options
% 2.53/0.99  
% 2.53/0.99  --resolution_flag                       true
% 2.53/0.99  --res_lit_sel                           adaptive
% 2.53/0.99  --res_lit_sel_side                      none
% 2.53/0.99  --res_ordering                          kbo
% 2.53/0.99  --res_to_prop_solver                    active
% 2.53/0.99  --res_prop_simpl_new                    false
% 2.53/0.99  --res_prop_simpl_given                  true
% 2.53/0.99  --res_passive_queue_type                priority_queues
% 2.53/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.53/0.99  --res_passive_queues_freq               [15;5]
% 2.53/0.99  --res_forward_subs                      full
% 2.53/0.99  --res_backward_subs                     full
% 2.53/0.99  --res_forward_subs_resolution           true
% 2.53/0.99  --res_backward_subs_resolution          true
% 2.53/0.99  --res_orphan_elimination                true
% 2.53/0.99  --res_time_limit                        2.
% 2.53/0.99  --res_out_proof                         true
% 2.53/0.99  
% 2.53/0.99  ------ Superposition Options
% 2.53/0.99  
% 2.53/0.99  --superposition_flag                    true
% 2.53/0.99  --sup_passive_queue_type                priority_queues
% 2.53/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.53/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.53/0.99  --demod_completeness_check              fast
% 2.53/0.99  --demod_use_ground                      true
% 2.53/0.99  --sup_to_prop_solver                    passive
% 2.53/0.99  --sup_prop_simpl_new                    true
% 2.53/0.99  --sup_prop_simpl_given                  true
% 2.53/0.99  --sup_fun_splitting                     false
% 2.53/0.99  --sup_smt_interval                      50000
% 2.53/0.99  
% 2.53/0.99  ------ Superposition Simplification Setup
% 2.53/0.99  
% 2.53/0.99  --sup_indices_passive                   []
% 2.53/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.53/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/0.99  --sup_full_bw                           [BwDemod]
% 2.53/0.99  --sup_immed_triv                        [TrivRules]
% 2.53/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.53/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/0.99  --sup_immed_bw_main                     []
% 2.53/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.53/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/0.99  
% 2.53/0.99  ------ Combination Options
% 2.53/0.99  
% 2.53/0.99  --comb_res_mult                         3
% 2.53/0.99  --comb_sup_mult                         2
% 2.53/0.99  --comb_inst_mult                        10
% 2.53/0.99  
% 2.53/0.99  ------ Debug Options
% 2.53/0.99  
% 2.53/0.99  --dbg_backtrace                         false
% 2.53/0.99  --dbg_dump_prop_clauses                 false
% 2.53/0.99  --dbg_dump_prop_clauses_file            -
% 2.53/0.99  --dbg_out_stat                          false
% 2.53/0.99  ------ Parsing...
% 2.53/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.53/0.99  
% 2.53/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.53/0.99  
% 2.53/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.53/0.99  
% 2.53/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.53/0.99  ------ Proving...
% 2.53/0.99  ------ Problem Properties 
% 2.53/0.99  
% 2.53/0.99  
% 2.53/0.99  clauses                                 21
% 2.53/0.99  conjectures                             4
% 2.53/0.99  EPR                                     0
% 2.53/0.99  Horn                                    19
% 2.53/0.99  unary                                   8
% 2.53/0.99  binary                                  8
% 2.53/0.99  lits                                    46
% 2.53/0.99  lits eq                                 24
% 2.53/0.99  fd_pure                                 0
% 2.53/0.99  fd_pseudo                               0
% 2.53/0.99  fd_cond                                 2
% 2.53/0.99  fd_pseudo_cond                          0
% 2.53/0.99  AC symbols                              0
% 2.53/0.99  
% 2.53/0.99  ------ Schedule dynamic 5 is on 
% 2.53/0.99  
% 2.53/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.53/0.99  
% 2.53/0.99  
% 2.53/0.99  ------ 
% 2.53/0.99  Current options:
% 2.53/0.99  ------ 
% 2.53/0.99  
% 2.53/0.99  ------ Input Options
% 2.53/0.99  
% 2.53/0.99  --out_options                           all
% 2.53/0.99  --tptp_safe_out                         true
% 2.53/0.99  --problem_path                          ""
% 2.53/0.99  --include_path                          ""
% 2.53/0.99  --clausifier                            res/vclausify_rel
% 2.53/0.99  --clausifier_options                    --mode clausify
% 2.53/0.99  --stdin                                 false
% 2.53/0.99  --stats_out                             all
% 2.53/0.99  
% 2.53/0.99  ------ General Options
% 2.53/0.99  
% 2.53/0.99  --fof                                   false
% 2.53/0.99  --time_out_real                         305.
% 2.53/0.99  --time_out_virtual                      -1.
% 2.53/0.99  --symbol_type_check                     false
% 2.53/0.99  --clausify_out                          false
% 2.53/0.99  --sig_cnt_out                           false
% 2.53/0.99  --trig_cnt_out                          false
% 2.53/0.99  --trig_cnt_out_tolerance                1.
% 2.53/0.99  --trig_cnt_out_sk_spl                   false
% 2.53/0.99  --abstr_cl_out                          false
% 2.53/0.99  
% 2.53/0.99  ------ Global Options
% 2.53/0.99  
% 2.53/0.99  --schedule                              default
% 2.53/0.99  --add_important_lit                     false
% 2.53/0.99  --prop_solver_per_cl                    1000
% 2.53/0.99  --min_unsat_core                        false
% 2.53/0.99  --soft_assumptions                      false
% 2.53/0.99  --soft_lemma_size                       3
% 2.53/0.99  --prop_impl_unit_size                   0
% 2.53/0.99  --prop_impl_unit                        []
% 2.53/0.99  --share_sel_clauses                     true
% 2.53/0.99  --reset_solvers                         false
% 2.53/0.99  --bc_imp_inh                            [conj_cone]
% 2.53/0.99  --conj_cone_tolerance                   3.
% 2.53/0.99  --extra_neg_conj                        none
% 2.53/0.99  --large_theory_mode                     true
% 2.53/0.99  --prolific_symb_bound                   200
% 2.53/0.99  --lt_threshold                          2000
% 2.53/0.99  --clause_weak_htbl                      true
% 2.53/0.99  --gc_record_bc_elim                     false
% 2.53/0.99  
% 2.53/0.99  ------ Preprocessing Options
% 2.53/0.99  
% 2.53/0.99  --preprocessing_flag                    true
% 2.53/0.99  --time_out_prep_mult                    0.1
% 2.53/0.99  --splitting_mode                        input
% 2.53/0.99  --splitting_grd                         true
% 2.53/0.99  --splitting_cvd                         false
% 2.53/0.99  --splitting_cvd_svl                     false
% 2.53/0.99  --splitting_nvd                         32
% 2.53/0.99  --sub_typing                            true
% 2.53/0.99  --prep_gs_sim                           true
% 2.53/0.99  --prep_unflatten                        true
% 2.53/0.99  --prep_res_sim                          true
% 2.53/0.99  --prep_upred                            true
% 2.53/0.99  --prep_sem_filter                       exhaustive
% 2.53/0.99  --prep_sem_filter_out                   false
% 2.53/0.99  --pred_elim                             true
% 2.53/0.99  --res_sim_input                         true
% 2.53/0.99  --eq_ax_congr_red                       true
% 2.53/0.99  --pure_diseq_elim                       true
% 2.53/0.99  --brand_transform                       false
% 2.53/0.99  --non_eq_to_eq                          false
% 2.53/0.99  --prep_def_merge                        true
% 2.53/0.99  --prep_def_merge_prop_impl              false
% 2.53/0.99  --prep_def_merge_mbd                    true
% 2.53/0.99  --prep_def_merge_tr_red                 false
% 2.53/0.99  --prep_def_merge_tr_cl                  false
% 2.53/0.99  --smt_preprocessing                     true
% 2.53/0.99  --smt_ac_axioms                         fast
% 2.53/0.99  --preprocessed_out                      false
% 2.53/0.99  --preprocessed_stats                    false
% 2.53/0.99  
% 2.53/0.99  ------ Abstraction refinement Options
% 2.53/0.99  
% 2.53/0.99  --abstr_ref                             []
% 2.53/0.99  --abstr_ref_prep                        false
% 2.53/0.99  --abstr_ref_until_sat                   false
% 2.53/0.99  --abstr_ref_sig_restrict                funpre
% 2.53/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.53/0.99  --abstr_ref_under                       []
% 2.53/0.99  
% 2.53/0.99  ------ SAT Options
% 2.53/0.99  
% 2.53/0.99  --sat_mode                              false
% 2.53/0.99  --sat_fm_restart_options                ""
% 2.53/0.99  --sat_gr_def                            false
% 2.53/0.99  --sat_epr_types                         true
% 2.53/0.99  --sat_non_cyclic_types                  false
% 2.53/0.99  --sat_finite_models                     false
% 2.53/0.99  --sat_fm_lemmas                         false
% 2.53/0.99  --sat_fm_prep                           false
% 2.53/0.99  --sat_fm_uc_incr                        true
% 2.53/0.99  --sat_out_model                         small
% 2.53/0.99  --sat_out_clauses                       false
% 2.53/0.99  
% 2.53/0.99  ------ QBF Options
% 2.53/0.99  
% 2.53/0.99  --qbf_mode                              false
% 2.53/0.99  --qbf_elim_univ                         false
% 2.53/0.99  --qbf_dom_inst                          none
% 2.53/0.99  --qbf_dom_pre_inst                      false
% 2.53/0.99  --qbf_sk_in                             false
% 2.53/0.99  --qbf_pred_elim                         true
% 2.53/0.99  --qbf_split                             512
% 2.53/0.99  
% 2.53/0.99  ------ BMC1 Options
% 2.53/0.99  
% 2.53/0.99  --bmc1_incremental                      false
% 2.53/0.99  --bmc1_axioms                           reachable_all
% 2.53/0.99  --bmc1_min_bound                        0
% 2.53/0.99  --bmc1_max_bound                        -1
% 2.53/0.99  --bmc1_max_bound_default                -1
% 2.53/0.99  --bmc1_symbol_reachability              true
% 2.53/0.99  --bmc1_property_lemmas                  false
% 2.53/0.99  --bmc1_k_induction                      false
% 2.53/0.99  --bmc1_non_equiv_states                 false
% 2.53/0.99  --bmc1_deadlock                         false
% 2.53/0.99  --bmc1_ucm                              false
% 2.53/0.99  --bmc1_add_unsat_core                   none
% 2.53/0.99  --bmc1_unsat_core_children              false
% 2.53/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.53/0.99  --bmc1_out_stat                         full
% 2.53/0.99  --bmc1_ground_init                      false
% 2.53/0.99  --bmc1_pre_inst_next_state              false
% 2.53/0.99  --bmc1_pre_inst_state                   false
% 2.53/0.99  --bmc1_pre_inst_reach_state             false
% 2.53/0.99  --bmc1_out_unsat_core                   false
% 2.53/0.99  --bmc1_aig_witness_out                  false
% 2.53/0.99  --bmc1_verbose                          false
% 2.53/0.99  --bmc1_dump_clauses_tptp                false
% 2.53/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.53/0.99  --bmc1_dump_file                        -
% 2.53/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.53/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.53/0.99  --bmc1_ucm_extend_mode                  1
% 2.53/0.99  --bmc1_ucm_init_mode                    2
% 2.53/0.99  --bmc1_ucm_cone_mode                    none
% 2.53/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.53/0.99  --bmc1_ucm_relax_model                  4
% 2.53/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.53/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.53/0.99  --bmc1_ucm_layered_model                none
% 2.53/0.99  --bmc1_ucm_max_lemma_size               10
% 2.53/0.99  
% 2.53/0.99  ------ AIG Options
% 2.53/0.99  
% 2.53/0.99  --aig_mode                              false
% 2.53/0.99  
% 2.53/0.99  ------ Instantiation Options
% 2.53/0.99  
% 2.53/0.99  --instantiation_flag                    true
% 2.53/0.99  --inst_sos_flag                         false
% 2.53/0.99  --inst_sos_phase                        true
% 2.53/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.53/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.53/0.99  --inst_lit_sel_side                     none
% 2.53/0.99  --inst_solver_per_active                1400
% 2.53/0.99  --inst_solver_calls_frac                1.
% 2.53/0.99  --inst_passive_queue_type               priority_queues
% 2.53/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.53/0.99  --inst_passive_queues_freq              [25;2]
% 2.53/0.99  --inst_dismatching                      true
% 2.53/0.99  --inst_eager_unprocessed_to_passive     true
% 2.53/0.99  --inst_prop_sim_given                   true
% 2.53/0.99  --inst_prop_sim_new                     false
% 2.53/0.99  --inst_subs_new                         false
% 2.53/0.99  --inst_eq_res_simp                      false
% 2.53/0.99  --inst_subs_given                       false
% 2.53/0.99  --inst_orphan_elimination               true
% 2.53/0.99  --inst_learning_loop_flag               true
% 2.53/0.99  --inst_learning_start                   3000
% 2.53/0.99  --inst_learning_factor                  2
% 2.53/0.99  --inst_start_prop_sim_after_learn       3
% 2.53/0.99  --inst_sel_renew                        solver
% 2.53/0.99  --inst_lit_activity_flag                true
% 2.53/0.99  --inst_restr_to_given                   false
% 2.53/0.99  --inst_activity_threshold               500
% 2.53/0.99  --inst_out_proof                        true
% 2.53/0.99  
% 2.53/0.99  ------ Resolution Options
% 2.53/0.99  
% 2.53/0.99  --resolution_flag                       false
% 2.53/0.99  --res_lit_sel                           adaptive
% 2.53/0.99  --res_lit_sel_side                      none
% 2.53/0.99  --res_ordering                          kbo
% 2.53/0.99  --res_to_prop_solver                    active
% 2.53/0.99  --res_prop_simpl_new                    false
% 2.53/0.99  --res_prop_simpl_given                  true
% 2.53/0.99  --res_passive_queue_type                priority_queues
% 2.53/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.53/0.99  --res_passive_queues_freq               [15;5]
% 2.53/0.99  --res_forward_subs                      full
% 2.53/0.99  --res_backward_subs                     full
% 2.53/0.99  --res_forward_subs_resolution           true
% 2.53/0.99  --res_backward_subs_resolution          true
% 2.53/0.99  --res_orphan_elimination                true
% 2.53/0.99  --res_time_limit                        2.
% 2.53/0.99  --res_out_proof                         true
% 2.53/0.99  
% 2.53/0.99  ------ Superposition Options
% 2.53/0.99  
% 2.53/0.99  --superposition_flag                    true
% 2.53/0.99  --sup_passive_queue_type                priority_queues
% 2.53/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.53/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.53/0.99  --demod_completeness_check              fast
% 2.53/0.99  --demod_use_ground                      true
% 2.53/0.99  --sup_to_prop_solver                    passive
% 2.53/0.99  --sup_prop_simpl_new                    true
% 2.53/0.99  --sup_prop_simpl_given                  true
% 2.53/0.99  --sup_fun_splitting                     false
% 2.53/0.99  --sup_smt_interval                      50000
% 2.53/0.99  
% 2.53/0.99  ------ Superposition Simplification Setup
% 2.53/0.99  
% 2.53/0.99  --sup_indices_passive                   []
% 2.53/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.53/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/0.99  --sup_full_bw                           [BwDemod]
% 2.53/0.99  --sup_immed_triv                        [TrivRules]
% 2.53/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.53/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/0.99  --sup_immed_bw_main                     []
% 2.53/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.53/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/0.99  
% 2.53/0.99  ------ Combination Options
% 2.53/0.99  
% 2.53/0.99  --comb_res_mult                         3
% 2.53/0.99  --comb_sup_mult                         2
% 2.53/0.99  --comb_inst_mult                        10
% 2.53/0.99  
% 2.53/0.99  ------ Debug Options
% 2.53/0.99  
% 2.53/0.99  --dbg_backtrace                         false
% 2.53/0.99  --dbg_dump_prop_clauses                 false
% 2.53/0.99  --dbg_dump_prop_clauses_file            -
% 2.53/0.99  --dbg_out_stat                          false
% 2.53/0.99  
% 2.53/0.99  
% 2.53/0.99  
% 2.53/0.99  
% 2.53/0.99  ------ Proving...
% 2.53/0.99  
% 2.53/0.99  
% 2.53/0.99  % SZS status Theorem for theBenchmark.p
% 2.53/0.99  
% 2.53/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.53/0.99  
% 2.53/0.99  fof(f14,conjecture,(
% 2.53/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 2.53/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/0.99  
% 2.53/0.99  fof(f15,negated_conjecture,(
% 2.53/0.99    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 2.53/0.99    inference(negated_conjecture,[],[f14])).
% 2.53/0.99  
% 2.53/0.99  fof(f32,plain,(
% 2.53/0.99    ? [X0] : (? [X1] : (? [X2] : (((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 2.53/0.99    inference(ennf_transformation,[],[f15])).
% 2.53/0.99  
% 2.53/0.99  fof(f33,plain,(
% 2.53/0.99    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 2.53/0.99    inference(flattening,[],[f32])).
% 2.53/0.99  
% 2.53/0.99  fof(f36,plain,(
% 2.53/0.99    ( ! [X0,X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.53/0.99    introduced(choice_axiom,[])).
% 2.53/0.99  
% 2.53/0.99  fof(f35,plain,(
% 2.53/0.99    ( ! [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(sK1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 2.53/0.99    introduced(choice_axiom,[])).
% 2.53/0.99  
% 2.53/0.99  fof(f34,plain,(
% 2.53/0.99    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 2.53/0.99    introduced(choice_axiom,[])).
% 2.53/0.99  
% 2.53/0.99  fof(f37,plain,(
% 2.53/0.99    (((k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.53/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f36,f35,f34])).
% 2.53/0.99  
% 2.53/0.99  fof(f62,plain,(
% 2.53/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.53/0.99    inference(cnf_transformation,[],[f37])).
% 2.53/0.99  
% 2.53/0.99  fof(f11,axiom,(
% 2.53/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.53/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/0.99  
% 2.53/0.99  fof(f27,plain,(
% 2.53/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.53/0.99    inference(ennf_transformation,[],[f11])).
% 2.53/0.99  
% 2.53/0.99  fof(f54,plain,(
% 2.53/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.53/0.99    inference(cnf_transformation,[],[f27])).
% 2.53/0.99  
% 2.53/0.99  fof(f59,plain,(
% 2.53/0.99    l1_struct_0(sK1)),
% 2.53/0.99    inference(cnf_transformation,[],[f37])).
% 2.53/0.99  
% 2.53/0.99  fof(f57,plain,(
% 2.53/0.99    l1_struct_0(sK0)),
% 2.53/0.99    inference(cnf_transformation,[],[f37])).
% 2.53/0.99  
% 2.53/0.99  fof(f7,axiom,(
% 2.53/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.53/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/0.99  
% 2.53/0.99  fof(f22,plain,(
% 2.53/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.53/0.99    inference(ennf_transformation,[],[f7])).
% 2.53/0.99  
% 2.53/0.99  fof(f47,plain,(
% 2.53/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.53/0.99    inference(cnf_transformation,[],[f22])).
% 2.53/0.99  
% 2.53/0.99  fof(f63,plain,(
% 2.53/0.99    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 2.53/0.99    inference(cnf_transformation,[],[f37])).
% 2.53/0.99  
% 2.53/0.99  fof(f10,axiom,(
% 2.53/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 2.53/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/0.99  
% 2.53/0.99  fof(f25,plain,(
% 2.53/0.99    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.53/0.99    inference(ennf_transformation,[],[f10])).
% 2.53/0.99  
% 2.53/0.99  fof(f26,plain,(
% 2.53/0.99    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.53/0.99    inference(flattening,[],[f25])).
% 2.53/0.99  
% 2.53/0.99  fof(f52,plain,(
% 2.53/0.99    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.53/0.99    inference(cnf_transformation,[],[f26])).
% 2.53/0.99  
% 2.53/0.99  fof(f64,plain,(
% 2.53/0.99    v2_funct_1(sK2)),
% 2.53/0.99    inference(cnf_transformation,[],[f37])).
% 2.53/0.99  
% 2.53/0.99  fof(f60,plain,(
% 2.53/0.99    v1_funct_1(sK2)),
% 2.53/0.99    inference(cnf_transformation,[],[f37])).
% 2.53/0.99  
% 2.53/0.99  fof(f4,axiom,(
% 2.53/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 2.53/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/0.99  
% 2.53/0.99  fof(f18,plain,(
% 2.53/0.99    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.53/0.99    inference(ennf_transformation,[],[f4])).
% 2.53/0.99  
% 2.53/0.99  fof(f19,plain,(
% 2.53/0.99    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.53/0.99    inference(flattening,[],[f18])).
% 2.53/0.99  
% 2.53/0.99  fof(f43,plain,(
% 2.53/0.99    ( ! [X0] : (k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.53/0.99    inference(cnf_transformation,[],[f19])).
% 2.53/0.99  
% 2.53/0.99  fof(f8,axiom,(
% 2.53/0.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.53/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/0.99  
% 2.53/0.99  fof(f48,plain,(
% 2.53/0.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.53/0.99    inference(cnf_transformation,[],[f8])).
% 2.53/0.99  
% 2.53/0.99  fof(f69,plain,(
% 2.53/0.99    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.53/0.99    inference(definition_unfolding,[],[f43,f48])).
% 2.53/0.99  
% 2.53/0.99  fof(f5,axiom,(
% 2.53/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.53/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/0.99  
% 2.53/0.99  fof(f20,plain,(
% 2.53/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.53/0.99    inference(ennf_transformation,[],[f5])).
% 2.53/0.99  
% 2.53/0.99  fof(f45,plain,(
% 2.53/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.53/0.99    inference(cnf_transformation,[],[f20])).
% 2.53/0.99  
% 2.53/0.99  fof(f61,plain,(
% 2.53/0.99    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.53/0.99    inference(cnf_transformation,[],[f37])).
% 2.53/0.99  
% 2.53/0.99  fof(f1,axiom,(
% 2.53/0.99    v1_xboole_0(k1_xboole_0)),
% 2.53/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/0.99  
% 2.53/0.99  fof(f38,plain,(
% 2.53/0.99    v1_xboole_0(k1_xboole_0)),
% 2.53/0.99    inference(cnf_transformation,[],[f1])).
% 2.53/0.99  
% 2.53/0.99  fof(f12,axiom,(
% 2.53/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.53/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/0.99  
% 2.53/0.99  fof(f28,plain,(
% 2.53/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.53/0.99    inference(ennf_transformation,[],[f12])).
% 2.53/0.99  
% 2.53/0.99  fof(f29,plain,(
% 2.53/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.53/0.99    inference(flattening,[],[f28])).
% 2.53/0.99  
% 2.53/0.99  fof(f55,plain,(
% 2.53/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.53/0.99    inference(cnf_transformation,[],[f29])).
% 2.53/0.99  
% 2.53/0.99  fof(f58,plain,(
% 2.53/0.99    ~v2_struct_0(sK1)),
% 2.53/0.99    inference(cnf_transformation,[],[f37])).
% 2.53/0.99  
% 2.53/0.99  fof(f2,axiom,(
% 2.53/0.99    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.53/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/0.99  
% 2.53/0.99  fof(f40,plain,(
% 2.53/0.99    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.53/0.99    inference(cnf_transformation,[],[f2])).
% 2.53/0.99  
% 2.53/0.99  fof(f66,plain,(
% 2.53/0.99    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 2.53/0.99    inference(definition_unfolding,[],[f40,f48])).
% 2.53/0.99  
% 2.53/0.99  fof(f9,axiom,(
% 2.53/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.53/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/0.99  
% 2.53/0.99  fof(f23,plain,(
% 2.53/0.99    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.53/0.99    inference(ennf_transformation,[],[f9])).
% 2.53/0.99  
% 2.53/0.99  fof(f24,plain,(
% 2.53/0.99    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.53/0.99    inference(flattening,[],[f23])).
% 2.53/0.99  
% 2.53/0.99  fof(f51,plain,(
% 2.53/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.53/0.99    inference(cnf_transformation,[],[f24])).
% 2.53/0.99  
% 2.53/0.99  fof(f3,axiom,(
% 2.53/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 2.53/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/0.99  
% 2.53/0.99  fof(f16,plain,(
% 2.53/0.99    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.53/0.99    inference(ennf_transformation,[],[f3])).
% 2.53/0.99  
% 2.53/0.99  fof(f17,plain,(
% 2.53/0.99    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.53/0.99    inference(flattening,[],[f16])).
% 2.53/0.99  
% 2.53/0.99  fof(f42,plain,(
% 2.53/0.99    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.53/0.99    inference(cnf_transformation,[],[f17])).
% 2.53/0.99  
% 2.53/0.99  fof(f13,axiom,(
% 2.53/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.53/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/0.99  
% 2.53/0.99  fof(f30,plain,(
% 2.53/0.99    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.53/0.99    inference(ennf_transformation,[],[f13])).
% 2.53/0.99  
% 2.53/0.99  fof(f31,plain,(
% 2.53/0.99    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.53/0.99    inference(flattening,[],[f30])).
% 2.53/0.99  
% 2.53/0.99  fof(f56,plain,(
% 2.53/0.99    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.53/0.99    inference(cnf_transformation,[],[f31])).
% 2.53/0.99  
% 2.53/0.99  fof(f65,plain,(
% 2.53/0.99    k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)),
% 2.53/0.99    inference(cnf_transformation,[],[f37])).
% 2.53/0.99  
% 2.53/0.99  fof(f6,axiom,(
% 2.53/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.53/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/0.99  
% 2.53/0.99  fof(f21,plain,(
% 2.53/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.53/0.99    inference(ennf_transformation,[],[f6])).
% 2.53/0.99  
% 2.53/0.99  fof(f46,plain,(
% 2.53/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.53/0.99    inference(cnf_transformation,[],[f21])).
% 2.53/0.99  
% 2.53/0.99  fof(f41,plain,(
% 2.53/0.99    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.53/0.99    inference(cnf_transformation,[],[f17])).
% 2.53/0.99  
% 2.53/0.99  cnf(c_21,negated_conjecture,
% 2.53/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.53/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_1148,plain,
% 2.53/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.53/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_15,plain,
% 2.53/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.53/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_24,negated_conjecture,
% 2.53/0.99      ( l1_struct_0(sK1) ),
% 2.53/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_295,plain,
% 2.53/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.53/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_24]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_296,plain,
% 2.53/0.99      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.53/0.99      inference(unflattening,[status(thm)],[c_295]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_26,negated_conjecture,
% 2.53/0.99      ( l1_struct_0(sK0) ),
% 2.53/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_300,plain,
% 2.53/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.53/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_26]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_301,plain,
% 2.53/0.99      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.53/0.99      inference(unflattening,[status(thm)],[c_300]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_1169,plain,
% 2.53/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.53/0.99      inference(light_normalisation,[status(thm)],[c_1148,c_296,c_301]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_9,plain,
% 2.53/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.53/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.53/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_1149,plain,
% 2.53/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.53/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.53/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_1485,plain,
% 2.53/0.99      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 2.53/0.99      inference(superposition,[status(thm)],[c_1169,c_1149]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_20,negated_conjecture,
% 2.53/0.99      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.53/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_1166,plain,
% 2.53/0.99      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.53/0.99      inference(light_normalisation,[status(thm)],[c_20,c_296,c_301]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_1981,plain,
% 2.53/0.99      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 2.53/0.99      inference(demodulation,[status(thm)],[c_1485,c_1166]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_1987,plain,
% 2.53/0.99      ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 2.53/0.99      inference(demodulation,[status(thm)],[c_1981,c_1485]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_14,plain,
% 2.53/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.53/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.53/0.99      | ~ v1_funct_1(X0)
% 2.53/0.99      | ~ v2_funct_1(X0)
% 2.53/0.99      | k2_relset_1(X1,X2,X0) != X2
% 2.53/0.99      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 2.53/0.99      | k1_xboole_0 = X2 ),
% 2.53/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_19,negated_conjecture,
% 2.53/0.99      ( v2_funct_1(sK2) ),
% 2.53/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_415,plain,
% 2.53/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.53/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.53/0.99      | ~ v1_funct_1(X0)
% 2.53/0.99      | k2_relset_1(X1,X2,X0) != X2
% 2.53/0.99      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 2.53/0.99      | sK2 != X0
% 2.53/0.99      | k1_xboole_0 = X2 ),
% 2.53/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_19]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_416,plain,
% 2.53/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 2.53/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.53/0.99      | ~ v1_funct_1(sK2)
% 2.53/0.99      | k2_relset_1(X0,X1,sK2) != X1
% 2.53/0.99      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 2.53/0.99      | k1_xboole_0 = X1 ),
% 2.53/0.99      inference(unflattening,[status(thm)],[c_415]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_23,negated_conjecture,
% 2.53/0.99      ( v1_funct_1(sK2) ),
% 2.53/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_420,plain,
% 2.53/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.53/0.99      | ~ v1_funct_2(sK2,X0,X1)
% 2.53/0.99      | k2_relset_1(X0,X1,sK2) != X1
% 2.53/0.99      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 2.53/0.99      | k1_xboole_0 = X1 ),
% 2.53/0.99      inference(global_propositional_subsumption,
% 2.53/0.99                [status(thm)],
% 2.53/0.99                [c_416,c_23]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_421,plain,
% 2.53/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 2.53/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.53/0.99      | k2_relset_1(X0,X1,sK2) != X1
% 2.53/0.99      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 2.53/0.99      | k1_xboole_0 = X1 ),
% 2.53/0.99      inference(renaming,[status(thm)],[c_420]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_1145,plain,
% 2.53/0.99      ( k2_relset_1(X0,X1,sK2) != X1
% 2.53/0.99      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 2.53/0.99      | k1_xboole_0 = X1
% 2.53/0.99      | v1_funct_2(sK2,X0,X1) != iProver_top
% 2.53/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.53/0.99      inference(predicate_to_equality,[status(thm)],[c_421]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_6,plain,
% 2.53/0.99      ( ~ v1_relat_1(X0)
% 2.53/0.99      | ~ v1_funct_1(X0)
% 2.53/0.99      | ~ v2_funct_1(X0)
% 2.53/0.99      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 2.53/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_541,plain,
% 2.53/0.99      ( ~ v1_relat_1(X0)
% 2.53/0.99      | ~ v1_funct_1(X0)
% 2.53/0.99      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 2.53/0.99      | sK2 != X0 ),
% 2.53/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_19]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_542,plain,
% 2.53/0.99      ( ~ v1_relat_1(sK2)
% 2.53/0.99      | ~ v1_funct_1(sK2)
% 2.53/0.99      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 2.53/0.99      inference(unflattening,[status(thm)],[c_541]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_544,plain,
% 2.53/0.99      ( ~ v1_relat_1(sK2)
% 2.53/0.99      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 2.53/0.99      inference(global_propositional_subsumption,
% 2.53/0.99                [status(thm)],
% 2.53/0.99                [c_542,c_23]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_1141,plain,
% 2.53/0.99      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
% 2.53/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.53/0.99      inference(predicate_to_equality,[status(thm)],[c_544]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_7,plain,
% 2.53/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.53/0.99      | v1_relat_1(X0) ),
% 2.53/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_1297,plain,
% 2.53/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.53/0.99      | v1_relat_1(sK2) ),
% 2.53/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_1559,plain,
% 2.53/0.99      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 2.53/0.99      inference(global_propositional_subsumption,
% 2.53/0.99                [status(thm)],
% 2.53/0.99                [c_1141,c_23,c_21,c_542,c_1297]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_2234,plain,
% 2.53/0.99      ( k2_relset_1(X0,X1,sK2) != X1
% 2.53/0.99      | k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(X0)
% 2.53/0.99      | k1_xboole_0 = X1
% 2.53/0.99      | v1_funct_2(sK2,X0,X1) != iProver_top
% 2.53/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.53/0.99      inference(demodulation,[status(thm)],[c_1145,c_1559]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_2398,plain,
% 2.53/0.99      ( k2_relat_1(sK2) = k1_xboole_0
% 2.53/0.99      | k6_partfun1(k2_struct_0(sK0)) = k6_partfun1(k1_relat_1(sK2))
% 2.53/0.99      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.53/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
% 2.53/0.99      inference(superposition,[status(thm)],[c_1987,c_2234]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1991,plain,
% 2.53/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 2.53/1.00      inference(demodulation,[status(thm)],[c_1981,c_1169]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_22,negated_conjecture,
% 2.53/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.53/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1147,plain,
% 2.53/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1163,plain,
% 2.53/1.00      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.53/1.00      inference(light_normalisation,[status(thm)],[c_1147,c_296,c_301]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1992,plain,
% 2.53/1.00      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
% 2.53/1.00      inference(demodulation,[status(thm)],[c_1981,c_1163]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_0,plain,
% 2.53/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 2.53/1.00      inference(cnf_transformation,[],[f38]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_16,plain,
% 2.53/1.00      ( v2_struct_0(X0)
% 2.53/1.00      | ~ l1_struct_0(X0)
% 2.53/1.00      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.53/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_268,plain,
% 2.53/1.00      ( v2_struct_0(X0)
% 2.53/1.00      | ~ l1_struct_0(X0)
% 2.53/1.00      | u1_struct_0(X0) != k1_xboole_0 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_16]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_25,negated_conjecture,
% 2.53/1.00      ( ~ v2_struct_0(sK1) ),
% 2.53/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_286,plain,
% 2.53/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) != k1_xboole_0 | sK1 != X0 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_268,c_25]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_287,plain,
% 2.53/1.00      ( ~ l1_struct_0(sK1) | u1_struct_0(sK1) != k1_xboole_0 ),
% 2.53/1.00      inference(unflattening,[status(thm)],[c_286]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_270,plain,
% 2.53/1.00      ( v2_struct_0(sK1)
% 2.53/1.00      | ~ l1_struct_0(sK1)
% 2.53/1.00      | u1_struct_0(sK1) != k1_xboole_0 ),
% 2.53/1.00      inference(instantiation,[status(thm)],[c_268]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_289,plain,
% 2.53/1.00      ( u1_struct_0(sK1) != k1_xboole_0 ),
% 2.53/1.00      inference(global_propositional_subsumption,
% 2.53/1.00                [status(thm)],
% 2.53/1.00                [c_287,c_25,c_24,c_270]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1156,plain,
% 2.53/1.00      ( k2_struct_0(sK1) != k1_xboole_0 ),
% 2.53/1.00      inference(light_normalisation,[status(thm)],[c_289,c_296]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1993,plain,
% 2.53/1.00      ( k2_relat_1(sK2) != k1_xboole_0 ),
% 2.53/1.00      inference(demodulation,[status(thm)],[c_1981,c_1156]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2880,plain,
% 2.53/1.00      ( k6_partfun1(k2_struct_0(sK0)) = k6_partfun1(k1_relat_1(sK2)) ),
% 2.53/1.00      inference(global_propositional_subsumption,
% 2.53/1.00                [status(thm)],
% 2.53/1.00                [c_2398,c_1991,c_1992,c_1993]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1,plain,
% 2.53/1.00      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 2.53/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2884,plain,
% 2.53/1.00      ( k2_relat_1(k6_partfun1(k1_relat_1(sK2))) = k2_struct_0(sK0) ),
% 2.53/1.00      inference(superposition,[status(thm)],[c_2880,c_1]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2886,plain,
% 2.53/1.00      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.53/1.00      inference(demodulation,[status(thm)],[c_2884,c_1]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_10,plain,
% 2.53/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.53/1.00      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.53/1.00      | ~ v1_funct_1(X0)
% 2.53/1.00      | ~ v2_funct_1(X0)
% 2.53/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.53/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_517,plain,
% 2.53/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.53/1.00      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.53/1.00      | ~ v1_funct_1(X0)
% 2.53/1.00      | k2_relset_1(X1,X2,X0) != X2
% 2.53/1.00      | sK2 != X0 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_19]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_518,plain,
% 2.53/1.00      ( ~ v1_funct_2(sK2,X0,X1)
% 2.53/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.53/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.53/1.00      | ~ v1_funct_1(sK2)
% 2.53/1.00      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.53/1.00      inference(unflattening,[status(thm)],[c_517]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_522,plain,
% 2.53/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.53/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.53/1.00      | ~ v1_funct_2(sK2,X0,X1)
% 2.53/1.00      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.53/1.00      inference(global_propositional_subsumption,
% 2.53/1.00                [status(thm)],
% 2.53/1.00                [c_518,c_23]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_523,plain,
% 2.53/1.00      ( ~ v1_funct_2(sK2,X0,X1)
% 2.53/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.53/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.53/1.00      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.53/1.00      inference(renaming,[status(thm)],[c_522]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1142,plain,
% 2.53/1.00      ( k2_relset_1(X0,X1,sK2) != X1
% 2.53/1.00      | v1_funct_2(sK2,X0,X1) != iProver_top
% 2.53/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
% 2.53/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_523]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1788,plain,
% 2.53/1.00      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.53/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
% 2.53/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 2.53/1.00      inference(superposition,[status(thm)],[c_1166,c_1142]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2104,plain,
% 2.53/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top ),
% 2.53/1.00      inference(global_propositional_subsumption,
% 2.53/1.00                [status(thm)],
% 2.53/1.00                [c_1788,c_1169,c_1163]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2108,plain,
% 2.53/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
% 2.53/1.00      inference(light_normalisation,[status(thm)],[c_2104,c_1981]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2113,plain,
% 2.53/1.00      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 2.53/1.00      inference(superposition,[status(thm)],[c_2108,c_1149]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3,plain,
% 2.53/1.00      ( ~ v1_relat_1(X0)
% 2.53/1.00      | ~ v1_funct_1(X0)
% 2.53/1.00      | ~ v2_funct_1(X0)
% 2.53/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.53/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_583,plain,
% 2.53/1.00      ( ~ v1_relat_1(X0)
% 2.53/1.00      | ~ v1_funct_1(X0)
% 2.53/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 2.53/1.00      | sK2 != X0 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_19]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_584,plain,
% 2.53/1.00      ( ~ v1_relat_1(sK2)
% 2.53/1.00      | ~ v1_funct_1(sK2)
% 2.53/1.00      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.53/1.00      inference(unflattening,[status(thm)],[c_583]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_586,plain,
% 2.53/1.00      ( ~ v1_relat_1(sK2)
% 2.53/1.00      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.53/1.00      inference(global_propositional_subsumption,
% 2.53/1.00                [status(thm)],
% 2.53/1.00                [c_584,c_23]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1138,plain,
% 2.53/1.00      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.53/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_586]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1329,plain,
% 2.53/1.00      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.53/1.00      inference(global_propositional_subsumption,
% 2.53/1.00                [status(thm)],
% 2.53/1.00                [c_1138,c_23,c_21,c_584,c_1297]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2115,plain,
% 2.53/1.00      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.53/1.00      inference(light_normalisation,[status(thm)],[c_2113,c_1329]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_17,plain,
% 2.53/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.53/1.00      | ~ v1_funct_1(X0)
% 2.53/1.00      | ~ v2_funct_1(X0)
% 2.53/1.00      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.53/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.53/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_391,plain,
% 2.53/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.53/1.00      | ~ v1_funct_1(X0)
% 2.53/1.00      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.53/1.00      | k2_relset_1(X1,X2,X0) != X2
% 2.53/1.00      | sK2 != X0 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_19]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_392,plain,
% 2.53/1.00      ( ~ v1_funct_2(sK2,X0,X1)
% 2.53/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.53/1.00      | ~ v1_funct_1(sK2)
% 2.53/1.00      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.53/1.00      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.53/1.00      inference(unflattening,[status(thm)],[c_391]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_396,plain,
% 2.53/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.53/1.00      | ~ v1_funct_2(sK2,X0,X1)
% 2.53/1.00      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.53/1.00      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.53/1.00      inference(global_propositional_subsumption,
% 2.53/1.00                [status(thm)],
% 2.53/1.00                [c_392,c_23]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_397,plain,
% 2.53/1.00      ( ~ v1_funct_2(sK2,X0,X1)
% 2.53/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.53/1.00      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.53/1.00      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.53/1.00      inference(renaming,[status(thm)],[c_396]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1146,plain,
% 2.53/1.00      ( k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.53/1.00      | k2_relset_1(X0,X1,sK2) != X1
% 2.53/1.00      | v1_funct_2(sK2,X0,X1) != iProver_top
% 2.53/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_397]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1638,plain,
% 2.53/1.00      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 2.53/1.00      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.53/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 2.53/1.00      inference(superposition,[status(thm)],[c_1166,c_1146]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1678,plain,
% 2.53/1.00      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 2.53/1.00      inference(global_propositional_subsumption,
% 2.53/1.00                [status(thm)],
% 2.53/1.00                [c_1638,c_1169,c_1163]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_18,negated_conjecture,
% 2.53/1.00      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 2.53/1.00      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
% 2.53/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1200,plain,
% 2.53/1.00      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 2.53/1.00      | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
% 2.53/1.00      inference(light_normalisation,[status(thm)],[c_18,c_296,c_301]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1681,plain,
% 2.53/1.00      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
% 2.53/1.00      | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK1) ),
% 2.53/1.00      inference(demodulation,[status(thm)],[c_1678,c_1200]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1988,plain,
% 2.53/1.00      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
% 2.53/1.00      | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2) ),
% 2.53/1.00      inference(demodulation,[status(thm)],[c_1981,c_1681]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_8,plain,
% 2.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.53/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.53/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1150,plain,
% 2.53/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.53/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2112,plain,
% 2.53/1.00      ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
% 2.53/1.00      inference(superposition,[status(thm)],[c_2108,c_1150]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_4,plain,
% 2.53/1.00      ( ~ v1_relat_1(X0)
% 2.53/1.00      | ~ v1_funct_1(X0)
% 2.53/1.00      | ~ v2_funct_1(X0)
% 2.53/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.53/1.00      inference(cnf_transformation,[],[f41]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_569,plain,
% 2.53/1.00      ( ~ v1_relat_1(X0)
% 2.53/1.00      | ~ v1_funct_1(X0)
% 2.53/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 2.53/1.00      | sK2 != X0 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_19]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_570,plain,
% 2.53/1.00      ( ~ v1_relat_1(sK2)
% 2.53/1.00      | ~ v1_funct_1(sK2)
% 2.53/1.00      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.53/1.00      inference(unflattening,[status(thm)],[c_569]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_572,plain,
% 2.53/1.00      ( ~ v1_relat_1(sK2)
% 2.53/1.00      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.53/1.00      inference(global_propositional_subsumption,
% 2.53/1.00                [status(thm)],
% 2.53/1.00                [c_570,c_23]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1139,plain,
% 2.53/1.00      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 2.53/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_572]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1357,plain,
% 2.53/1.00      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.53/1.00      inference(global_propositional_subsumption,
% 2.53/1.00                [status(thm)],
% 2.53/1.00                [c_1139,c_23,c_21,c_570,c_1297]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2118,plain,
% 2.53/1.00      ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.53/1.00      inference(light_normalisation,[status(thm)],[c_2112,c_1357]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2412,plain,
% 2.53/1.00      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
% 2.53/1.00      inference(global_propositional_subsumption,
% 2.53/1.00                [status(thm)],
% 2.53/1.00                [c_1988,c_2118]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2818,plain,
% 2.53/1.00      ( k2_struct_0(sK0) != k1_relat_1(sK2) ),
% 2.53/1.00      inference(demodulation,[status(thm)],[c_2115,c_2412]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(contradiction,plain,
% 2.53/1.00      ( $false ),
% 2.53/1.00      inference(minisat,[status(thm)],[c_2886,c_2818]) ).
% 2.53/1.00  
% 2.53/1.00  
% 2.53/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.53/1.00  
% 2.53/1.00  ------                               Statistics
% 2.53/1.00  
% 2.53/1.00  ------ General
% 2.53/1.00  
% 2.53/1.00  abstr_ref_over_cycles:                  0
% 2.53/1.00  abstr_ref_under_cycles:                 0
% 2.53/1.00  gc_basic_clause_elim:                   0
% 2.53/1.00  forced_gc_time:                         0
% 2.53/1.00  parsing_time:                           0.008
% 2.53/1.00  unif_index_cands_time:                  0.
% 2.53/1.00  unif_index_add_time:                    0.
% 2.53/1.00  orderings_time:                         0.
% 2.53/1.00  out_proof_time:                         0.009
% 2.53/1.00  total_time:                             0.127
% 2.53/1.00  num_of_symbols:                         55
% 2.53/1.00  num_of_terms:                           2087
% 2.53/1.00  
% 2.53/1.00  ------ Preprocessing
% 2.53/1.00  
% 2.53/1.00  num_of_splits:                          0
% 2.53/1.00  num_of_split_atoms:                     0
% 2.53/1.00  num_of_reused_defs:                     0
% 2.53/1.00  num_eq_ax_congr_red:                    2
% 2.53/1.00  num_of_sem_filtered_clauses:            1
% 2.53/1.00  num_of_subtypes:                        0
% 2.53/1.00  monotx_restored_types:                  0
% 2.53/1.00  sat_num_of_epr_types:                   0
% 2.53/1.00  sat_num_of_non_cyclic_types:            0
% 2.53/1.00  sat_guarded_non_collapsed_types:        0
% 2.53/1.00  num_pure_diseq_elim:                    0
% 2.53/1.00  simp_replaced_by:                       0
% 2.53/1.00  res_preprocessed:                       125
% 2.53/1.00  prep_upred:                             0
% 2.53/1.00  prep_unflattend:                        21
% 2.53/1.00  smt_new_axioms:                         0
% 2.53/1.00  pred_elim_cands:                        3
% 2.53/1.00  pred_elim:                              5
% 2.53/1.00  pred_elim_cl:                           6
% 2.53/1.00  pred_elim_cycles:                       8
% 2.53/1.00  merged_defs:                            0
% 2.53/1.00  merged_defs_ncl:                        0
% 2.53/1.00  bin_hyper_res:                          0
% 2.53/1.00  prep_cycles:                            4
% 2.53/1.00  pred_elim_time:                         0.01
% 2.53/1.00  splitting_time:                         0.
% 2.53/1.00  sem_filter_time:                        0.
% 2.53/1.00  monotx_time:                            0.001
% 2.53/1.00  subtype_inf_time:                       0.
% 2.53/1.00  
% 2.53/1.00  ------ Problem properties
% 2.53/1.00  
% 2.53/1.00  clauses:                                21
% 2.53/1.00  conjectures:                            4
% 2.53/1.00  epr:                                    0
% 2.53/1.00  horn:                                   19
% 2.53/1.00  ground:                                 11
% 2.53/1.00  unary:                                  8
% 2.53/1.00  binary:                                 8
% 2.53/1.00  lits:                                   46
% 2.53/1.00  lits_eq:                                24
% 2.53/1.00  fd_pure:                                0
% 2.53/1.00  fd_pseudo:                              0
% 2.53/1.00  fd_cond:                                2
% 2.53/1.00  fd_pseudo_cond:                         0
% 2.53/1.00  ac_symbols:                             0
% 2.53/1.00  
% 2.53/1.00  ------ Propositional Solver
% 2.53/1.00  
% 2.53/1.00  prop_solver_calls:                      28
% 2.53/1.00  prop_fast_solver_calls:                 848
% 2.53/1.00  smt_solver_calls:                       0
% 2.53/1.00  smt_fast_solver_calls:                  0
% 2.53/1.00  prop_num_of_clauses:                    985
% 2.53/1.00  prop_preprocess_simplified:             3657
% 2.53/1.00  prop_fo_subsumed:                       28
% 2.53/1.00  prop_solver_time:                       0.
% 2.53/1.00  smt_solver_time:                        0.
% 2.53/1.00  smt_fast_solver_time:                   0.
% 2.53/1.00  prop_fast_solver_time:                  0.
% 2.53/1.00  prop_unsat_core_time:                   0.
% 2.53/1.00  
% 2.53/1.00  ------ QBF
% 2.53/1.00  
% 2.53/1.00  qbf_q_res:                              0
% 2.53/1.00  qbf_num_tautologies:                    0
% 2.53/1.00  qbf_prep_cycles:                        0
% 2.53/1.00  
% 2.53/1.00  ------ BMC1
% 2.53/1.00  
% 2.53/1.00  bmc1_current_bound:                     -1
% 2.53/1.00  bmc1_last_solved_bound:                 -1
% 2.53/1.00  bmc1_unsat_core_size:                   -1
% 2.53/1.00  bmc1_unsat_core_parents_size:           -1
% 2.53/1.00  bmc1_merge_next_fun:                    0
% 2.53/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.53/1.00  
% 2.53/1.00  ------ Instantiation
% 2.53/1.00  
% 2.53/1.00  inst_num_of_clauses:                    348
% 2.53/1.00  inst_num_in_passive:                    145
% 2.53/1.00  inst_num_in_active:                     187
% 2.53/1.00  inst_num_in_unprocessed:                16
% 2.53/1.00  inst_num_of_loops:                      210
% 2.53/1.00  inst_num_of_learning_restarts:          0
% 2.53/1.00  inst_num_moves_active_passive:          19
% 2.53/1.00  inst_lit_activity:                      0
% 2.53/1.00  inst_lit_activity_moves:                0
% 2.53/1.00  inst_num_tautologies:                   0
% 2.53/1.00  inst_num_prop_implied:                  0
% 2.53/1.00  inst_num_existing_simplified:           0
% 2.53/1.00  inst_num_eq_res_simplified:             0
% 2.53/1.00  inst_num_child_elim:                    0
% 2.53/1.00  inst_num_of_dismatching_blockings:      17
% 2.53/1.00  inst_num_of_non_proper_insts:           241
% 2.53/1.00  inst_num_of_duplicates:                 0
% 2.53/1.00  inst_inst_num_from_inst_to_res:         0
% 2.53/1.00  inst_dismatching_checking_time:         0.
% 2.53/1.00  
% 2.53/1.00  ------ Resolution
% 2.53/1.00  
% 2.53/1.00  res_num_of_clauses:                     0
% 2.53/1.00  res_num_in_passive:                     0
% 2.53/1.00  res_num_in_active:                      0
% 2.53/1.00  res_num_of_loops:                       129
% 2.53/1.00  res_forward_subset_subsumed:            41
% 2.53/1.00  res_backward_subset_subsumed:           2
% 2.53/1.00  res_forward_subsumed:                   0
% 2.53/1.00  res_backward_subsumed:                  0
% 2.53/1.00  res_forward_subsumption_resolution:     0
% 2.53/1.00  res_backward_subsumption_resolution:    0
% 2.53/1.00  res_clause_to_clause_subsumption:       54
% 2.53/1.00  res_orphan_elimination:                 0
% 2.53/1.00  res_tautology_del:                      29
% 2.53/1.00  res_num_eq_res_simplified:              0
% 2.53/1.00  res_num_sel_changes:                    0
% 2.53/1.00  res_moves_from_active_to_pass:          0
% 2.53/1.00  
% 2.53/1.00  ------ Superposition
% 2.53/1.00  
% 2.53/1.00  sup_time_total:                         0.
% 2.53/1.00  sup_time_generating:                    0.
% 2.53/1.00  sup_time_sim_full:                      0.
% 2.53/1.00  sup_time_sim_immed:                     0.
% 2.53/1.00  
% 2.53/1.00  sup_num_of_clauses:                     32
% 2.53/1.00  sup_num_in_active:                      31
% 2.53/1.00  sup_num_in_passive:                     1
% 2.53/1.00  sup_num_of_loops:                       41
% 2.53/1.00  sup_fw_superposition:                   7
% 2.53/1.00  sup_bw_superposition:                   17
% 2.53/1.00  sup_immediate_simplified:               9
% 2.53/1.00  sup_given_eliminated:                   1
% 2.53/1.00  comparisons_done:                       0
% 2.53/1.00  comparisons_avoided:                    0
% 2.53/1.00  
% 2.53/1.00  ------ Simplifications
% 2.53/1.00  
% 2.53/1.00  
% 2.53/1.00  sim_fw_subset_subsumed:                 7
% 2.53/1.00  sim_bw_subset_subsumed:                 0
% 2.53/1.00  sim_fw_subsumed:                        0
% 2.53/1.00  sim_bw_subsumed:                        0
% 2.53/1.00  sim_fw_subsumption_res:                 0
% 2.53/1.00  sim_bw_subsumption_res:                 0
% 2.53/1.00  sim_tautology_del:                      0
% 2.53/1.00  sim_eq_tautology_del:                   3
% 2.53/1.00  sim_eq_res_simp:                        0
% 2.53/1.00  sim_fw_demodulated:                     3
% 2.53/1.00  sim_bw_demodulated:                     12
% 2.53/1.00  sim_light_normalised:                   10
% 2.53/1.00  sim_joinable_taut:                      0
% 2.53/1.00  sim_joinable_simp:                      0
% 2.53/1.00  sim_ac_normalised:                      0
% 2.53/1.00  sim_smt_subsumption:                    0
% 2.53/1.00  
%------------------------------------------------------------------------------
