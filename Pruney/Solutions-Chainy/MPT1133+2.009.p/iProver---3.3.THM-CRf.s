%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:49 EST 2020

% Result     : Theorem 7.74s
% Output     : CNFRefutation 7.74s
% Verified   : 
% Statistics : Number of formulae       :  312 (21259 expanded)
%              Number of clauses        :  211 (5108 expanded)
%              Number of leaves         :   25 (5875 expanded)
%              Depth                    :   27
%              Number of atoms          : 1306 (210933 expanded)
%              Number of equality atoms :  512 (22543 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f13,axiom,(
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

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f113,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f81])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f15,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f87,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f86,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f21,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                      & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                      & v1_funct_1(X3) )
                   => ( X2 = X3
                     => ( v5_pre_topc(X2,X0,X1)
                      <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f49])).

fof(f57,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f58,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f57])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
            | ~ v5_pre_topc(X2,X0,X1) )
          & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
            | v5_pre_topc(X2,X0,X1) )
          & X2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
          & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
          & v1_funct_1(X3) )
     => ( ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
          | ~ v5_pre_topc(X2,X0,X1) )
        & ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
          | v5_pre_topc(X2,X0,X1) )
        & sK3 = X2
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                | ~ v5_pre_topc(X2,X0,X1) )
              & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                | v5_pre_topc(X2,X0,X1) )
              & X2 = X3
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
              & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
              & v1_funct_1(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ? [X3] :
            ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ v5_pre_topc(sK2,X0,X1) )
            & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | v5_pre_topc(sK2,X0,X1) )
            & sK2 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
            & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
            & v1_funct_1(X3) )
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
                  | ~ v5_pre_topc(X2,X0,sK1) )
                & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
                  | v5_pre_topc(X2,X0,sK1) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
                & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | ~ v5_pre_topc(X2,X0,X1) )
                    & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | v5_pre_topc(X2,X0,X1) )
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,sK0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,sK0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ v5_pre_topc(sK2,sK0,sK1) )
    & ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | v5_pre_topc(sK2,sK0,sK1) )
    & sK2 = sK3
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f58,f62,f61,f60,f59])).

fof(f101,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f63])).

fof(f105,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f63])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f35])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f102,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f63])).

fof(f100,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f63])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f33])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f114,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f79])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f51])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f109,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f65])).

fof(f103,plain,(
    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(cnf_transformation,[],[f63])).

fof(f104,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(cnf_transformation,[],[f63])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v5_pre_topc(X2,X0,X1)
                      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                    & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                      | ~ v5_pre_topc(X2,X0,X1) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X2,X0,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f117,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f91])).

fof(f95,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f63])).

fof(f96,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f63])).

fof(f97,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f63])).

fof(f98,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f63])).

fof(f107,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f63])).

fof(f106,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f63])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f43,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f44,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f90,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f41,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f88,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f89,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v5_pre_topc(X2,X0,X1)
                      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                    & ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | ~ v5_pre_topc(X2,X0,X1) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f118,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f94])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f119,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f93])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f116,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f92])).

fof(f67,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_5,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_3026,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_3023,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4059,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3026,c_3023])).

cnf(c_16,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f113])).

cnf(c_3019,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_6867,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4059,c_3019])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_3030,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_22,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_3015,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_3024,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4809,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k6_partfun1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3015,c_3024])).

cnf(c_4,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_3027,plain,
    ( X0 = X1
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_8039,plain,
    ( k6_partfun1(X0) = X1
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4809,c_3027])).

cnf(c_9235,plain,
    ( k6_partfun1(k1_xboole_0) = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3030,c_8039])).

cnf(c_9343,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3030,c_9235])).

cnf(c_8,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_21,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_583,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_8,c_21])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_587,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_583,c_21,c_8,c_7])).

cnf(c_588,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_587])).

cnf(c_23,plain,
    ( v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_651,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 != X1
    | k6_partfun1(X3) != X0
    | k1_relat_1(X0) = X1 ),
    inference(resolution_lifted,[status(thm)],[c_588,c_23])).

cnf(c_652,plain,
    ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_651])).

cnf(c_2994,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0
    | m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_652])).

cnf(c_3563,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(superposition,[status(thm)],[c_3015,c_2994])).

cnf(c_10355,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9343,c_3563])).

cnf(c_11321,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6867,c_10355])).

cnf(c_11327,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3026,c_11321])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_3002,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_33,negated_conjecture,
    ( sK2 = sK3 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_3033,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3002,c_33])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_627,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_12,c_588])).

cnf(c_629,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_627,c_21,c_12,c_8,c_7])).

cnf(c_630,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_629])).

cnf(c_2995,plain,
    ( k1_relat_1(X0) = X1
    | v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_630])).

cnf(c_3883,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3033,c_2995])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_51,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_38,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_3001,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_3032,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3001,c_33])).

cnf(c_4087,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3883,c_51,c_3032])).

cnf(c_9238,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | k6_partfun1(u1_struct_0(sK1)) = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4087,c_8039])).

cnf(c_10147,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | k6_partfun1(u1_struct_0(sK1)) = u1_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_4087,c_9238])).

cnf(c_10211,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_10147,c_3015])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_3022,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_10471,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1)))) = iProver_top
    | r1_tarski(k1_relat_1(u1_struct_0(sK1)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10211,c_3022])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f114])).

cnf(c_3017,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_12691,plain,
    ( k1_relset_1(k1_xboole_0,u1_struct_0(sK1),u1_struct_0(sK1)) = k1_xboole_0
    | u1_struct_0(sK0) = k1_relat_1(sK3)
    | v1_funct_2(u1_struct_0(sK1),k1_xboole_0,u1_struct_0(sK1)) != iProver_top
    | r1_tarski(k1_relat_1(u1_struct_0(sK1)),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10471,c_3017])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_131,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_133,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_131])).

cnf(c_2145,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_4954,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(u1_struct_0(sK1)),X1)
    | k1_relat_1(u1_struct_0(sK1)) != X0 ),
    inference(instantiation,[status(thm)],[c_2145])).

cnf(c_4955,plain,
    ( k1_relat_1(u1_struct_0(sK1)) != X0
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(u1_struct_0(sK1)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4954])).

cnf(c_4957,plain,
    ( k1_relat_1(u1_struct_0(sK1)) != k1_xboole_0
    | r1_tarski(k1_relat_1(u1_struct_0(sK1)),k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4955])).

cnf(c_4091,plain,
    ( u1_struct_0(sK1) = X0
    | u1_struct_0(sK0) = k1_relat_1(sK3)
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4087,c_3027])).

cnf(c_4542,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK0) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_3030,c_4091])).

cnf(c_10470,plain,
    ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1)) = k1_relat_1(u1_struct_0(sK1))
    | u1_struct_0(sK0) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_10211,c_3023])).

cnf(c_10477,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_relat_1(u1_struct_0(sK1))
    | u1_struct_0(sK0) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_4542,c_10470])).

cnf(c_10481,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | k1_relat_1(u1_struct_0(sK1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10477,c_4059,c_10355])).

cnf(c_17606,plain,
    ( v1_funct_2(u1_struct_0(sK1),k1_xboole_0,u1_struct_0(sK1)) != iProver_top
    | u1_struct_0(sK0) = k1_relat_1(sK3)
    | k1_relset_1(k1_xboole_0,u1_struct_0(sK1),u1_struct_0(sK1)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12691,c_133,c_4957,c_10481])).

cnf(c_17607,plain,
    ( k1_relset_1(k1_xboole_0,u1_struct_0(sK1),u1_struct_0(sK1)) = k1_xboole_0
    | u1_struct_0(sK0) = k1_relat_1(sK3)
    | v1_funct_2(u1_struct_0(sK1),k1_xboole_0,u1_struct_0(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_17606])).

cnf(c_4811,plain,
    ( v1_xboole_0(u1_struct_0(sK1)) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3033,c_3024])).

cnf(c_4944,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4087,c_4811])).

cnf(c_3956,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3030,c_3027])).

cnf(c_7174,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4944,c_3956])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_3004,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_15026,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7174,c_3004])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_3005,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_5531,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3005,c_3022])).

cnf(c_5651,plain,
    ( k1_relat_1(sK3) = X0
    | v1_funct_2(sK3,X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5531,c_2995])).

cnf(c_11263,plain,
    ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | v1_funct_2(sK3,X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | k1_relat_1(sK3) = X0
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5651,c_51])).

cnf(c_11264,plain,
    ( k1_relat_1(sK3) = X0
    | v1_funct_2(sK3,X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
    inference(renaming,[status(thm)],[c_11263])).

cnf(c_15286,plain,
    ( u1_struct_0(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | sK3 = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0)))) != iProver_top
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_15026,c_11264])).

cnf(c_3418,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(sK3)
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3420,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK3 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3418])).

cnf(c_3363,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_3868,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3363])).

cnf(c_15070,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_15026])).

cnf(c_15025,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7174,c_3005])).

cnf(c_15300,plain,
    ( u1_struct_0(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | sK3 = k1_xboole_0
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_15025,c_2995])).

cnf(c_15304,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | u1_struct_0(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_15300])).

cnf(c_16296,plain,
    ( u1_struct_0(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_15286,c_36,c_34,c_0,c_3420,c_3868,c_15070,c_15304])).

cnf(c_16323,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_16296,c_15026])).

cnf(c_28,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_3010,plain,
    ( v5_pre_topc(X0,X1,X2) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) = iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_6005,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3005,c_3010])).

cnf(c_43,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_44,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_42,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_45,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_41,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_46,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_40,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_47,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_52,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_31,negated_conjecture,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_3007,plain,
    ( v5_pre_topc(sK2,sK0,sK1) != iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3035,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v5_pre_topc(sK3,sK0,sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3007,c_33])).

cnf(c_32,negated_conjecture,
    ( v5_pre_topc(sK2,sK0,sK1)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_3006,plain,
    ( v5_pre_topc(sK2,sK0,sK1) = iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_3034,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v5_pre_topc(sK3,sK0,sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3006,c_33])).

cnf(c_26,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_3188,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_3189,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3188])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_3446,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_3447,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3446])).

cnf(c_25,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_3660,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_3661,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3660])).

cnf(c_29,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_3596,plain,
    ( ~ v5_pre_topc(sK3,X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK3,X0,sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_3977,plain,
    ( ~ v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK3,sK0,sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3596])).

cnf(c_3978,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v5_pre_topc(sK3,sK0,sK1) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3977])).

cnf(c_30,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_3940,plain,
    ( ~ v5_pre_topc(sK3,sK0,X0)
    | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(X0))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_5507,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK3,sK0,sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3940])).

cnf(c_5508,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v5_pre_topc(sK3,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5507])).

cnf(c_27,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_3011,plain,
    ( v5_pre_topc(X0,X1,X2) = iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_6360,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3005,c_3011])).

cnf(c_6474,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6005,c_44,c_45,c_46,c_47,c_51,c_52,c_3035,c_3032,c_3034,c_3033,c_3189,c_3447,c_3661,c_3978,c_5508,c_6360])).

cnf(c_6475,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6474])).

cnf(c_6478,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6475,c_44,c_45,c_46,c_47,c_51,c_52,c_3032,c_3034,c_3033,c_3189,c_3447,c_3661,c_5508,c_6360])).

cnf(c_15018,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7174,c_6478])).

cnf(c_15805,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5531,c_15018])).

cnf(c_14258,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_14259,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14258])).

cnf(c_15893,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_15805,c_14259])).

cnf(c_15894,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_15893])).

cnf(c_15897,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7174,c_15894])).

cnf(c_16368,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_16323,c_15897])).

cnf(c_17610,plain,
    ( k1_relset_1(k1_xboole_0,u1_struct_0(sK1),u1_struct_0(sK1)) = k1_xboole_0
    | u1_struct_0(sK0) = k1_xboole_0
    | v1_funct_2(u1_struct_0(sK1),k1_xboole_0,u1_struct_0(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17607,c_10355,c_16368])).

cnf(c_4858,plain,
    ( v1_funct_2(X0,k1_xboole_0,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | k1_relset_1(k1_xboole_0,u1_struct_0(sK1),X0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_4859,plain,
    ( k1_relset_1(k1_xboole_0,u1_struct_0(sK1),X0) != k1_xboole_0
    | v1_funct_2(X0,k1_xboole_0,u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4858])).

cnf(c_4861,plain,
    ( k1_relset_1(k1_xboole_0,u1_struct_0(sK1),k1_xboole_0) != k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4859])).

cnf(c_14799,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_14800,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14799])).

cnf(c_3028,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5532,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1)))) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3033,c_3022])).

cnf(c_5543,plain,
    ( k1_relset_1(X0,u1_struct_0(sK1),sK3) = k1_relat_1(sK3)
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5532,c_3023])).

cnf(c_5777,plain,
    ( k1_relset_1(k1_relat_1(sK3),u1_struct_0(sK1),sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_3028,c_5543])).

cnf(c_16482,plain,
    ( k1_relset_1(k1_relat_1(k1_xboole_0),u1_struct_0(sK1),k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_16368,c_5777])).

cnf(c_16541,plain,
    ( k1_relset_1(k1_xboole_0,u1_struct_0(sK1),k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_16482,c_10355])).

cnf(c_3882,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3005,c_2995])).

cnf(c_4285,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3882,c_51,c_52])).

cnf(c_7400,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | u1_struct_0(sK0) = k1_relat_1(sK3)
    | v1_xboole_0(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4542,c_4285])).

cnf(c_4544,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = u1_struct_0(sK1)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | u1_struct_0(sK0) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_4285,c_4091])).

cnf(c_5144,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | u1_struct_0(sK0) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4544,c_3004])).

cnf(c_5143,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | u1_struct_0(sK0) = k1_relat_1(sK3)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4544,c_3005])).

cnf(c_3009,plain,
    ( v5_pre_topc(X0,X1,X2) = iProver_top
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5295,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3005,c_3009])).

cnf(c_3173,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_3174,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3173])).

cnf(c_3434,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_3435,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3434])).

cnf(c_3650,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_3651,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3650])).

cnf(c_3008,plain,
    ( v5_pre_topc(X0,X1,X2) != iProver_top
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) = iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_4674,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3005,c_3008])).

cnf(c_3626,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)
    | v5_pre_topc(sK3,sK0,X0)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X0))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(X0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X0))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_4002,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK3,sK0,sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3626])).

cnf(c_4003,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
    | v5_pre_topc(sK3,sK0,sK1) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4002])).

cnf(c_5080,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4674,c_44,c_45,c_46,c_47,c_51,c_52,c_3035,c_3032,c_3033,c_3174,c_3435,c_3651,c_4003])).

cnf(c_5081,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5080])).

cnf(c_3928,plain,
    ( ~ v5_pre_topc(sK3,X0,sK1)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(sK1))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK1))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_5493,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v5_pre_topc(sK3,sK0,sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3928])).

cnf(c_5494,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top
    | v5_pre_topc(sK3,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5493])).

cnf(c_5669,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5295,c_44,c_45,c_46,c_47,c_51,c_52,c_3032,c_3034,c_3033,c_3174,c_3435,c_3651,c_5081,c_5494])).

cnf(c_5670,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5669])).

cnf(c_5673,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | u1_struct_0(sK0) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5143,c_5670])).

cnf(c_8809,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7400,c_5144,c_5673])).

cnf(c_8810,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | u1_struct_0(sK0) = k1_relat_1(sK3) ),
    inference(renaming,[status(thm)],[c_8809])).

cnf(c_8841,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8810,c_5670])).

cnf(c_10094,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8810,c_8841])).

cnf(c_16397,plain,
    ( u1_struct_0(sK0) = k1_relat_1(k1_xboole_0)
    | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(sK1)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_16368,c_10094])).

cnf(c_16607,plain,
    ( u1_struct_0(sK0) = k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16397,c_10355])).

cnf(c_17612,plain,
    ( u1_struct_0(sK0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_17610,c_4861,c_14800,c_16541,c_16607])).

cnf(c_16488,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_16368,c_6478])).

cnf(c_132,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_136,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2143,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_10575,plain,
    ( X0 != X1
    | X0 = u1_struct_0(sK0)
    | u1_struct_0(sK0) != X1 ),
    inference(instantiation,[status(thm)],[c_2143])).

cnf(c_10576,plain,
    ( u1_struct_0(sK0) != k1_xboole_0
    | k1_xboole_0 = u1_struct_0(sK0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10575])).

cnf(c_10928,plain,
    ( r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_10929,plain,
    ( r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10928])).

cnf(c_6482,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | r1_tarski(k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5531,c_6478])).

cnf(c_16487,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | r1_tarski(k1_relat_1(k1_xboole_0),u1_struct_0(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_16368,c_6482])).

cnf(c_16536,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | r1_tarski(k1_xboole_0,u1_struct_0(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16487,c_10355])).

cnf(c_8946,plain,
    ( ~ r1_tarski(X0,u1_struct_0(sK0))
    | r1_tarski(X1,u1_struct_0(sK0))
    | X1 != X0 ),
    inference(instantiation,[status(thm)],[c_2145])).

cnf(c_16702,plain,
    ( r1_tarski(X0,u1_struct_0(sK0))
    | ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))
    | X0 != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_8946])).

cnf(c_16703,plain,
    ( X0 != u1_struct_0(sK0)
    | r1_tarski(X0,u1_struct_0(sK0)) = iProver_top
    | r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16702])).

cnf(c_16705,plain,
    ( k1_xboole_0 != u1_struct_0(sK0)
    | r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k1_xboole_0,u1_struct_0(sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_16703])).

cnf(c_17238,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16488,c_132,c_136,c_4861,c_10576,c_10929,c_14800,c_16536,c_16541,c_16607,c_16705])).

cnf(c_17618,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_17612,c_17238])).

cnf(c_17984,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_11327,c_17618])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:13:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.74/1.47  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.74/1.47  
% 7.74/1.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.74/1.47  
% 7.74/1.47  ------  iProver source info
% 7.74/1.47  
% 7.74/1.47  git: date: 2020-06-30 10:37:57 +0100
% 7.74/1.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.74/1.47  git: non_committed_changes: false
% 7.74/1.47  git: last_make_outside_of_git: false
% 7.74/1.47  
% 7.74/1.47  ------ 
% 7.74/1.47  
% 7.74/1.47  ------ Input Options
% 7.74/1.47  
% 7.74/1.47  --out_options                           all
% 7.74/1.47  --tptp_safe_out                         true
% 7.74/1.47  --problem_path                          ""
% 7.74/1.47  --include_path                          ""
% 7.74/1.47  --clausifier                            res/vclausify_rel
% 7.74/1.47  --clausifier_options                    ""
% 7.74/1.47  --stdin                                 false
% 7.74/1.47  --stats_out                             all
% 7.74/1.47  
% 7.74/1.47  ------ General Options
% 7.74/1.47  
% 7.74/1.47  --fof                                   false
% 7.74/1.47  --time_out_real                         305.
% 7.74/1.47  --time_out_virtual                      -1.
% 7.74/1.47  --symbol_type_check                     false
% 7.74/1.47  --clausify_out                          false
% 7.74/1.47  --sig_cnt_out                           false
% 7.74/1.47  --trig_cnt_out                          false
% 7.74/1.47  --trig_cnt_out_tolerance                1.
% 7.74/1.47  --trig_cnt_out_sk_spl                   false
% 7.74/1.47  --abstr_cl_out                          false
% 7.74/1.47  
% 7.74/1.47  ------ Global Options
% 7.74/1.47  
% 7.74/1.47  --schedule                              default
% 7.74/1.47  --add_important_lit                     false
% 7.74/1.47  --prop_solver_per_cl                    1000
% 7.74/1.47  --min_unsat_core                        false
% 7.74/1.47  --soft_assumptions                      false
% 7.74/1.47  --soft_lemma_size                       3
% 7.74/1.47  --prop_impl_unit_size                   0
% 7.74/1.47  --prop_impl_unit                        []
% 7.74/1.47  --share_sel_clauses                     true
% 7.74/1.47  --reset_solvers                         false
% 7.74/1.47  --bc_imp_inh                            [conj_cone]
% 7.74/1.47  --conj_cone_tolerance                   3.
% 7.74/1.47  --extra_neg_conj                        none
% 7.74/1.47  --large_theory_mode                     true
% 7.74/1.47  --prolific_symb_bound                   200
% 7.74/1.47  --lt_threshold                          2000
% 7.74/1.47  --clause_weak_htbl                      true
% 7.74/1.47  --gc_record_bc_elim                     false
% 7.74/1.47  
% 7.74/1.47  ------ Preprocessing Options
% 7.74/1.47  
% 7.74/1.47  --preprocessing_flag                    true
% 7.74/1.47  --time_out_prep_mult                    0.1
% 7.74/1.47  --splitting_mode                        input
% 7.74/1.47  --splitting_grd                         true
% 7.74/1.47  --splitting_cvd                         false
% 7.74/1.47  --splitting_cvd_svl                     false
% 7.74/1.47  --splitting_nvd                         32
% 7.74/1.47  --sub_typing                            true
% 7.74/1.47  --prep_gs_sim                           true
% 7.74/1.47  --prep_unflatten                        true
% 7.74/1.47  --prep_res_sim                          true
% 7.74/1.47  --prep_upred                            true
% 7.74/1.47  --prep_sem_filter                       exhaustive
% 7.74/1.47  --prep_sem_filter_out                   false
% 7.74/1.47  --pred_elim                             true
% 7.74/1.47  --res_sim_input                         true
% 7.74/1.47  --eq_ax_congr_red                       true
% 7.74/1.47  --pure_diseq_elim                       true
% 7.74/1.47  --brand_transform                       false
% 7.74/1.47  --non_eq_to_eq                          false
% 7.74/1.47  --prep_def_merge                        true
% 7.74/1.47  --prep_def_merge_prop_impl              false
% 7.74/1.47  --prep_def_merge_mbd                    true
% 7.74/1.47  --prep_def_merge_tr_red                 false
% 7.74/1.47  --prep_def_merge_tr_cl                  false
% 7.74/1.47  --smt_preprocessing                     true
% 7.74/1.47  --smt_ac_axioms                         fast
% 7.74/1.47  --preprocessed_out                      false
% 7.74/1.47  --preprocessed_stats                    false
% 7.74/1.47  
% 7.74/1.47  ------ Abstraction refinement Options
% 7.74/1.47  
% 7.74/1.47  --abstr_ref                             []
% 7.74/1.47  --abstr_ref_prep                        false
% 7.74/1.47  --abstr_ref_until_sat                   false
% 7.74/1.47  --abstr_ref_sig_restrict                funpre
% 7.74/1.47  --abstr_ref_af_restrict_to_split_sk     false
% 7.74/1.47  --abstr_ref_under                       []
% 7.74/1.47  
% 7.74/1.47  ------ SAT Options
% 7.74/1.47  
% 7.74/1.47  --sat_mode                              false
% 7.74/1.47  --sat_fm_restart_options                ""
% 7.74/1.47  --sat_gr_def                            false
% 7.74/1.47  --sat_epr_types                         true
% 7.74/1.47  --sat_non_cyclic_types                  false
% 7.74/1.47  --sat_finite_models                     false
% 7.74/1.47  --sat_fm_lemmas                         false
% 7.74/1.47  --sat_fm_prep                           false
% 7.74/1.47  --sat_fm_uc_incr                        true
% 7.74/1.47  --sat_out_model                         small
% 7.74/1.47  --sat_out_clauses                       false
% 7.74/1.47  
% 7.74/1.47  ------ QBF Options
% 7.74/1.47  
% 7.74/1.47  --qbf_mode                              false
% 7.74/1.47  --qbf_elim_univ                         false
% 7.74/1.47  --qbf_dom_inst                          none
% 7.74/1.47  --qbf_dom_pre_inst                      false
% 7.74/1.47  --qbf_sk_in                             false
% 7.74/1.47  --qbf_pred_elim                         true
% 7.74/1.47  --qbf_split                             512
% 7.74/1.47  
% 7.74/1.47  ------ BMC1 Options
% 7.74/1.47  
% 7.74/1.47  --bmc1_incremental                      false
% 7.74/1.47  --bmc1_axioms                           reachable_all
% 7.74/1.47  --bmc1_min_bound                        0
% 7.74/1.47  --bmc1_max_bound                        -1
% 7.74/1.47  --bmc1_max_bound_default                -1
% 7.74/1.47  --bmc1_symbol_reachability              true
% 7.74/1.47  --bmc1_property_lemmas                  false
% 7.74/1.47  --bmc1_k_induction                      false
% 7.74/1.47  --bmc1_non_equiv_states                 false
% 7.74/1.47  --bmc1_deadlock                         false
% 7.74/1.47  --bmc1_ucm                              false
% 7.74/1.47  --bmc1_add_unsat_core                   none
% 7.74/1.47  --bmc1_unsat_core_children              false
% 7.74/1.47  --bmc1_unsat_core_extrapolate_axioms    false
% 7.74/1.47  --bmc1_out_stat                         full
% 7.74/1.47  --bmc1_ground_init                      false
% 7.74/1.47  --bmc1_pre_inst_next_state              false
% 7.74/1.47  --bmc1_pre_inst_state                   false
% 7.74/1.47  --bmc1_pre_inst_reach_state             false
% 7.74/1.47  --bmc1_out_unsat_core                   false
% 7.74/1.47  --bmc1_aig_witness_out                  false
% 7.74/1.47  --bmc1_verbose                          false
% 7.74/1.47  --bmc1_dump_clauses_tptp                false
% 7.74/1.47  --bmc1_dump_unsat_core_tptp             false
% 7.74/1.47  --bmc1_dump_file                        -
% 7.74/1.47  --bmc1_ucm_expand_uc_limit              128
% 7.74/1.47  --bmc1_ucm_n_expand_iterations          6
% 7.74/1.47  --bmc1_ucm_extend_mode                  1
% 7.74/1.47  --bmc1_ucm_init_mode                    2
% 7.74/1.47  --bmc1_ucm_cone_mode                    none
% 7.74/1.47  --bmc1_ucm_reduced_relation_type        0
% 7.74/1.47  --bmc1_ucm_relax_model                  4
% 7.74/1.47  --bmc1_ucm_full_tr_after_sat            true
% 7.74/1.47  --bmc1_ucm_expand_neg_assumptions       false
% 7.74/1.47  --bmc1_ucm_layered_model                none
% 7.74/1.47  --bmc1_ucm_max_lemma_size               10
% 7.74/1.47  
% 7.74/1.47  ------ AIG Options
% 7.74/1.47  
% 7.74/1.47  --aig_mode                              false
% 7.74/1.47  
% 7.74/1.47  ------ Instantiation Options
% 7.74/1.47  
% 7.74/1.47  --instantiation_flag                    true
% 7.74/1.47  --inst_sos_flag                         true
% 7.74/1.47  --inst_sos_phase                        true
% 7.74/1.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.74/1.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.74/1.47  --inst_lit_sel_side                     num_symb
% 7.74/1.47  --inst_solver_per_active                1400
% 7.74/1.47  --inst_solver_calls_frac                1.
% 7.74/1.47  --inst_passive_queue_type               priority_queues
% 7.74/1.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.74/1.47  --inst_passive_queues_freq              [25;2]
% 7.74/1.47  --inst_dismatching                      true
% 7.74/1.47  --inst_eager_unprocessed_to_passive     true
% 7.74/1.47  --inst_prop_sim_given                   true
% 7.74/1.47  --inst_prop_sim_new                     false
% 7.74/1.47  --inst_subs_new                         false
% 7.74/1.47  --inst_eq_res_simp                      false
% 7.74/1.47  --inst_subs_given                       false
% 7.74/1.47  --inst_orphan_elimination               true
% 7.74/1.47  --inst_learning_loop_flag               true
% 7.74/1.47  --inst_learning_start                   3000
% 7.74/1.47  --inst_learning_factor                  2
% 7.74/1.47  --inst_start_prop_sim_after_learn       3
% 7.74/1.47  --inst_sel_renew                        solver
% 7.74/1.47  --inst_lit_activity_flag                true
% 7.74/1.47  --inst_restr_to_given                   false
% 7.74/1.47  --inst_activity_threshold               500
% 7.74/1.47  --inst_out_proof                        true
% 7.74/1.47  
% 7.74/1.47  ------ Resolution Options
% 7.74/1.47  
% 7.74/1.47  --resolution_flag                       true
% 7.74/1.47  --res_lit_sel                           adaptive
% 7.74/1.47  --res_lit_sel_side                      none
% 7.74/1.47  --res_ordering                          kbo
% 7.74/1.47  --res_to_prop_solver                    active
% 7.74/1.47  --res_prop_simpl_new                    false
% 7.74/1.47  --res_prop_simpl_given                  true
% 7.74/1.47  --res_passive_queue_type                priority_queues
% 7.74/1.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.74/1.47  --res_passive_queues_freq               [15;5]
% 7.74/1.47  --res_forward_subs                      full
% 7.74/1.47  --res_backward_subs                     full
% 7.74/1.47  --res_forward_subs_resolution           true
% 7.74/1.47  --res_backward_subs_resolution          true
% 7.74/1.47  --res_orphan_elimination                true
% 7.74/1.47  --res_time_limit                        2.
% 7.74/1.47  --res_out_proof                         true
% 7.74/1.47  
% 7.74/1.47  ------ Superposition Options
% 7.74/1.47  
% 7.74/1.47  --superposition_flag                    true
% 7.74/1.47  --sup_passive_queue_type                priority_queues
% 7.74/1.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.74/1.47  --sup_passive_queues_freq               [8;1;4]
% 7.74/1.47  --demod_completeness_check              fast
% 7.74/1.47  --demod_use_ground                      true
% 7.74/1.47  --sup_to_prop_solver                    passive
% 7.74/1.47  --sup_prop_simpl_new                    true
% 7.74/1.47  --sup_prop_simpl_given                  true
% 7.74/1.47  --sup_fun_splitting                     true
% 7.74/1.47  --sup_smt_interval                      50000
% 7.74/1.47  
% 7.74/1.47  ------ Superposition Simplification Setup
% 7.74/1.47  
% 7.74/1.47  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.74/1.47  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.74/1.47  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.74/1.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.74/1.47  --sup_full_triv                         [TrivRules;PropSubs]
% 7.74/1.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.74/1.47  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.74/1.47  --sup_immed_triv                        [TrivRules]
% 7.74/1.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.74/1.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.74/1.47  --sup_immed_bw_main                     []
% 7.74/1.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.74/1.47  --sup_input_triv                        [Unflattening;TrivRules]
% 7.74/1.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.74/1.47  --sup_input_bw                          []
% 7.74/1.47  
% 7.74/1.47  ------ Combination Options
% 7.74/1.47  
% 7.74/1.47  --comb_res_mult                         3
% 7.74/1.47  --comb_sup_mult                         2
% 7.74/1.47  --comb_inst_mult                        10
% 7.74/1.47  
% 7.74/1.47  ------ Debug Options
% 7.74/1.47  
% 7.74/1.47  --dbg_backtrace                         false
% 7.74/1.47  --dbg_dump_prop_clauses                 false
% 7.74/1.47  --dbg_dump_prop_clauses_file            -
% 7.74/1.47  --dbg_out_stat                          false
% 7.74/1.47  ------ Parsing...
% 7.74/1.47  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.74/1.47  
% 7.74/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.74/1.47  
% 7.74/1.47  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.74/1.47  
% 7.74/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.74/1.47  ------ Proving...
% 7.74/1.47  ------ Problem Properties 
% 7.74/1.47  
% 7.74/1.47  
% 7.74/1.47  clauses                                 38
% 7.74/1.47  conjectures                             13
% 7.74/1.47  EPR                                     12
% 7.74/1.47  Horn                                    32
% 7.74/1.47  unary                                   15
% 7.74/1.47  binary                                  7
% 7.74/1.47  lits                                    114
% 7.74/1.47  lits eq                                 15
% 7.74/1.47  fd_pure                                 0
% 7.74/1.47  fd_pseudo                               0
% 7.74/1.47  fd_cond                                 3
% 7.74/1.47  fd_pseudo_cond                          3
% 7.74/1.47  AC symbols                              0
% 7.74/1.47  
% 7.74/1.47  ------ Schedule dynamic 5 is on 
% 7.74/1.47  
% 7.74/1.47  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.74/1.47  
% 7.74/1.47  
% 7.74/1.47  ------ 
% 7.74/1.47  Current options:
% 7.74/1.47  ------ 
% 7.74/1.47  
% 7.74/1.47  ------ Input Options
% 7.74/1.47  
% 7.74/1.47  --out_options                           all
% 7.74/1.47  --tptp_safe_out                         true
% 7.74/1.47  --problem_path                          ""
% 7.74/1.47  --include_path                          ""
% 7.74/1.47  --clausifier                            res/vclausify_rel
% 7.74/1.47  --clausifier_options                    ""
% 7.74/1.47  --stdin                                 false
% 7.74/1.47  --stats_out                             all
% 7.74/1.47  
% 7.74/1.47  ------ General Options
% 7.74/1.47  
% 7.74/1.47  --fof                                   false
% 7.74/1.47  --time_out_real                         305.
% 7.74/1.47  --time_out_virtual                      -1.
% 7.74/1.47  --symbol_type_check                     false
% 7.74/1.47  --clausify_out                          false
% 7.74/1.47  --sig_cnt_out                           false
% 7.74/1.47  --trig_cnt_out                          false
% 7.74/1.47  --trig_cnt_out_tolerance                1.
% 7.74/1.47  --trig_cnt_out_sk_spl                   false
% 7.74/1.47  --abstr_cl_out                          false
% 7.74/1.47  
% 7.74/1.47  ------ Global Options
% 7.74/1.47  
% 7.74/1.47  --schedule                              default
% 7.74/1.47  --add_important_lit                     false
% 7.74/1.47  --prop_solver_per_cl                    1000
% 7.74/1.47  --min_unsat_core                        false
% 7.74/1.47  --soft_assumptions                      false
% 7.74/1.47  --soft_lemma_size                       3
% 7.74/1.47  --prop_impl_unit_size                   0
% 7.74/1.47  --prop_impl_unit                        []
% 7.74/1.47  --share_sel_clauses                     true
% 7.74/1.47  --reset_solvers                         false
% 7.74/1.47  --bc_imp_inh                            [conj_cone]
% 7.74/1.47  --conj_cone_tolerance                   3.
% 7.74/1.47  --extra_neg_conj                        none
% 7.74/1.47  --large_theory_mode                     true
% 7.74/1.47  --prolific_symb_bound                   200
% 7.74/1.47  --lt_threshold                          2000
% 7.74/1.47  --clause_weak_htbl                      true
% 7.74/1.47  --gc_record_bc_elim                     false
% 7.74/1.47  
% 7.74/1.47  ------ Preprocessing Options
% 7.74/1.47  
% 7.74/1.47  --preprocessing_flag                    true
% 7.74/1.47  --time_out_prep_mult                    0.1
% 7.74/1.47  --splitting_mode                        input
% 7.74/1.47  --splitting_grd                         true
% 7.74/1.47  --splitting_cvd                         false
% 7.74/1.47  --splitting_cvd_svl                     false
% 7.74/1.47  --splitting_nvd                         32
% 7.74/1.47  --sub_typing                            true
% 7.74/1.47  --prep_gs_sim                           true
% 7.74/1.47  --prep_unflatten                        true
% 7.74/1.47  --prep_res_sim                          true
% 7.74/1.47  --prep_upred                            true
% 7.74/1.47  --prep_sem_filter                       exhaustive
% 7.74/1.47  --prep_sem_filter_out                   false
% 7.74/1.47  --pred_elim                             true
% 7.74/1.47  --res_sim_input                         true
% 7.74/1.47  --eq_ax_congr_red                       true
% 7.74/1.47  --pure_diseq_elim                       true
% 7.74/1.47  --brand_transform                       false
% 7.74/1.47  --non_eq_to_eq                          false
% 7.74/1.47  --prep_def_merge                        true
% 7.74/1.47  --prep_def_merge_prop_impl              false
% 7.74/1.47  --prep_def_merge_mbd                    true
% 7.74/1.47  --prep_def_merge_tr_red                 false
% 7.74/1.47  --prep_def_merge_tr_cl                  false
% 7.74/1.47  --smt_preprocessing                     true
% 7.74/1.47  --smt_ac_axioms                         fast
% 7.74/1.47  --preprocessed_out                      false
% 7.74/1.47  --preprocessed_stats                    false
% 7.74/1.47  
% 7.74/1.47  ------ Abstraction refinement Options
% 7.74/1.47  
% 7.74/1.47  --abstr_ref                             []
% 7.74/1.47  --abstr_ref_prep                        false
% 7.74/1.47  --abstr_ref_until_sat                   false
% 7.74/1.47  --abstr_ref_sig_restrict                funpre
% 7.74/1.47  --abstr_ref_af_restrict_to_split_sk     false
% 7.74/1.47  --abstr_ref_under                       []
% 7.74/1.47  
% 7.74/1.47  ------ SAT Options
% 7.74/1.47  
% 7.74/1.47  --sat_mode                              false
% 7.74/1.47  --sat_fm_restart_options                ""
% 7.74/1.47  --sat_gr_def                            false
% 7.74/1.47  --sat_epr_types                         true
% 7.74/1.47  --sat_non_cyclic_types                  false
% 7.74/1.47  --sat_finite_models                     false
% 7.74/1.47  --sat_fm_lemmas                         false
% 7.74/1.47  --sat_fm_prep                           false
% 7.74/1.47  --sat_fm_uc_incr                        true
% 7.74/1.47  --sat_out_model                         small
% 7.74/1.47  --sat_out_clauses                       false
% 7.74/1.47  
% 7.74/1.47  ------ QBF Options
% 7.74/1.47  
% 7.74/1.47  --qbf_mode                              false
% 7.74/1.47  --qbf_elim_univ                         false
% 7.74/1.47  --qbf_dom_inst                          none
% 7.74/1.47  --qbf_dom_pre_inst                      false
% 7.74/1.47  --qbf_sk_in                             false
% 7.74/1.47  --qbf_pred_elim                         true
% 7.74/1.47  --qbf_split                             512
% 7.74/1.47  
% 7.74/1.47  ------ BMC1 Options
% 7.74/1.47  
% 7.74/1.47  --bmc1_incremental                      false
% 7.74/1.47  --bmc1_axioms                           reachable_all
% 7.74/1.47  --bmc1_min_bound                        0
% 7.74/1.47  --bmc1_max_bound                        -1
% 7.74/1.47  --bmc1_max_bound_default                -1
% 7.74/1.47  --bmc1_symbol_reachability              true
% 7.74/1.47  --bmc1_property_lemmas                  false
% 7.74/1.47  --bmc1_k_induction                      false
% 7.74/1.47  --bmc1_non_equiv_states                 false
% 7.74/1.47  --bmc1_deadlock                         false
% 7.74/1.47  --bmc1_ucm                              false
% 7.74/1.47  --bmc1_add_unsat_core                   none
% 7.74/1.47  --bmc1_unsat_core_children              false
% 7.74/1.47  --bmc1_unsat_core_extrapolate_axioms    false
% 7.74/1.47  --bmc1_out_stat                         full
% 7.74/1.47  --bmc1_ground_init                      false
% 7.74/1.47  --bmc1_pre_inst_next_state              false
% 7.74/1.47  --bmc1_pre_inst_state                   false
% 7.74/1.47  --bmc1_pre_inst_reach_state             false
% 7.74/1.47  --bmc1_out_unsat_core                   false
% 7.74/1.47  --bmc1_aig_witness_out                  false
% 7.74/1.47  --bmc1_verbose                          false
% 7.74/1.47  --bmc1_dump_clauses_tptp                false
% 7.74/1.47  --bmc1_dump_unsat_core_tptp             false
% 7.74/1.47  --bmc1_dump_file                        -
% 7.74/1.47  --bmc1_ucm_expand_uc_limit              128
% 7.74/1.47  --bmc1_ucm_n_expand_iterations          6
% 7.74/1.47  --bmc1_ucm_extend_mode                  1
% 7.74/1.47  --bmc1_ucm_init_mode                    2
% 7.74/1.47  --bmc1_ucm_cone_mode                    none
% 7.74/1.47  --bmc1_ucm_reduced_relation_type        0
% 7.74/1.47  --bmc1_ucm_relax_model                  4
% 7.74/1.47  --bmc1_ucm_full_tr_after_sat            true
% 7.74/1.47  --bmc1_ucm_expand_neg_assumptions       false
% 7.74/1.47  --bmc1_ucm_layered_model                none
% 7.74/1.47  --bmc1_ucm_max_lemma_size               10
% 7.74/1.47  
% 7.74/1.47  ------ AIG Options
% 7.74/1.47  
% 7.74/1.47  --aig_mode                              false
% 7.74/1.47  
% 7.74/1.47  ------ Instantiation Options
% 7.74/1.47  
% 7.74/1.47  --instantiation_flag                    true
% 7.74/1.47  --inst_sos_flag                         true
% 7.74/1.47  --inst_sos_phase                        true
% 7.74/1.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.74/1.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.74/1.47  --inst_lit_sel_side                     none
% 7.74/1.47  --inst_solver_per_active                1400
% 7.74/1.47  --inst_solver_calls_frac                1.
% 7.74/1.47  --inst_passive_queue_type               priority_queues
% 7.74/1.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.74/1.47  --inst_passive_queues_freq              [25;2]
% 7.74/1.47  --inst_dismatching                      true
% 7.74/1.47  --inst_eager_unprocessed_to_passive     true
% 7.74/1.47  --inst_prop_sim_given                   true
% 7.74/1.47  --inst_prop_sim_new                     false
% 7.74/1.47  --inst_subs_new                         false
% 7.74/1.47  --inst_eq_res_simp                      false
% 7.74/1.47  --inst_subs_given                       false
% 7.74/1.47  --inst_orphan_elimination               true
% 7.74/1.47  --inst_learning_loop_flag               true
% 7.74/1.47  --inst_learning_start                   3000
% 7.74/1.47  --inst_learning_factor                  2
% 7.74/1.47  --inst_start_prop_sim_after_learn       3
% 7.74/1.47  --inst_sel_renew                        solver
% 7.74/1.47  --inst_lit_activity_flag                true
% 7.74/1.47  --inst_restr_to_given                   false
% 7.74/1.47  --inst_activity_threshold               500
% 7.74/1.47  --inst_out_proof                        true
% 7.74/1.47  
% 7.74/1.47  ------ Resolution Options
% 7.74/1.47  
% 7.74/1.47  --resolution_flag                       false
% 7.74/1.47  --res_lit_sel                           adaptive
% 7.74/1.47  --res_lit_sel_side                      none
% 7.74/1.47  --res_ordering                          kbo
% 7.74/1.47  --res_to_prop_solver                    active
% 7.74/1.47  --res_prop_simpl_new                    false
% 7.74/1.47  --res_prop_simpl_given                  true
% 7.74/1.47  --res_passive_queue_type                priority_queues
% 7.74/1.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.74/1.47  --res_passive_queues_freq               [15;5]
% 7.74/1.47  --res_forward_subs                      full
% 7.74/1.47  --res_backward_subs                     full
% 7.74/1.47  --res_forward_subs_resolution           true
% 7.74/1.47  --res_backward_subs_resolution          true
% 7.74/1.47  --res_orphan_elimination                true
% 7.74/1.47  --res_time_limit                        2.
% 7.74/1.47  --res_out_proof                         true
% 7.74/1.47  
% 7.74/1.47  ------ Superposition Options
% 7.74/1.47  
% 7.74/1.47  --superposition_flag                    true
% 7.74/1.47  --sup_passive_queue_type                priority_queues
% 7.74/1.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.74/1.47  --sup_passive_queues_freq               [8;1;4]
% 7.74/1.47  --demod_completeness_check              fast
% 7.74/1.47  --demod_use_ground                      true
% 7.74/1.47  --sup_to_prop_solver                    passive
% 7.74/1.47  --sup_prop_simpl_new                    true
% 7.74/1.47  --sup_prop_simpl_given                  true
% 7.74/1.47  --sup_fun_splitting                     true
% 7.74/1.47  --sup_smt_interval                      50000
% 7.74/1.47  
% 7.74/1.47  ------ Superposition Simplification Setup
% 7.74/1.47  
% 7.74/1.47  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.74/1.47  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.74/1.47  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.74/1.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.74/1.47  --sup_full_triv                         [TrivRules;PropSubs]
% 7.74/1.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.74/1.47  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.74/1.47  --sup_immed_triv                        [TrivRules]
% 7.74/1.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.74/1.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.74/1.47  --sup_immed_bw_main                     []
% 7.74/1.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.74/1.47  --sup_input_triv                        [Unflattening;TrivRules]
% 7.74/1.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.74/1.47  --sup_input_bw                          []
% 7.74/1.47  
% 7.74/1.47  ------ Combination Options
% 7.74/1.47  
% 7.74/1.47  --comb_res_mult                         3
% 7.74/1.47  --comb_sup_mult                         2
% 7.74/1.47  --comb_inst_mult                        10
% 7.74/1.47  
% 7.74/1.47  ------ Debug Options
% 7.74/1.47  
% 7.74/1.47  --dbg_backtrace                         false
% 7.74/1.47  --dbg_dump_prop_clauses                 false
% 7.74/1.47  --dbg_dump_prop_clauses_file            -
% 7.74/1.47  --dbg_out_stat                          false
% 7.74/1.47  
% 7.74/1.47  
% 7.74/1.47  
% 7.74/1.47  
% 7.74/1.47  ------ Proving...
% 7.74/1.47  
% 7.74/1.47  
% 7.74/1.47  % SZS status Theorem for theBenchmark.p
% 7.74/1.47  
% 7.74/1.47   Resolution empty clause
% 7.74/1.47  
% 7.74/1.47  % SZS output start CNFRefutation for theBenchmark.p
% 7.74/1.47  
% 7.74/1.47  fof(f4,axiom,(
% 7.74/1.47    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 7.74/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.47  
% 7.74/1.47  fof(f69,plain,(
% 7.74/1.47    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 7.74/1.47    inference(cnf_transformation,[],[f4])).
% 7.74/1.47  
% 7.74/1.47  fof(f10,axiom,(
% 7.74/1.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 7.74/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.47  
% 7.74/1.47  fof(f32,plain,(
% 7.74/1.47    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.74/1.47    inference(ennf_transformation,[],[f10])).
% 7.74/1.47  
% 7.74/1.47  fof(f74,plain,(
% 7.74/1.47    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.74/1.47    inference(cnf_transformation,[],[f32])).
% 7.74/1.47  
% 7.74/1.47  fof(f13,axiom,(
% 7.74/1.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.74/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.47  
% 7.74/1.47  fof(f37,plain,(
% 7.74/1.47    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.74/1.47    inference(ennf_transformation,[],[f13])).
% 7.74/1.47  
% 7.74/1.47  fof(f38,plain,(
% 7.74/1.47    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.74/1.47    inference(flattening,[],[f37])).
% 7.74/1.47  
% 7.74/1.47  fof(f53,plain,(
% 7.74/1.47    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.74/1.47    inference(nnf_transformation,[],[f38])).
% 7.74/1.47  
% 7.74/1.47  fof(f81,plain,(
% 7.74/1.47    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.74/1.47    inference(cnf_transformation,[],[f53])).
% 7.74/1.47  
% 7.74/1.47  fof(f113,plain,(
% 7.74/1.47    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 7.74/1.47    inference(equality_resolution,[],[f81])).
% 7.74/1.47  
% 7.74/1.47  fof(f1,axiom,(
% 7.74/1.47    v1_xboole_0(k1_xboole_0)),
% 7.74/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.47  
% 7.74/1.47  fof(f64,plain,(
% 7.74/1.47    v1_xboole_0(k1_xboole_0)),
% 7.74/1.47    inference(cnf_transformation,[],[f1])).
% 7.74/1.47  
% 7.74/1.47  fof(f15,axiom,(
% 7.74/1.47    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 7.74/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.47  
% 7.74/1.47  fof(f87,plain,(
% 7.74/1.47    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.74/1.47    inference(cnf_transformation,[],[f15])).
% 7.74/1.47  
% 7.74/1.47  fof(f9,axiom,(
% 7.74/1.47    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 7.74/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.47  
% 7.74/1.47  fof(f31,plain,(
% 7.74/1.47    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 7.74/1.47    inference(ennf_transformation,[],[f9])).
% 7.74/1.47  
% 7.74/1.47  fof(f73,plain,(
% 7.74/1.47    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 7.74/1.47    inference(cnf_transformation,[],[f31])).
% 7.74/1.47  
% 7.74/1.47  fof(f3,axiom,(
% 7.74/1.47    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 7.74/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.47  
% 7.74/1.47  fof(f27,plain,(
% 7.74/1.47    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 7.74/1.47    inference(ennf_transformation,[],[f3])).
% 7.74/1.47  
% 7.74/1.47  fof(f68,plain,(
% 7.74/1.47    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 7.74/1.47    inference(cnf_transformation,[],[f27])).
% 7.74/1.47  
% 7.74/1.47  fof(f8,axiom,(
% 7.74/1.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.74/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.47  
% 7.74/1.47  fof(f25,plain,(
% 7.74/1.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.74/1.47    inference(pure_predicate_removal,[],[f8])).
% 7.74/1.47  
% 7.74/1.47  fof(f30,plain,(
% 7.74/1.47    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.74/1.47    inference(ennf_transformation,[],[f25])).
% 7.74/1.47  
% 7.74/1.47  fof(f72,plain,(
% 7.74/1.47    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.74/1.47    inference(cnf_transformation,[],[f30])).
% 7.74/1.47  
% 7.74/1.47  fof(f14,axiom,(
% 7.74/1.47    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 7.74/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.47  
% 7.74/1.47  fof(f39,plain,(
% 7.74/1.47    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.74/1.47    inference(ennf_transformation,[],[f14])).
% 7.74/1.47  
% 7.74/1.47  fof(f40,plain,(
% 7.74/1.47    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.74/1.47    inference(flattening,[],[f39])).
% 7.74/1.47  
% 7.74/1.47  fof(f54,plain,(
% 7.74/1.47    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.74/1.47    inference(nnf_transformation,[],[f40])).
% 7.74/1.47  
% 7.74/1.47  fof(f84,plain,(
% 7.74/1.47    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.74/1.47    inference(cnf_transformation,[],[f54])).
% 7.74/1.47  
% 7.74/1.47  fof(f7,axiom,(
% 7.74/1.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.74/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.47  
% 7.74/1.47  fof(f29,plain,(
% 7.74/1.47    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.74/1.47    inference(ennf_transformation,[],[f7])).
% 7.74/1.47  
% 7.74/1.47  fof(f71,plain,(
% 7.74/1.47    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.74/1.47    inference(cnf_transformation,[],[f29])).
% 7.74/1.47  
% 7.74/1.47  fof(f86,plain,(
% 7.74/1.47    ( ! [X0] : (v1_partfun1(k6_partfun1(X0),X0)) )),
% 7.74/1.47    inference(cnf_transformation,[],[f15])).
% 7.74/1.47  
% 7.74/1.47  fof(f21,conjecture,(
% 7.74/1.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 7.74/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.47  
% 7.74/1.47  fof(f22,negated_conjecture,(
% 7.74/1.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 7.74/1.47    inference(negated_conjecture,[],[f21])).
% 7.74/1.47  
% 7.74/1.47  fof(f49,plain,(
% 7.74/1.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 7.74/1.47    inference(ennf_transformation,[],[f22])).
% 7.74/1.47  
% 7.74/1.47  fof(f50,plain,(
% 7.74/1.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.74/1.47    inference(flattening,[],[f49])).
% 7.74/1.47  
% 7.74/1.47  fof(f57,plain,(
% 7.74/1.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.74/1.47    inference(nnf_transformation,[],[f50])).
% 7.74/1.47  
% 7.74/1.47  fof(f58,plain,(
% 7.74/1.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.74/1.47    inference(flattening,[],[f57])).
% 7.74/1.47  
% 7.74/1.47  fof(f62,plain,(
% 7.74/1.47    ( ! [X2,X0,X1] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => ((~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & sK3 = X2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(sK3))) )),
% 7.74/1.47    introduced(choice_axiom,[])).
% 7.74/1.47  
% 7.74/1.47  fof(f61,plain,(
% 7.74/1.47    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(sK2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK2,X0,X1)) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 7.74/1.47    introduced(choice_axiom,[])).
% 7.74/1.47  
% 7.74/1.47  fof(f60,plain,(
% 7.74/1.47    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(X2,X0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X2,X0,sK1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))) )),
% 7.74/1.47    introduced(choice_axiom,[])).
% 7.74/1.47  
% 7.74/1.47  fof(f59,plain,(
% 7.74/1.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 7.74/1.47    introduced(choice_axiom,[])).
% 7.74/1.47  
% 7.74/1.47  fof(f63,plain,(
% 7.74/1.47    ((((~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 7.74/1.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f58,f62,f61,f60,f59])).
% 7.74/1.47  
% 7.74/1.47  fof(f101,plain,(
% 7.74/1.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 7.74/1.47    inference(cnf_transformation,[],[f63])).
% 7.74/1.47  
% 7.74/1.47  fof(f105,plain,(
% 7.74/1.47    sK2 = sK3),
% 7.74/1.47    inference(cnf_transformation,[],[f63])).
% 7.74/1.47  
% 7.74/1.47  fof(f12,axiom,(
% 7.74/1.47    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 7.74/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.47  
% 7.74/1.47  fof(f35,plain,(
% 7.74/1.47    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 7.74/1.47    inference(ennf_transformation,[],[f12])).
% 7.74/1.47  
% 7.74/1.47  fof(f36,plain,(
% 7.74/1.47    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 7.74/1.47    inference(flattening,[],[f35])).
% 7.74/1.47  
% 7.74/1.47  fof(f77,plain,(
% 7.74/1.47    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 7.74/1.47    inference(cnf_transformation,[],[f36])).
% 7.74/1.47  
% 7.74/1.47  fof(f102,plain,(
% 7.74/1.47    v1_funct_1(sK3)),
% 7.74/1.47    inference(cnf_transformation,[],[f63])).
% 7.74/1.47  
% 7.74/1.47  fof(f100,plain,(
% 7.74/1.47    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 7.74/1.47    inference(cnf_transformation,[],[f63])).
% 7.74/1.47  
% 7.74/1.47  fof(f11,axiom,(
% 7.74/1.47    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 7.74/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.47  
% 7.74/1.47  fof(f33,plain,(
% 7.74/1.47    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 7.74/1.47    inference(ennf_transformation,[],[f11])).
% 7.74/1.47  
% 7.74/1.47  fof(f34,plain,(
% 7.74/1.47    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 7.74/1.47    inference(flattening,[],[f33])).
% 7.74/1.47  
% 7.74/1.47  fof(f75,plain,(
% 7.74/1.47    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 7.74/1.47    inference(cnf_transformation,[],[f34])).
% 7.74/1.47  
% 7.74/1.47  fof(f79,plain,(
% 7.74/1.47    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.74/1.47    inference(cnf_transformation,[],[f53])).
% 7.74/1.47  
% 7.74/1.47  fof(f114,plain,(
% 7.74/1.47    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 7.74/1.47    inference(equality_resolution,[],[f79])).
% 7.74/1.47  
% 7.74/1.47  fof(f2,axiom,(
% 7.74/1.47    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.74/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.47  
% 7.74/1.47  fof(f51,plain,(
% 7.74/1.47    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.74/1.47    inference(nnf_transformation,[],[f2])).
% 7.74/1.47  
% 7.74/1.47  fof(f52,plain,(
% 7.74/1.47    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.74/1.47    inference(flattening,[],[f51])).
% 7.74/1.47  
% 7.74/1.47  fof(f65,plain,(
% 7.74/1.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.74/1.47    inference(cnf_transformation,[],[f52])).
% 7.74/1.47  
% 7.74/1.47  fof(f109,plain,(
% 7.74/1.47    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.74/1.47    inference(equality_resolution,[],[f65])).
% 7.74/1.47  
% 7.74/1.47  fof(f103,plain,(
% 7.74/1.47    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 7.74/1.47    inference(cnf_transformation,[],[f63])).
% 7.74/1.47  
% 7.74/1.47  fof(f104,plain,(
% 7.74/1.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 7.74/1.47    inference(cnf_transformation,[],[f63])).
% 7.74/1.47  
% 7.74/1.47  fof(f19,axiom,(
% 7.74/1.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 7.74/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.47  
% 7.74/1.47  fof(f45,plain,(
% 7.74/1.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.74/1.47    inference(ennf_transformation,[],[f19])).
% 7.74/1.47  
% 7.74/1.47  fof(f46,plain,(
% 7.74/1.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.74/1.47    inference(flattening,[],[f45])).
% 7.74/1.47  
% 7.74/1.47  fof(f55,plain,(
% 7.74/1.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.74/1.47    inference(nnf_transformation,[],[f46])).
% 7.74/1.47  
% 7.74/1.47  fof(f91,plain,(
% 7.74/1.47    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.74/1.47    inference(cnf_transformation,[],[f55])).
% 7.74/1.47  
% 7.74/1.47  fof(f117,plain,(
% 7.74/1.47    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.74/1.47    inference(equality_resolution,[],[f91])).
% 7.74/1.47  
% 7.74/1.47  fof(f95,plain,(
% 7.74/1.47    v2_pre_topc(sK0)),
% 7.74/1.47    inference(cnf_transformation,[],[f63])).
% 7.74/1.47  
% 7.74/1.47  fof(f96,plain,(
% 7.74/1.47    l1_pre_topc(sK0)),
% 7.74/1.47    inference(cnf_transformation,[],[f63])).
% 7.74/1.47  
% 7.74/1.47  fof(f97,plain,(
% 7.74/1.47    v2_pre_topc(sK1)),
% 7.74/1.47    inference(cnf_transformation,[],[f63])).
% 7.74/1.47  
% 7.74/1.47  fof(f98,plain,(
% 7.74/1.47    l1_pre_topc(sK1)),
% 7.74/1.47    inference(cnf_transformation,[],[f63])).
% 7.74/1.47  
% 7.74/1.47  fof(f107,plain,(
% 7.74/1.47    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)),
% 7.74/1.47    inference(cnf_transformation,[],[f63])).
% 7.74/1.47  
% 7.74/1.47  fof(f106,plain,(
% 7.74/1.47    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)),
% 7.74/1.47    inference(cnf_transformation,[],[f63])).
% 7.74/1.47  
% 7.74/1.47  fof(f18,axiom,(
% 7.74/1.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 7.74/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.47  
% 7.74/1.47  fof(f23,plain,(
% 7.74/1.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 7.74/1.47    inference(pure_predicate_removal,[],[f18])).
% 7.74/1.47  
% 7.74/1.47  fof(f43,plain,(
% 7.74/1.47    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.74/1.47    inference(ennf_transformation,[],[f23])).
% 7.74/1.47  
% 7.74/1.47  fof(f44,plain,(
% 7.74/1.47    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.74/1.47    inference(flattening,[],[f43])).
% 7.74/1.47  
% 7.74/1.47  fof(f90,plain,(
% 7.74/1.47    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.74/1.47    inference(cnf_transformation,[],[f44])).
% 7.74/1.47  
% 7.74/1.47  fof(f16,axiom,(
% 7.74/1.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 7.74/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.47  
% 7.74/1.47  fof(f24,plain,(
% 7.74/1.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 7.74/1.47    inference(pure_predicate_removal,[],[f16])).
% 7.74/1.47  
% 7.74/1.47  fof(f41,plain,(
% 7.74/1.47    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 7.74/1.47    inference(ennf_transformation,[],[f24])).
% 7.74/1.47  
% 7.74/1.47  fof(f88,plain,(
% 7.74/1.47    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 7.74/1.47    inference(cnf_transformation,[],[f41])).
% 7.74/1.47  
% 7.74/1.47  fof(f17,axiom,(
% 7.74/1.47    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.74/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.47  
% 7.74/1.47  fof(f42,plain,(
% 7.74/1.47    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.74/1.47    inference(ennf_transformation,[],[f17])).
% 7.74/1.47  
% 7.74/1.47  fof(f89,plain,(
% 7.74/1.47    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 7.74/1.47    inference(cnf_transformation,[],[f42])).
% 7.74/1.47  
% 7.74/1.47  fof(f20,axiom,(
% 7.74/1.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 7.74/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.47  
% 7.74/1.47  fof(f47,plain,(
% 7.74/1.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.74/1.47    inference(ennf_transformation,[],[f20])).
% 7.74/1.47  
% 7.74/1.47  fof(f48,plain,(
% 7.74/1.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.74/1.47    inference(flattening,[],[f47])).
% 7.74/1.47  
% 7.74/1.47  fof(f56,plain,(
% 7.74/1.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.74/1.47    inference(nnf_transformation,[],[f48])).
% 7.74/1.47  
% 7.74/1.47  fof(f94,plain,(
% 7.74/1.47    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.74/1.47    inference(cnf_transformation,[],[f56])).
% 7.74/1.47  
% 7.74/1.47  fof(f118,plain,(
% 7.74/1.47    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.74/1.47    inference(equality_resolution,[],[f94])).
% 7.74/1.47  
% 7.74/1.47  fof(f93,plain,(
% 7.74/1.47    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.74/1.47    inference(cnf_transformation,[],[f56])).
% 7.74/1.47  
% 7.74/1.47  fof(f119,plain,(
% 7.74/1.47    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.74/1.47    inference(equality_resolution,[],[f93])).
% 7.74/1.47  
% 7.74/1.47  fof(f92,plain,(
% 7.74/1.47    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.74/1.47    inference(cnf_transformation,[],[f55])).
% 7.74/1.47  
% 7.74/1.47  fof(f116,plain,(
% 7.74/1.47    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.74/1.47    inference(equality_resolution,[],[f92])).
% 7.74/1.47  
% 7.74/1.47  fof(f67,plain,(
% 7.74/1.47    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.74/1.47    inference(cnf_transformation,[],[f52])).
% 7.74/1.47  
% 7.74/1.47  cnf(c_5,plain,
% 7.74/1.47      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 7.74/1.47      inference(cnf_transformation,[],[f69]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_3026,plain,
% 7.74/1.47      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.74/1.47      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_10,plain,
% 7.74/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.74/1.47      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.74/1.47      inference(cnf_transformation,[],[f74]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_3023,plain,
% 7.74/1.47      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.74/1.47      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.74/1.47      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_4059,plain,
% 7.74/1.47      ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 7.74/1.47      inference(superposition,[status(thm)],[c_3026,c_3023]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_16,plain,
% 7.74/1.47      ( v1_funct_2(X0,k1_xboole_0,X1)
% 7.74/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.74/1.47      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 7.74/1.47      inference(cnf_transformation,[],[f113]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_3019,plain,
% 7.74/1.47      ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
% 7.74/1.47      | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
% 7.74/1.47      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 7.74/1.47      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_6867,plain,
% 7.74/1.47      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 7.74/1.47      | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top
% 7.74/1.47      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 7.74/1.47      inference(superposition,[status(thm)],[c_4059,c_3019]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_0,plain,
% 7.74/1.47      ( v1_xboole_0(k1_xboole_0) ),
% 7.74/1.47      inference(cnf_transformation,[],[f64]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_3030,plain,
% 7.74/1.47      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.74/1.47      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_22,plain,
% 7.74/1.47      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 7.74/1.47      inference(cnf_transformation,[],[f87]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_3015,plain,
% 7.74/1.47      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 7.74/1.47      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_9,plain,
% 7.74/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.74/1.47      | ~ v1_xboole_0(X2)
% 7.74/1.47      | v1_xboole_0(X0) ),
% 7.74/1.47      inference(cnf_transformation,[],[f73]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_3024,plain,
% 7.74/1.47      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.74/1.47      | v1_xboole_0(X2) != iProver_top
% 7.74/1.47      | v1_xboole_0(X0) = iProver_top ),
% 7.74/1.47      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_4809,plain,
% 7.74/1.47      ( v1_xboole_0(X0) != iProver_top
% 7.74/1.47      | v1_xboole_0(k6_partfun1(X0)) = iProver_top ),
% 7.74/1.47      inference(superposition,[status(thm)],[c_3015,c_3024]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_4,plain,
% 7.74/1.47      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X0 = X1 ),
% 7.74/1.47      inference(cnf_transformation,[],[f68]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_3027,plain,
% 7.74/1.47      ( X0 = X1
% 7.74/1.47      | v1_xboole_0(X0) != iProver_top
% 7.74/1.47      | v1_xboole_0(X1) != iProver_top ),
% 7.74/1.47      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_8039,plain,
% 7.74/1.47      ( k6_partfun1(X0) = X1
% 7.74/1.47      | v1_xboole_0(X0) != iProver_top
% 7.74/1.47      | v1_xboole_0(X1) != iProver_top ),
% 7.74/1.47      inference(superposition,[status(thm)],[c_4809,c_3027]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_9235,plain,
% 7.74/1.47      ( k6_partfun1(k1_xboole_0) = X0 | v1_xboole_0(X0) != iProver_top ),
% 7.74/1.47      inference(superposition,[status(thm)],[c_3030,c_8039]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_9343,plain,
% 7.74/1.47      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 7.74/1.47      inference(superposition,[status(thm)],[c_3030,c_9235]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_8,plain,
% 7.74/1.47      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.74/1.47      inference(cnf_transformation,[],[f72]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_21,plain,
% 7.74/1.47      ( ~ v1_partfun1(X0,X1)
% 7.74/1.47      | ~ v4_relat_1(X0,X1)
% 7.74/1.47      | ~ v1_relat_1(X0)
% 7.74/1.47      | k1_relat_1(X0) = X1 ),
% 7.74/1.47      inference(cnf_transformation,[],[f84]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_583,plain,
% 7.74/1.47      ( ~ v1_partfun1(X0,X1)
% 7.74/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.74/1.47      | ~ v1_relat_1(X0)
% 7.74/1.47      | k1_relat_1(X0) = X1 ),
% 7.74/1.47      inference(resolution,[status(thm)],[c_8,c_21]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_7,plain,
% 7.74/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 7.74/1.47      inference(cnf_transformation,[],[f71]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_587,plain,
% 7.74/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.74/1.47      | ~ v1_partfun1(X0,X1)
% 7.74/1.47      | k1_relat_1(X0) = X1 ),
% 7.74/1.47      inference(global_propositional_subsumption,
% 7.74/1.47                [status(thm)],
% 7.74/1.47                [c_583,c_21,c_8,c_7]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_588,plain,
% 7.74/1.47      ( ~ v1_partfun1(X0,X1)
% 7.74/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.74/1.47      | k1_relat_1(X0) = X1 ),
% 7.74/1.47      inference(renaming,[status(thm)],[c_587]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_23,plain,
% 7.74/1.47      ( v1_partfun1(k6_partfun1(X0),X0) ),
% 7.74/1.47      inference(cnf_transformation,[],[f86]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_651,plain,
% 7.74/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.74/1.47      | X3 != X1
% 7.74/1.47      | k6_partfun1(X3) != X0
% 7.74/1.47      | k1_relat_1(X0) = X1 ),
% 7.74/1.47      inference(resolution_lifted,[status(thm)],[c_588,c_23]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_652,plain,
% 7.74/1.47      ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.74/1.47      | k1_relat_1(k6_partfun1(X0)) = X0 ),
% 7.74/1.47      inference(unflattening,[status(thm)],[c_651]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_2994,plain,
% 7.74/1.47      ( k1_relat_1(k6_partfun1(X0)) = X0
% 7.74/1.47      | m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.74/1.47      inference(predicate_to_equality,[status(thm)],[c_652]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_3563,plain,
% 7.74/1.47      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 7.74/1.47      inference(superposition,[status(thm)],[c_3015,c_2994]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_10355,plain,
% 7.74/1.47      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.74/1.47      inference(superposition,[status(thm)],[c_9343,c_3563]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_11321,plain,
% 7.74/1.47      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top
% 7.74/1.47      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 7.74/1.47      inference(global_propositional_subsumption,
% 7.74/1.47                [status(thm)],
% 7.74/1.47                [c_6867,c_10355]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_11327,plain,
% 7.74/1.47      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top ),
% 7.74/1.47      inference(superposition,[status(thm)],[c_3026,c_11321]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_37,negated_conjecture,
% 7.74/1.47      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 7.74/1.47      inference(cnf_transformation,[],[f101]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_3002,plain,
% 7.74/1.47      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 7.74/1.47      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_33,negated_conjecture,
% 7.74/1.47      ( sK2 = sK3 ),
% 7.74/1.47      inference(cnf_transformation,[],[f105]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_3033,plain,
% 7.74/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 7.74/1.47      inference(light_normalisation,[status(thm)],[c_3002,c_33]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_12,plain,
% 7.74/1.47      ( ~ v1_funct_2(X0,X1,X2)
% 7.74/1.47      | v1_partfun1(X0,X1)
% 7.74/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.74/1.47      | ~ v1_funct_1(X0)
% 7.74/1.47      | v1_xboole_0(X2) ),
% 7.74/1.47      inference(cnf_transformation,[],[f77]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_627,plain,
% 7.74/1.47      ( ~ v1_funct_2(X0,X1,X2)
% 7.74/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.74/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 7.74/1.47      | ~ v1_funct_1(X0)
% 7.74/1.47      | v1_xboole_0(X2)
% 7.74/1.47      | k1_relat_1(X0) = X1 ),
% 7.74/1.47      inference(resolution,[status(thm)],[c_12,c_588]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_629,plain,
% 7.74/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.74/1.47      | ~ v1_funct_2(X0,X1,X2)
% 7.74/1.47      | ~ v1_funct_1(X0)
% 7.74/1.47      | v1_xboole_0(X2)
% 7.74/1.47      | k1_relat_1(X0) = X1 ),
% 7.74/1.47      inference(global_propositional_subsumption,
% 7.74/1.47                [status(thm)],
% 7.74/1.47                [c_627,c_21,c_12,c_8,c_7]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_630,plain,
% 7.74/1.47      ( ~ v1_funct_2(X0,X1,X2)
% 7.74/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.74/1.47      | ~ v1_funct_1(X0)
% 7.74/1.47      | v1_xboole_0(X2)
% 7.74/1.47      | k1_relat_1(X0) = X1 ),
% 7.74/1.47      inference(renaming,[status(thm)],[c_629]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_2995,plain,
% 7.74/1.47      ( k1_relat_1(X0) = X1
% 7.74/1.47      | v1_funct_2(X0,X1,X2) != iProver_top
% 7.74/1.47      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.74/1.47      | v1_funct_1(X0) != iProver_top
% 7.74/1.47      | v1_xboole_0(X2) = iProver_top ),
% 7.74/1.47      inference(predicate_to_equality,[status(thm)],[c_630]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_3883,plain,
% 7.74/1.47      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.74/1.47      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.74/1.47      | v1_funct_1(sK3) != iProver_top
% 7.74/1.47      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 7.74/1.47      inference(superposition,[status(thm)],[c_3033,c_2995]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_36,negated_conjecture,
% 7.74/1.47      ( v1_funct_1(sK3) ),
% 7.74/1.47      inference(cnf_transformation,[],[f102]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_51,plain,
% 7.74/1.47      ( v1_funct_1(sK3) = iProver_top ),
% 7.74/1.47      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_38,negated_conjecture,
% 7.74/1.47      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 7.74/1.47      inference(cnf_transformation,[],[f100]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_3001,plain,
% 7.74/1.47      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 7.74/1.47      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_3032,plain,
% 7.74/1.47      ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 7.74/1.47      inference(light_normalisation,[status(thm)],[c_3001,c_33]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_4087,plain,
% 7.74/1.47      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.74/1.47      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 7.74/1.47      inference(global_propositional_subsumption,
% 7.74/1.47                [status(thm)],
% 7.74/1.47                [c_3883,c_51,c_3032]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_9238,plain,
% 7.74/1.47      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.74/1.47      | k6_partfun1(u1_struct_0(sK1)) = X0
% 7.74/1.47      | v1_xboole_0(X0) != iProver_top ),
% 7.74/1.47      inference(superposition,[status(thm)],[c_4087,c_8039]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_10147,plain,
% 7.74/1.47      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.74/1.47      | k6_partfun1(u1_struct_0(sK1)) = u1_struct_0(sK1) ),
% 7.74/1.47      inference(superposition,[status(thm)],[c_4087,c_9238]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_10211,plain,
% 7.74/1.47      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.74/1.47      | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top ),
% 7.74/1.47      inference(superposition,[status(thm)],[c_10147,c_3015]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_11,plain,
% 7.74/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.74/1.47      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 7.74/1.47      | ~ r1_tarski(k1_relat_1(X0),X3) ),
% 7.74/1.47      inference(cnf_transformation,[],[f75]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_3022,plain,
% 7.74/1.47      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.74/1.47      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
% 7.74/1.47      | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
% 7.74/1.47      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_10471,plain,
% 7.74/1.47      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.74/1.47      | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1)))) = iProver_top
% 7.74/1.47      | r1_tarski(k1_relat_1(u1_struct_0(sK1)),X0) != iProver_top ),
% 7.74/1.47      inference(superposition,[status(thm)],[c_10211,c_3022]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_18,plain,
% 7.74/1.47      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 7.74/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.74/1.47      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 7.74/1.47      inference(cnf_transformation,[],[f114]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_3017,plain,
% 7.74/1.47      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
% 7.74/1.47      | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
% 7.74/1.47      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 7.74/1.47      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_12691,plain,
% 7.74/1.47      ( k1_relset_1(k1_xboole_0,u1_struct_0(sK1),u1_struct_0(sK1)) = k1_xboole_0
% 7.74/1.47      | u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.74/1.47      | v1_funct_2(u1_struct_0(sK1),k1_xboole_0,u1_struct_0(sK1)) != iProver_top
% 7.74/1.47      | r1_tarski(k1_relat_1(u1_struct_0(sK1)),k1_xboole_0) != iProver_top ),
% 7.74/1.47      inference(superposition,[status(thm)],[c_10471,c_3017]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_3,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f109]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_131,plain,
% 7.74/1.47      ( r1_tarski(X0,X0) = iProver_top ),
% 7.74/1.47      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_133,plain,
% 7.74/1.47      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 7.74/1.47      inference(instantiation,[status(thm)],[c_131]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_2145,plain,
% 7.74/1.47      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 7.74/1.47      theory(equality) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_4954,plain,
% 7.74/1.47      ( ~ r1_tarski(X0,X1)
% 7.74/1.47      | r1_tarski(k1_relat_1(u1_struct_0(sK1)),X1)
% 7.74/1.47      | k1_relat_1(u1_struct_0(sK1)) != X0 ),
% 7.74/1.47      inference(instantiation,[status(thm)],[c_2145]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_4955,plain,
% 7.74/1.47      ( k1_relat_1(u1_struct_0(sK1)) != X0
% 7.74/1.47      | r1_tarski(X0,X1) != iProver_top
% 7.74/1.47      | r1_tarski(k1_relat_1(u1_struct_0(sK1)),X1) = iProver_top ),
% 7.74/1.47      inference(predicate_to_equality,[status(thm)],[c_4954]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_4957,plain,
% 7.74/1.47      ( k1_relat_1(u1_struct_0(sK1)) != k1_xboole_0
% 7.74/1.47      | r1_tarski(k1_relat_1(u1_struct_0(sK1)),k1_xboole_0) = iProver_top
% 7.74/1.47      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 7.74/1.47      inference(instantiation,[status(thm)],[c_4955]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_4091,plain,
% 7.74/1.47      ( u1_struct_0(sK1) = X0
% 7.74/1.47      | u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.74/1.47      | v1_xboole_0(X0) != iProver_top ),
% 7.74/1.47      inference(superposition,[status(thm)],[c_4087,c_3027]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_4542,plain,
% 7.74/1.47      ( u1_struct_0(sK1) = k1_xboole_0 | u1_struct_0(sK0) = k1_relat_1(sK3) ),
% 7.74/1.47      inference(superposition,[status(thm)],[c_3030,c_4091]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_10470,plain,
% 7.74/1.47      ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1)) = k1_relat_1(u1_struct_0(sK1))
% 7.74/1.47      | u1_struct_0(sK0) = k1_relat_1(sK3) ),
% 7.74/1.47      inference(superposition,[status(thm)],[c_10211,c_3023]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_10477,plain,
% 7.74/1.47      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_relat_1(u1_struct_0(sK1))
% 7.74/1.47      | u1_struct_0(sK0) = k1_relat_1(sK3) ),
% 7.74/1.47      inference(superposition,[status(thm)],[c_4542,c_10470]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_10481,plain,
% 7.74/1.47      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.74/1.47      | k1_relat_1(u1_struct_0(sK1)) = k1_xboole_0 ),
% 7.74/1.47      inference(demodulation,[status(thm)],[c_10477,c_4059,c_10355]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_17606,plain,
% 7.74/1.47      ( v1_funct_2(u1_struct_0(sK1),k1_xboole_0,u1_struct_0(sK1)) != iProver_top
% 7.74/1.47      | u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.74/1.47      | k1_relset_1(k1_xboole_0,u1_struct_0(sK1),u1_struct_0(sK1)) = k1_xboole_0 ),
% 7.74/1.47      inference(global_propositional_subsumption,
% 7.74/1.47                [status(thm)],
% 7.74/1.47                [c_12691,c_133,c_4957,c_10481]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_17607,plain,
% 7.74/1.47      ( k1_relset_1(k1_xboole_0,u1_struct_0(sK1),u1_struct_0(sK1)) = k1_xboole_0
% 7.74/1.47      | u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.74/1.47      | v1_funct_2(u1_struct_0(sK1),k1_xboole_0,u1_struct_0(sK1)) != iProver_top ),
% 7.74/1.47      inference(renaming,[status(thm)],[c_17606]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_4811,plain,
% 7.74/1.47      ( v1_xboole_0(u1_struct_0(sK1)) != iProver_top
% 7.74/1.47      | v1_xboole_0(sK3) = iProver_top ),
% 7.74/1.47      inference(superposition,[status(thm)],[c_3033,c_3024]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_4944,plain,
% 7.74/1.47      ( u1_struct_0(sK0) = k1_relat_1(sK3) | v1_xboole_0(sK3) = iProver_top ),
% 7.74/1.47      inference(superposition,[status(thm)],[c_4087,c_4811]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_3956,plain,
% 7.74/1.47      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 7.74/1.47      inference(superposition,[status(thm)],[c_3030,c_3027]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_7174,plain,
% 7.74/1.47      ( u1_struct_0(sK0) = k1_relat_1(sK3) | sK3 = k1_xboole_0 ),
% 7.74/1.47      inference(superposition,[status(thm)],[c_4944,c_3956]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_35,negated_conjecture,
% 7.74/1.47      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
% 7.74/1.47      inference(cnf_transformation,[],[f103]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_3004,plain,
% 7.74/1.47      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
% 7.74/1.47      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_15026,plain,
% 7.74/1.47      ( sK3 = k1_xboole_0
% 7.74/1.47      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
% 7.74/1.47      inference(superposition,[status(thm)],[c_7174,c_3004]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_34,negated_conjecture,
% 7.74/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
% 7.74/1.47      inference(cnf_transformation,[],[f104]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_3005,plain,
% 7.74/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
% 7.74/1.47      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_5531,plain,
% 7.74/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top
% 7.74/1.47      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 7.74/1.47      inference(superposition,[status(thm)],[c_3005,c_3022]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_5651,plain,
% 7.74/1.47      ( k1_relat_1(sK3) = X0
% 7.74/1.47      | v1_funct_2(sK3,X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.74/1.47      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 7.74/1.47      | v1_funct_1(sK3) != iProver_top
% 7.74/1.47      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
% 7.74/1.47      inference(superposition,[status(thm)],[c_5531,c_2995]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_11263,plain,
% 7.74/1.47      ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 7.74/1.47      | v1_funct_2(sK3,X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.74/1.47      | k1_relat_1(sK3) = X0
% 7.74/1.47      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
% 7.74/1.47      inference(global_propositional_subsumption,[status(thm)],[c_5651,c_51]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_11264,plain,
% 7.74/1.47      ( k1_relat_1(sK3) = X0
% 7.74/1.47      | v1_funct_2(sK3,X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.74/1.47      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 7.74/1.47      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
% 7.74/1.47      inference(renaming,[status(thm)],[c_11263]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_15286,plain,
% 7.74/1.47      ( u1_struct_0(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.74/1.47      | sK3 = k1_xboole_0
% 7.74/1.47      | r1_tarski(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0)))) != iProver_top
% 7.74/1.47      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
% 7.74/1.47      inference(superposition,[status(thm)],[c_15026,c_11264]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_3418,plain,
% 7.74/1.47      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(sK3) | sK3 = X0 ),
% 7.74/1.47      inference(instantiation,[status(thm)],[c_4]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_3420,plain,
% 7.74/1.47      ( ~ v1_xboole_0(sK3) | ~ v1_xboole_0(k1_xboole_0) | sK3 = k1_xboole_0 ),
% 7.74/1.47      inference(instantiation,[status(thm)],[c_3418]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_3363,plain,
% 7.74/1.47      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.74/1.47      | ~ v1_xboole_0(X1)
% 7.74/1.47      | v1_xboole_0(sK3) ),
% 7.74/1.47      inference(instantiation,[status(thm)],[c_9]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_3868,plain,
% 7.74/1.47      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 7.74/1.47      | ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 7.74/1.47      | v1_xboole_0(sK3) ),
% 7.74/1.47      inference(instantiation,[status(thm)],[c_3363]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_15070,plain,
% 7.74/1.47      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 7.74/1.47      | sK3 = k1_xboole_0 ),
% 7.74/1.47      inference(predicate_to_equality_rev,[status(thm)],[c_15026]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_15025,plain,
% 7.74/1.47      ( sK3 = k1_xboole_0
% 7.74/1.47      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
% 7.74/1.47      inference(superposition,[status(thm)],[c_7174,c_3005]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_15300,plain,
% 7.74/1.47      ( u1_struct_0(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.74/1.47      | sK3 = k1_xboole_0
% 7.74/1.47      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.74/1.47      | v1_funct_1(sK3) != iProver_top
% 7.74/1.47      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
% 7.74/1.47      inference(superposition,[status(thm)],[c_15025,c_2995]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_15304,plain,
% 7.74/1.47      ( ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 7.74/1.47      | ~ v1_funct_1(sK3)
% 7.74/1.47      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 7.74/1.47      | u1_struct_0(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.74/1.47      | sK3 = k1_xboole_0 ),
% 7.74/1.47      inference(predicate_to_equality_rev,[status(thm)],[c_15300]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_16296,plain,
% 7.74/1.47      ( u1_struct_0(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.74/1.47      | sK3 = k1_xboole_0 ),
% 7.74/1.47      inference(global_propositional_subsumption,
% 7.74/1.47                [status(thm)],
% 7.74/1.47                [c_15286,c_36,c_34,c_0,c_3420,c_3868,c_15070,c_15304]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_16323,plain,
% 7.74/1.47      ( sK3 = k1_xboole_0
% 7.74/1.47      | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
% 7.74/1.47      inference(superposition,[status(thm)],[c_16296,c_15026]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_28,plain,
% 7.74/1.47      ( ~ v5_pre_topc(X0,X1,X2)
% 7.74/1.47      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 7.74/1.47      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.74/1.47      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 7.74/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.74/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 7.74/1.47      | ~ v2_pre_topc(X1)
% 7.74/1.47      | ~ v2_pre_topc(X2)
% 7.74/1.47      | ~ l1_pre_topc(X1)
% 7.74/1.47      | ~ l1_pre_topc(X2)
% 7.74/1.47      | ~ v1_funct_1(X0) ),
% 7.74/1.47      inference(cnf_transformation,[],[f117]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_3010,plain,
% 7.74/1.47      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 7.74/1.47      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) = iProver_top
% 7.74/1.47      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 7.74/1.47      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
% 7.74/1.47      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 7.74/1.47      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
% 7.74/1.47      | v2_pre_topc(X1) != iProver_top
% 7.74/1.47      | v2_pre_topc(X2) != iProver_top
% 7.74/1.47      | l1_pre_topc(X1) != iProver_top
% 7.74/1.47      | l1_pre_topc(X2) != iProver_top
% 7.74/1.47      | v1_funct_1(X0) != iProver_top ),
% 7.74/1.47      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_6005,plain,
% 7.74/1.47      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 7.74/1.47      | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.74/1.47      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.74/1.47      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.74/1.47      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 7.74/1.47      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.74/1.47      | v2_pre_topc(sK0) != iProver_top
% 7.74/1.47      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.74/1.47      | l1_pre_topc(sK0) != iProver_top
% 7.74/1.47      | v1_funct_1(sK3) != iProver_top ),
% 7.74/1.47      inference(superposition,[status(thm)],[c_3005,c_3010]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_43,negated_conjecture,
% 7.74/1.47      ( v2_pre_topc(sK0) ),
% 7.74/1.47      inference(cnf_transformation,[],[f95]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_44,plain,
% 7.74/1.47      ( v2_pre_topc(sK0) = iProver_top ),
% 7.74/1.47      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_42,negated_conjecture,
% 7.74/1.47      ( l1_pre_topc(sK0) ),
% 7.74/1.47      inference(cnf_transformation,[],[f96]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_45,plain,
% 7.74/1.47      ( l1_pre_topc(sK0) = iProver_top ),
% 7.74/1.47      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_41,negated_conjecture,
% 7.74/1.47      ( v2_pre_topc(sK1) ),
% 7.74/1.47      inference(cnf_transformation,[],[f97]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_46,plain,
% 7.74/1.47      ( v2_pre_topc(sK1) = iProver_top ),
% 7.74/1.47      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_40,negated_conjecture,
% 7.74/1.47      ( l1_pre_topc(sK1) ),
% 7.74/1.47      inference(cnf_transformation,[],[f98]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_47,plain,
% 7.74/1.47      ( l1_pre_topc(sK1) = iProver_top ),
% 7.74/1.47      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_52,plain,
% 7.74/1.47      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
% 7.74/1.47      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_31,negated_conjecture,
% 7.74/1.47      ( ~ v5_pre_topc(sK2,sK0,sK1)
% 7.74/1.47      | ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 7.74/1.47      inference(cnf_transformation,[],[f107]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_3007,plain,
% 7.74/1.47      ( v5_pre_topc(sK2,sK0,sK1) != iProver_top
% 7.74/1.47      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 7.74/1.47      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_3035,plain,
% 7.74/1.47      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.74/1.47      | v5_pre_topc(sK3,sK0,sK1) != iProver_top ),
% 7.74/1.47      inference(light_normalisation,[status(thm)],[c_3007,c_33]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_32,negated_conjecture,
% 7.74/1.47      ( v5_pre_topc(sK2,sK0,sK1)
% 7.74/1.47      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 7.74/1.47      inference(cnf_transformation,[],[f106]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_3006,plain,
% 7.74/1.47      ( v5_pre_topc(sK2,sK0,sK1) = iProver_top
% 7.74/1.47      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
% 7.74/1.47      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_3034,plain,
% 7.74/1.47      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 7.74/1.47      | v5_pre_topc(sK3,sK0,sK1) = iProver_top ),
% 7.74/1.47      inference(light_normalisation,[status(thm)],[c_3006,c_33]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_26,plain,
% 7.74/1.47      ( ~ v2_pre_topc(X0)
% 7.74/1.47      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 7.74/1.47      | ~ l1_pre_topc(X0) ),
% 7.74/1.47      inference(cnf_transformation,[],[f90]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_3188,plain,
% 7.74/1.47      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 7.74/1.47      | ~ v2_pre_topc(sK1)
% 7.74/1.47      | ~ l1_pre_topc(sK1) ),
% 7.74/1.47      inference(instantiation,[status(thm)],[c_26]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_3189,plain,
% 7.74/1.47      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 7.74/1.47      | v2_pre_topc(sK1) != iProver_top
% 7.74/1.47      | l1_pre_topc(sK1) != iProver_top ),
% 7.74/1.47      inference(predicate_to_equality,[status(thm)],[c_3188]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_24,plain,
% 7.74/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 7.74/1.47      | l1_pre_topc(g1_pre_topc(X1,X0)) ),
% 7.74/1.47      inference(cnf_transformation,[],[f88]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_3446,plain,
% 7.74/1.47      ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 7.74/1.47      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 7.74/1.47      inference(instantiation,[status(thm)],[c_24]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_3447,plain,
% 7.74/1.47      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
% 7.74/1.47      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
% 7.74/1.47      inference(predicate_to_equality,[status(thm)],[c_3446]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_25,plain,
% 7.74/1.47      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 7.74/1.47      | ~ l1_pre_topc(X0) ),
% 7.74/1.47      inference(cnf_transformation,[],[f89]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_3660,plain,
% 7.74/1.47      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 7.74/1.47      | ~ l1_pre_topc(sK1) ),
% 7.74/1.47      inference(instantiation,[status(thm)],[c_25]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_3661,plain,
% 7.74/1.47      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
% 7.74/1.47      | l1_pre_topc(sK1) != iProver_top ),
% 7.74/1.47      inference(predicate_to_equality,[status(thm)],[c_3660]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_29,plain,
% 7.74/1.47      ( v5_pre_topc(X0,X1,X2)
% 7.74/1.47      | ~ v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 7.74/1.47      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.74/1.47      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 7.74/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.74/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 7.74/1.47      | ~ v2_pre_topc(X1)
% 7.74/1.47      | ~ v2_pre_topc(X2)
% 7.74/1.47      | ~ l1_pre_topc(X1)
% 7.74/1.47      | ~ l1_pre_topc(X2)
% 7.74/1.47      | ~ v1_funct_1(X0) ),
% 7.74/1.47      inference(cnf_transformation,[],[f118]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_3596,plain,
% 7.74/1.47      ( ~ v5_pre_topc(sK3,X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 7.74/1.47      | v5_pre_topc(sK3,X0,sK1)
% 7.74/1.47      | ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 7.74/1.47      | ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(sK1))
% 7.74/1.47      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 7.74/1.47      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
% 7.74/1.47      | ~ v2_pre_topc(X0)
% 7.74/1.47      | ~ v2_pre_topc(sK1)
% 7.74/1.47      | ~ l1_pre_topc(X0)
% 7.74/1.47      | ~ l1_pre_topc(sK1)
% 7.74/1.47      | ~ v1_funct_1(sK3) ),
% 7.74/1.47      inference(instantiation,[status(thm)],[c_29]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_3977,plain,
% 7.74/1.47      ( ~ v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 7.74/1.47      | v5_pre_topc(sK3,sK0,sK1)
% 7.74/1.47      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 7.74/1.47      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
% 7.74/1.47      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 7.74/1.47      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 7.74/1.47      | ~ v2_pre_topc(sK1)
% 7.74/1.47      | ~ v2_pre_topc(sK0)
% 7.74/1.47      | ~ l1_pre_topc(sK1)
% 7.74/1.47      | ~ l1_pre_topc(sK0)
% 7.74/1.47      | ~ v1_funct_1(sK3) ),
% 7.74/1.47      inference(instantiation,[status(thm)],[c_3596]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_3978,plain,
% 7.74/1.47      ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.74/1.47      | v5_pre_topc(sK3,sK0,sK1) = iProver_top
% 7.74/1.47      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.74/1.47      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.74/1.47      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 7.74/1.47      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 7.74/1.47      | v2_pre_topc(sK1) != iProver_top
% 7.74/1.47      | v2_pre_topc(sK0) != iProver_top
% 7.74/1.47      | l1_pre_topc(sK1) != iProver_top
% 7.74/1.47      | l1_pre_topc(sK0) != iProver_top
% 7.74/1.47      | v1_funct_1(sK3) != iProver_top ),
% 7.74/1.47      inference(predicate_to_equality,[status(thm)],[c_3977]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_30,plain,
% 7.74/1.47      ( ~ v5_pre_topc(X0,X1,X2)
% 7.74/1.47      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 7.74/1.47      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.74/1.47      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 7.74/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.74/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 7.74/1.47      | ~ v2_pre_topc(X1)
% 7.74/1.47      | ~ v2_pre_topc(X2)
% 7.74/1.47      | ~ l1_pre_topc(X1)
% 7.74/1.47      | ~ l1_pre_topc(X2)
% 7.74/1.47      | ~ v1_funct_1(X0) ),
% 7.74/1.47      inference(cnf_transformation,[],[f119]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_3940,plain,
% 7.74/1.47      ( ~ v5_pre_topc(sK3,sK0,X0)
% 7.74/1.47      | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 7.74/1.47      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(X0))
% 7.74/1.47      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
% 7.74/1.47      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
% 7.74/1.47      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
% 7.74/1.47      | ~ v2_pre_topc(X0)
% 7.74/1.47      | ~ v2_pre_topc(sK0)
% 7.74/1.47      | ~ l1_pre_topc(X0)
% 7.74/1.47      | ~ l1_pre_topc(sK0)
% 7.74/1.47      | ~ v1_funct_1(sK3) ),
% 7.74/1.47      inference(instantiation,[status(thm)],[c_30]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_5507,plain,
% 7.74/1.47      ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 7.74/1.47      | ~ v5_pre_topc(sK3,sK0,sK1)
% 7.74/1.47      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 7.74/1.47      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
% 7.74/1.47      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 7.74/1.47      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 7.74/1.47      | ~ v2_pre_topc(sK1)
% 7.74/1.47      | ~ v2_pre_topc(sK0)
% 7.74/1.47      | ~ l1_pre_topc(sK1)
% 7.74/1.47      | ~ l1_pre_topc(sK0)
% 7.74/1.47      | ~ v1_funct_1(sK3) ),
% 7.74/1.47      inference(instantiation,[status(thm)],[c_3940]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_5508,plain,
% 7.74/1.47      ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 7.74/1.47      | v5_pre_topc(sK3,sK0,sK1) != iProver_top
% 7.74/1.47      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.74/1.47      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.74/1.47      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 7.74/1.47      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 7.74/1.47      | v2_pre_topc(sK1) != iProver_top
% 7.74/1.47      | v2_pre_topc(sK0) != iProver_top
% 7.74/1.47      | l1_pre_topc(sK1) != iProver_top
% 7.74/1.47      | l1_pre_topc(sK0) != iProver_top
% 7.74/1.47      | v1_funct_1(sK3) != iProver_top ),
% 7.74/1.47      inference(predicate_to_equality,[status(thm)],[c_5507]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_27,plain,
% 7.74/1.47      ( v5_pre_topc(X0,X1,X2)
% 7.74/1.47      | ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 7.74/1.47      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.74/1.47      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 7.74/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.74/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 7.74/1.47      | ~ v2_pre_topc(X1)
% 7.74/1.47      | ~ v2_pre_topc(X2)
% 7.74/1.47      | ~ l1_pre_topc(X1)
% 7.74/1.47      | ~ l1_pre_topc(X2)
% 7.74/1.47      | ~ v1_funct_1(X0) ),
% 7.74/1.47      inference(cnf_transformation,[],[f116]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_3011,plain,
% 7.74/1.47      ( v5_pre_topc(X0,X1,X2) = iProver_top
% 7.74/1.47      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) != iProver_top
% 7.74/1.47      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 7.74/1.47      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
% 7.74/1.47      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 7.74/1.47      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
% 7.74/1.47      | v2_pre_topc(X1) != iProver_top
% 7.74/1.47      | v2_pre_topc(X2) != iProver_top
% 7.74/1.47      | l1_pre_topc(X1) != iProver_top
% 7.74/1.47      | l1_pre_topc(X2) != iProver_top
% 7.74/1.47      | v1_funct_1(X0) != iProver_top ),
% 7.74/1.47      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_6360,plain,
% 7.74/1.47      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.74/1.47      | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 7.74/1.47      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.74/1.47      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.74/1.47      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 7.74/1.47      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.74/1.47      | v2_pre_topc(sK0) != iProver_top
% 7.74/1.47      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.74/1.47      | l1_pre_topc(sK0) != iProver_top
% 7.74/1.47      | v1_funct_1(sK3) != iProver_top ),
% 7.74/1.47      inference(superposition,[status(thm)],[c_3005,c_3011]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_6474,plain,
% 7.74/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 7.74/1.47      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.74/1.47      | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 7.74/1.47      inference(global_propositional_subsumption,
% 7.74/1.47                [status(thm)],
% 7.74/1.47                [c_6005,c_44,c_45,c_46,c_47,c_51,c_52,c_3035,c_3032,c_3034,
% 7.74/1.47                 c_3033,c_3189,c_3447,c_3661,c_3978,c_5508,c_6360]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_6475,plain,
% 7.74/1.47      ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.74/1.47      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.74/1.47      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
% 7.74/1.47      inference(renaming,[status(thm)],[c_6474]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_6478,plain,
% 7.74/1.47      ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.74/1.47      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
% 7.74/1.47      inference(global_propositional_subsumption,
% 7.74/1.47                [status(thm)],
% 7.74/1.47                [c_6475,c_44,c_45,c_46,c_47,c_51,c_52,c_3032,c_3034,c_3033,
% 7.74/1.47                 c_3189,c_3447,c_3661,c_5508,c_6360]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_15018,plain,
% 7.74/1.47      ( sK3 = k1_xboole_0
% 7.74/1.47      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.74/1.47      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
% 7.74/1.47      inference(superposition,[status(thm)],[c_7174,c_6478]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_15805,plain,
% 7.74/1.47      ( sK3 = k1_xboole_0
% 7.74/1.47      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.74/1.47      | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) != iProver_top ),
% 7.74/1.47      inference(superposition,[status(thm)],[c_5531,c_15018]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_14258,plain,
% 7.74/1.47      ( r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) ),
% 7.74/1.47      inference(instantiation,[status(thm)],[c_3]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_14259,plain,
% 7.74/1.47      ( r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) = iProver_top ),
% 7.74/1.47      inference(predicate_to_equality,[status(thm)],[c_14258]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_15893,plain,
% 7.74/1.47      ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.74/1.47      | sK3 = k1_xboole_0 ),
% 7.74/1.47      inference(global_propositional_subsumption,
% 7.74/1.47                [status(thm)],
% 7.74/1.47                [c_15805,c_14259]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_15894,plain,
% 7.74/1.47      ( sK3 = k1_xboole_0
% 7.74/1.47      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
% 7.74/1.47      inference(renaming,[status(thm)],[c_15893]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_15897,plain,
% 7.74/1.47      ( sK3 = k1_xboole_0
% 7.74/1.47      | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
% 7.74/1.47      inference(superposition,[status(thm)],[c_7174,c_15894]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_16368,plain,
% 7.74/1.47      ( sK3 = k1_xboole_0 ),
% 7.74/1.47      inference(global_propositional_subsumption,
% 7.74/1.47                [status(thm)],
% 7.74/1.47                [c_16323,c_15897]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_17610,plain,
% 7.74/1.47      ( k1_relset_1(k1_xboole_0,u1_struct_0(sK1),u1_struct_0(sK1)) = k1_xboole_0
% 7.74/1.47      | u1_struct_0(sK0) = k1_xboole_0
% 7.74/1.47      | v1_funct_2(u1_struct_0(sK1),k1_xboole_0,u1_struct_0(sK1)) != iProver_top ),
% 7.74/1.47      inference(light_normalisation,[status(thm)],[c_17607,c_10355,c_16368]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_4858,plain,
% 7.74/1.47      ( v1_funct_2(X0,k1_xboole_0,u1_struct_0(sK1))
% 7.74/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
% 7.74/1.47      | k1_relset_1(k1_xboole_0,u1_struct_0(sK1),X0) != k1_xboole_0 ),
% 7.74/1.47      inference(instantiation,[status(thm)],[c_16]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_4859,plain,
% 7.74/1.47      ( k1_relset_1(k1_xboole_0,u1_struct_0(sK1),X0) != k1_xboole_0
% 7.74/1.47      | v1_funct_2(X0,k1_xboole_0,u1_struct_0(sK1)) = iProver_top
% 7.74/1.47      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) != iProver_top ),
% 7.74/1.47      inference(predicate_to_equality,[status(thm)],[c_4858]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_4861,plain,
% 7.74/1.47      ( k1_relset_1(k1_xboole_0,u1_struct_0(sK1),k1_xboole_0) != k1_xboole_0
% 7.74/1.47      | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1)) = iProver_top
% 7.74/1.47      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) != iProver_top ),
% 7.74/1.47      inference(instantiation,[status(thm)],[c_4859]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_14799,plain,
% 7.74/1.47      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) ),
% 7.74/1.47      inference(instantiation,[status(thm)],[c_5]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_14800,plain,
% 7.74/1.47      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) = iProver_top ),
% 7.74/1.47      inference(predicate_to_equality,[status(thm)],[c_14799]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_3028,plain,
% 7.74/1.47      ( r1_tarski(X0,X0) = iProver_top ),
% 7.74/1.47      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_5532,plain,
% 7.74/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1)))) = iProver_top
% 7.74/1.47      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 7.74/1.47      inference(superposition,[status(thm)],[c_3033,c_3022]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_5543,plain,
% 7.74/1.47      ( k1_relset_1(X0,u1_struct_0(sK1),sK3) = k1_relat_1(sK3)
% 7.74/1.47      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 7.74/1.47      inference(superposition,[status(thm)],[c_5532,c_3023]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_5777,plain,
% 7.74/1.47      ( k1_relset_1(k1_relat_1(sK3),u1_struct_0(sK1),sK3) = k1_relat_1(sK3) ),
% 7.74/1.47      inference(superposition,[status(thm)],[c_3028,c_5543]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_16482,plain,
% 7.74/1.47      ( k1_relset_1(k1_relat_1(k1_xboole_0),u1_struct_0(sK1),k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 7.74/1.47      inference(demodulation,[status(thm)],[c_16368,c_5777]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_16541,plain,
% 7.74/1.47      ( k1_relset_1(k1_xboole_0,u1_struct_0(sK1),k1_xboole_0) = k1_xboole_0 ),
% 7.74/1.47      inference(light_normalisation,[status(thm)],[c_16482,c_10355]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_3882,plain,
% 7.74/1.47      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.74/1.47      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.74/1.47      | v1_funct_1(sK3) != iProver_top
% 7.74/1.47      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
% 7.74/1.47      inference(superposition,[status(thm)],[c_3005,c_2995]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_4285,plain,
% 7.74/1.47      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.74/1.47      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
% 7.74/1.47      inference(global_propositional_subsumption,
% 7.74/1.47                [status(thm)],
% 7.74/1.47                [c_3882,c_51,c_52]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_7400,plain,
% 7.74/1.47      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.74/1.47      | u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.74/1.47      | v1_xboole_0(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) = iProver_top ),
% 7.74/1.47      inference(superposition,[status(thm)],[c_4542,c_4285]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_4544,plain,
% 7.74/1.47      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = u1_struct_0(sK1)
% 7.74/1.47      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.74/1.47      | u1_struct_0(sK0) = k1_relat_1(sK3) ),
% 7.74/1.47      inference(superposition,[status(thm)],[c_4285,c_4091]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_5144,plain,
% 7.74/1.47      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.74/1.47      | u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.74/1.47      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) = iProver_top ),
% 7.74/1.47      inference(superposition,[status(thm)],[c_4544,c_3004]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_5143,plain,
% 7.74/1.47      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.74/1.47      | u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.74/1.47      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) = iProver_top ),
% 7.74/1.47      inference(superposition,[status(thm)],[c_4544,c_3005]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_3009,plain,
% 7.74/1.47      ( v5_pre_topc(X0,X1,X2) = iProver_top
% 7.74/1.47      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) != iProver_top
% 7.74/1.47      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 7.74/1.47      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 7.74/1.47      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 7.74/1.47      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 7.74/1.47      | v2_pre_topc(X1) != iProver_top
% 7.74/1.47      | v2_pre_topc(X2) != iProver_top
% 7.74/1.47      | l1_pre_topc(X1) != iProver_top
% 7.74/1.47      | l1_pre_topc(X2) != iProver_top
% 7.74/1.47      | v1_funct_1(X0) != iProver_top ),
% 7.74/1.47      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_5295,plain,
% 7.74/1.47      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.74/1.47      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top
% 7.74/1.47      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.74/1.47      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 7.74/1.47      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 7.74/1.47      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 7.74/1.47      | v2_pre_topc(sK1) != iProver_top
% 7.74/1.47      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 7.74/1.47      | l1_pre_topc(sK1) != iProver_top
% 7.74/1.47      | v1_funct_1(sK3) != iProver_top ),
% 7.74/1.47      inference(superposition,[status(thm)],[c_3005,c_3009]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_3173,plain,
% 7.74/1.47      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 7.74/1.47      | ~ v2_pre_topc(sK0)
% 7.74/1.47      | ~ l1_pre_topc(sK0) ),
% 7.74/1.47      inference(instantiation,[status(thm)],[c_26]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_3174,plain,
% 7.74/1.47      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
% 7.74/1.47      | v2_pre_topc(sK0) != iProver_top
% 7.74/1.47      | l1_pre_topc(sK0) != iProver_top ),
% 7.74/1.47      inference(predicate_to_equality,[status(thm)],[c_3173]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_3434,plain,
% 7.74/1.47      ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 7.74/1.47      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 7.74/1.47      inference(instantiation,[status(thm)],[c_24]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_3435,plain,
% 7.74/1.47      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 7.74/1.47      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top ),
% 7.74/1.47      inference(predicate_to_equality,[status(thm)],[c_3434]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_3650,plain,
% 7.74/1.47      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 7.74/1.47      | ~ l1_pre_topc(sK0) ),
% 7.74/1.47      inference(instantiation,[status(thm)],[c_25]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_3651,plain,
% 7.74/1.47      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 7.74/1.47      | l1_pre_topc(sK0) != iProver_top ),
% 7.74/1.47      inference(predicate_to_equality,[status(thm)],[c_3650]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_3008,plain,
% 7.74/1.47      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 7.74/1.47      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) = iProver_top
% 7.74/1.47      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 7.74/1.47      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 7.74/1.47      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 7.74/1.47      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 7.74/1.47      | v2_pre_topc(X1) != iProver_top
% 7.74/1.47      | v2_pre_topc(X2) != iProver_top
% 7.74/1.47      | l1_pre_topc(X1) != iProver_top
% 7.74/1.47      | l1_pre_topc(X2) != iProver_top
% 7.74/1.47      | v1_funct_1(X0) != iProver_top ),
% 7.74/1.47      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_4674,plain,
% 7.74/1.47      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 7.74/1.47      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
% 7.74/1.47      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.74/1.47      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 7.74/1.47      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 7.74/1.47      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 7.74/1.47      | v2_pre_topc(sK1) != iProver_top
% 7.74/1.47      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 7.74/1.47      | l1_pre_topc(sK1) != iProver_top
% 7.74/1.47      | v1_funct_1(sK3) != iProver_top ),
% 7.74/1.47      inference(superposition,[status(thm)],[c_3005,c_3008]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_3626,plain,
% 7.74/1.47      ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)
% 7.74/1.47      | v5_pre_topc(sK3,sK0,X0)
% 7.74/1.47      | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X0))
% 7.74/1.47      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(X0))
% 7.74/1.47      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X0))))
% 7.74/1.47      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
% 7.74/1.47      | ~ v2_pre_topc(X0)
% 7.74/1.47      | ~ v2_pre_topc(sK0)
% 7.74/1.47      | ~ l1_pre_topc(X0)
% 7.74/1.47      | ~ l1_pre_topc(sK0)
% 7.74/1.47      | ~ v1_funct_1(sK3) ),
% 7.74/1.47      inference(instantiation,[status(thm)],[c_27]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_4002,plain,
% 7.74/1.47      ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
% 7.74/1.47      | v5_pre_topc(sK3,sK0,sK1)
% 7.74/1.47      | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
% 7.74/1.47      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
% 7.74/1.47      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
% 7.74/1.47      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 7.74/1.47      | ~ v2_pre_topc(sK1)
% 7.74/1.47      | ~ v2_pre_topc(sK0)
% 7.74/1.47      | ~ l1_pre_topc(sK1)
% 7.74/1.47      | ~ l1_pre_topc(sK0)
% 7.74/1.47      | ~ v1_funct_1(sK3) ),
% 7.74/1.47      inference(instantiation,[status(thm)],[c_3626]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_4003,plain,
% 7.74/1.47      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
% 7.74/1.47      | v5_pre_topc(sK3,sK0,sK1) = iProver_top
% 7.74/1.47      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 7.74/1.47      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.74/1.47      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 7.74/1.47      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 7.74/1.47      | v2_pre_topc(sK1) != iProver_top
% 7.74/1.47      | v2_pre_topc(sK0) != iProver_top
% 7.74/1.47      | l1_pre_topc(sK1) != iProver_top
% 7.74/1.47      | l1_pre_topc(sK0) != iProver_top
% 7.74/1.47      | v1_funct_1(sK3) != iProver_top ),
% 7.74/1.47      inference(predicate_to_equality,[status(thm)],[c_4002]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_5080,plain,
% 7.74/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 7.74/1.47      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 7.74/1.47      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top ),
% 7.74/1.47      inference(global_propositional_subsumption,
% 7.74/1.47                [status(thm)],
% 7.74/1.47                [c_4674,c_44,c_45,c_46,c_47,c_51,c_52,c_3035,c_3032,c_3033,
% 7.74/1.47                 c_3174,c_3435,c_3651,c_4003]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_5081,plain,
% 7.74/1.47      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
% 7.74/1.47      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 7.74/1.47      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
% 7.74/1.47      inference(renaming,[status(thm)],[c_5080]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_3928,plain,
% 7.74/1.47      ( ~ v5_pre_topc(sK3,X0,sK1)
% 7.74/1.47      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1)
% 7.74/1.47      | ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(sK1))
% 7.74/1.47      | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK1))
% 7.74/1.47      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
% 7.74/1.47      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK1))))
% 7.74/1.47      | ~ v2_pre_topc(X0)
% 7.74/1.47      | ~ v2_pre_topc(sK1)
% 7.74/1.47      | ~ l1_pre_topc(X0)
% 7.74/1.47      | ~ l1_pre_topc(sK1)
% 7.74/1.47      | ~ v1_funct_1(sK3) ),
% 7.74/1.47      inference(instantiation,[status(thm)],[c_28]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_5493,plain,
% 7.74/1.47      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
% 7.74/1.47      | ~ v5_pre_topc(sK3,sK0,sK1)
% 7.74/1.47      | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
% 7.74/1.47      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
% 7.74/1.47      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
% 7.74/1.47      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 7.74/1.47      | ~ v2_pre_topc(sK1)
% 7.74/1.47      | ~ v2_pre_topc(sK0)
% 7.74/1.47      | ~ l1_pre_topc(sK1)
% 7.74/1.47      | ~ l1_pre_topc(sK0)
% 7.74/1.47      | ~ v1_funct_1(sK3) ),
% 7.74/1.47      inference(instantiation,[status(thm)],[c_3928]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_5494,plain,
% 7.74/1.47      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top
% 7.74/1.47      | v5_pre_topc(sK3,sK0,sK1) != iProver_top
% 7.74/1.47      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 7.74/1.47      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.74/1.47      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 7.74/1.47      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 7.74/1.47      | v2_pre_topc(sK1) != iProver_top
% 7.74/1.47      | v2_pre_topc(sK0) != iProver_top
% 7.74/1.47      | l1_pre_topc(sK1) != iProver_top
% 7.74/1.47      | l1_pre_topc(sK0) != iProver_top
% 7.74/1.47      | v1_funct_1(sK3) != iProver_top ),
% 7.74/1.47      inference(predicate_to_equality,[status(thm)],[c_5493]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_5669,plain,
% 7.74/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 7.74/1.47      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top ),
% 7.74/1.47      inference(global_propositional_subsumption,
% 7.74/1.47                [status(thm)],
% 7.74/1.47                [c_5295,c_44,c_45,c_46,c_47,c_51,c_52,c_3032,c_3034,c_3033,
% 7.74/1.47                 c_3174,c_3435,c_3651,c_5081,c_5494]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_5670,plain,
% 7.74/1.47      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 7.74/1.47      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
% 7.74/1.47      inference(renaming,[status(thm)],[c_5669]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_5673,plain,
% 7.74/1.47      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.74/1.47      | u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.74/1.47      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top ),
% 7.74/1.47      inference(superposition,[status(thm)],[c_5143,c_5670]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_8809,plain,
% 7.74/1.47      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.74/1.47      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
% 7.74/1.47      inference(global_propositional_subsumption,
% 7.74/1.47                [status(thm)],
% 7.74/1.47                [c_7400,c_5144,c_5673]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_8810,plain,
% 7.74/1.47      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.74/1.47      | u1_struct_0(sK0) = k1_relat_1(sK3) ),
% 7.74/1.47      inference(renaming,[status(thm)],[c_8809]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_8841,plain,
% 7.74/1.47      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.74/1.47      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 7.74/1.47      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1)))) != iProver_top ),
% 7.74/1.47      inference(superposition,[status(thm)],[c_8810,c_5670]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_10094,plain,
% 7.74/1.47      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.74/1.47      | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK1)) != iProver_top
% 7.74/1.47      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1)))) != iProver_top ),
% 7.74/1.47      inference(superposition,[status(thm)],[c_8810,c_8841]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_16397,plain,
% 7.74/1.47      ( u1_struct_0(sK0) = k1_relat_1(k1_xboole_0)
% 7.74/1.47      | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK1)) != iProver_top
% 7.74/1.47      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(sK1)))) != iProver_top ),
% 7.74/1.47      inference(demodulation,[status(thm)],[c_16368,c_10094]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_16607,plain,
% 7.74/1.47      ( u1_struct_0(sK0) = k1_xboole_0
% 7.74/1.47      | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1)) != iProver_top
% 7.74/1.47      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) != iProver_top ),
% 7.74/1.47      inference(light_normalisation,[status(thm)],[c_16397,c_10355]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_17612,plain,
% 7.74/1.47      ( u1_struct_0(sK0) = k1_xboole_0 ),
% 7.74/1.47      inference(global_propositional_subsumption,
% 7.74/1.47                [status(thm)],
% 7.74/1.47                [c_17610,c_4861,c_14800,c_16541,c_16607]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_16488,plain,
% 7.74/1.47      ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.74/1.47      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
% 7.74/1.47      inference(demodulation,[status(thm)],[c_16368,c_6478]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_132,plain,
% 7.74/1.47      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 7.74/1.47      inference(instantiation,[status(thm)],[c_3]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_1,plain,
% 7.74/1.47      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.74/1.47      inference(cnf_transformation,[],[f67]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_136,plain,
% 7.74/1.47      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_xboole_0 ),
% 7.74/1.47      inference(instantiation,[status(thm)],[c_1]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_2143,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_10575,plain,
% 7.74/1.47      ( X0 != X1 | X0 = u1_struct_0(sK0) | u1_struct_0(sK0) != X1 ),
% 7.74/1.47      inference(instantiation,[status(thm)],[c_2143]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_10576,plain,
% 7.74/1.47      ( u1_struct_0(sK0) != k1_xboole_0
% 7.74/1.47      | k1_xboole_0 = u1_struct_0(sK0)
% 7.74/1.47      | k1_xboole_0 != k1_xboole_0 ),
% 7.74/1.47      inference(instantiation,[status(thm)],[c_10575]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_10928,plain,
% 7.74/1.47      ( r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) ),
% 7.74/1.47      inference(instantiation,[status(thm)],[c_3]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_10929,plain,
% 7.74/1.47      ( r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) = iProver_top ),
% 7.74/1.47      inference(predicate_to_equality,[status(thm)],[c_10928]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_6482,plain,
% 7.74/1.47      ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.74/1.47      | r1_tarski(k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top ),
% 7.74/1.47      inference(superposition,[status(thm)],[c_5531,c_6478]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_16487,plain,
% 7.74/1.47      ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.74/1.47      | r1_tarski(k1_relat_1(k1_xboole_0),u1_struct_0(sK0)) != iProver_top ),
% 7.74/1.47      inference(demodulation,[status(thm)],[c_16368,c_6482]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_16536,plain,
% 7.74/1.47      ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.74/1.47      | r1_tarski(k1_xboole_0,u1_struct_0(sK0)) != iProver_top ),
% 7.74/1.47      inference(light_normalisation,[status(thm)],[c_16487,c_10355]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_8946,plain,
% 7.74/1.47      ( ~ r1_tarski(X0,u1_struct_0(sK0))
% 7.74/1.47      | r1_tarski(X1,u1_struct_0(sK0))
% 7.74/1.47      | X1 != X0 ),
% 7.74/1.47      inference(instantiation,[status(thm)],[c_2145]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_16702,plain,
% 7.74/1.47      ( r1_tarski(X0,u1_struct_0(sK0))
% 7.74/1.47      | ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))
% 7.74/1.47      | X0 != u1_struct_0(sK0) ),
% 7.74/1.47      inference(instantiation,[status(thm)],[c_8946]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_16703,plain,
% 7.74/1.47      ( X0 != u1_struct_0(sK0)
% 7.74/1.47      | r1_tarski(X0,u1_struct_0(sK0)) = iProver_top
% 7.74/1.47      | r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) != iProver_top ),
% 7.74/1.47      inference(predicate_to_equality,[status(thm)],[c_16702]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_16705,plain,
% 7.74/1.47      ( k1_xboole_0 != u1_struct_0(sK0)
% 7.74/1.47      | r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) != iProver_top
% 7.74/1.47      | r1_tarski(k1_xboole_0,u1_struct_0(sK0)) = iProver_top ),
% 7.74/1.47      inference(instantiation,[status(thm)],[c_16703]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_17238,plain,
% 7.74/1.47      ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
% 7.74/1.47      inference(global_propositional_subsumption,
% 7.74/1.47                [status(thm)],
% 7.74/1.47                [c_16488,c_132,c_136,c_4861,c_10576,c_10929,c_14800,c_16536,
% 7.74/1.47                 c_16541,c_16607,c_16705]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_17618,plain,
% 7.74/1.47      ( v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
% 7.74/1.47      inference(demodulation,[status(thm)],[c_17612,c_17238]) ).
% 7.74/1.47  
% 7.74/1.47  cnf(c_17984,plain,
% 7.74/1.47      ( $false ),
% 7.74/1.47      inference(superposition,[status(thm)],[c_11327,c_17618]) ).
% 7.74/1.47  
% 7.74/1.47  
% 7.74/1.47  % SZS output end CNFRefutation for theBenchmark.p
% 7.74/1.47  
% 7.74/1.47  ------                               Statistics
% 7.74/1.47  
% 7.74/1.47  ------ General
% 7.74/1.47  
% 7.74/1.47  abstr_ref_over_cycles:                  0
% 7.74/1.47  abstr_ref_under_cycles:                 0
% 7.74/1.47  gc_basic_clause_elim:                   0
% 7.74/1.47  forced_gc_time:                         0
% 7.74/1.47  parsing_time:                           0.008
% 7.74/1.47  unif_index_cands_time:                  0.
% 7.74/1.47  unif_index_add_time:                    0.
% 7.74/1.47  orderings_time:                         0.
% 7.74/1.47  out_proof_time:                         0.019
% 7.74/1.47  total_time:                             0.58
% 7.74/1.47  num_of_symbols:                         55
% 7.74/1.47  num_of_terms:                           13486
% 7.74/1.47  
% 7.74/1.47  ------ Preprocessing
% 7.74/1.47  
% 7.74/1.47  num_of_splits:                          0
% 7.74/1.47  num_of_split_atoms:                     0
% 7.74/1.47  num_of_reused_defs:                     0
% 7.74/1.47  num_eq_ax_congr_red:                    15
% 7.74/1.47  num_of_sem_filtered_clauses:            1
% 7.74/1.47  num_of_subtypes:                        0
% 7.74/1.47  monotx_restored_types:                  0
% 7.74/1.47  sat_num_of_epr_types:                   0
% 7.74/1.47  sat_num_of_non_cyclic_types:            0
% 7.74/1.47  sat_guarded_non_collapsed_types:        0
% 7.74/1.47  num_pure_diseq_elim:                    0
% 7.74/1.47  simp_replaced_by:                       0
% 7.74/1.47  res_preprocessed:                       191
% 7.74/1.47  prep_upred:                             0
% 7.74/1.47  prep_unflattend:                        26
% 7.74/1.47  smt_new_axioms:                         0
% 7.74/1.47  pred_elim_cands:                        8
% 7.74/1.47  pred_elim:                              3
% 7.74/1.47  pred_elim_cl:                           4
% 7.74/1.47  pred_elim_cycles:                       6
% 7.74/1.47  merged_defs:                            8
% 7.74/1.47  merged_defs_ncl:                        0
% 7.74/1.47  bin_hyper_res:                          8
% 7.74/1.47  prep_cycles:                            4
% 7.74/1.47  pred_elim_time:                         0.026
% 7.74/1.47  splitting_time:                         0.
% 7.74/1.47  sem_filter_time:                        0.
% 7.74/1.47  monotx_time:                            0.
% 7.74/1.47  subtype_inf_time:                       0.
% 7.74/1.47  
% 7.74/1.47  ------ Problem properties
% 7.74/1.47  
% 7.74/1.47  clauses:                                38
% 7.74/1.47  conjectures:                            13
% 7.74/1.47  epr:                                    12
% 7.74/1.47  horn:                                   32
% 7.74/1.47  ground:                                 14
% 7.74/1.47  unary:                                  15
% 7.74/1.47  binary:                                 7
% 7.74/1.47  lits:                                   114
% 7.74/1.47  lits_eq:                                15
% 7.74/1.47  fd_pure:                                0
% 7.74/1.47  fd_pseudo:                              0
% 7.74/1.47  fd_cond:                                3
% 7.74/1.47  fd_pseudo_cond:                         3
% 7.74/1.47  ac_symbols:                             0
% 7.74/1.47  
% 7.74/1.47  ------ Propositional Solver
% 7.74/1.47  
% 7.74/1.47  prop_solver_calls:                      32
% 7.74/1.47  prop_fast_solver_calls:                 2419
% 7.74/1.47  smt_solver_calls:                       0
% 7.74/1.47  smt_fast_solver_calls:                  0
% 7.74/1.47  prop_num_of_clauses:                    6975
% 7.74/1.47  prop_preprocess_simplified:             13281
% 7.74/1.47  prop_fo_subsumed:                       127
% 7.74/1.47  prop_solver_time:                       0.
% 7.74/1.47  smt_solver_time:                        0.
% 7.74/1.47  smt_fast_solver_time:                   0.
% 7.74/1.47  prop_fast_solver_time:                  0.
% 7.74/1.47  prop_unsat_core_time:                   0.
% 7.74/1.47  
% 7.74/1.47  ------ QBF
% 7.74/1.47  
% 7.74/1.47  qbf_q_res:                              0
% 7.74/1.47  qbf_num_tautologies:                    0
% 7.74/1.47  qbf_prep_cycles:                        0
% 7.74/1.47  
% 7.74/1.47  ------ BMC1
% 7.74/1.47  
% 7.74/1.47  bmc1_current_bound:                     -1
% 7.74/1.47  bmc1_last_solved_bound:                 -1
% 7.74/1.47  bmc1_unsat_core_size:                   -1
% 7.74/1.47  bmc1_unsat_core_parents_size:           -1
% 7.74/1.47  bmc1_merge_next_fun:                    0
% 7.74/1.47  bmc1_unsat_core_clauses_time:           0.
% 7.74/1.47  
% 7.74/1.47  ------ Instantiation
% 7.74/1.47  
% 7.74/1.47  inst_num_of_clauses:                    1899
% 7.74/1.47  inst_num_in_passive:                    790
% 7.74/1.47  inst_num_in_active:                     1094
% 7.74/1.47  inst_num_in_unprocessed:                15
% 7.74/1.47  inst_num_of_loops:                      1190
% 7.74/1.47  inst_num_of_learning_restarts:          0
% 7.74/1.47  inst_num_moves_active_passive:          91
% 7.74/1.47  inst_lit_activity:                      0
% 7.74/1.47  inst_lit_activity_moves:                0
% 7.74/1.47  inst_num_tautologies:                   0
% 7.74/1.47  inst_num_prop_implied:                  0
% 7.74/1.47  inst_num_existing_simplified:           0
% 7.74/1.47  inst_num_eq_res_simplified:             0
% 7.74/1.47  inst_num_child_elim:                    0
% 7.74/1.47  inst_num_of_dismatching_blockings:      673
% 7.74/1.47  inst_num_of_non_proper_insts:           2665
% 7.74/1.47  inst_num_of_duplicates:                 0
% 7.74/1.47  inst_inst_num_from_inst_to_res:         0
% 7.74/1.47  inst_dismatching_checking_time:         0.
% 7.74/1.47  
% 7.74/1.47  ------ Resolution
% 7.74/1.47  
% 7.74/1.47  res_num_of_clauses:                     0
% 7.74/1.47  res_num_in_passive:                     0
% 7.74/1.47  res_num_in_active:                      0
% 7.74/1.47  res_num_of_loops:                       195
% 7.74/1.47  res_forward_subset_subsumed:            146
% 7.74/1.47  res_backward_subset_subsumed:           0
% 7.74/1.47  res_forward_subsumed:                   0
% 7.74/1.47  res_backward_subsumed:                  0
% 7.74/1.47  res_forward_subsumption_resolution:     1
% 7.74/1.47  res_backward_subsumption_resolution:    0
% 7.74/1.47  res_clause_to_clause_subsumption:       1382
% 7.74/1.47  res_orphan_elimination:                 0
% 7.74/1.47  res_tautology_del:                      225
% 7.74/1.47  res_num_eq_res_simplified:              0
% 7.74/1.47  res_num_sel_changes:                    0
% 7.74/1.47  res_moves_from_active_to_pass:          0
% 7.74/1.47  
% 7.74/1.47  ------ Superposition
% 7.74/1.47  
% 7.74/1.47  sup_time_total:                         0.
% 7.74/1.47  sup_time_generating:                    0.
% 7.74/1.47  sup_time_sim_full:                      0.
% 7.74/1.47  sup_time_sim_immed:                     0.
% 7.74/1.47  
% 7.74/1.47  sup_num_of_clauses:                     327
% 7.74/1.47  sup_num_in_active:                      53
% 7.74/1.47  sup_num_in_passive:                     274
% 7.74/1.47  sup_num_of_loops:                       236
% 7.74/1.47  sup_fw_superposition:                   342
% 7.74/1.47  sup_bw_superposition:                   637
% 7.74/1.47  sup_immediate_simplified:               382
% 7.74/1.47  sup_given_eliminated:                   1
% 7.74/1.47  comparisons_done:                       0
% 7.74/1.47  comparisons_avoided:                    89
% 7.74/1.47  
% 7.74/1.47  ------ Simplifications
% 7.74/1.47  
% 7.74/1.47  
% 7.74/1.47  sim_fw_subset_subsumed:                 206
% 7.74/1.47  sim_bw_subset_subsumed:                 152
% 7.74/1.47  sim_fw_subsumed:                        62
% 7.74/1.47  sim_bw_subsumed:                        3
% 7.74/1.47  sim_fw_subsumption_res:                 0
% 7.74/1.47  sim_bw_subsumption_res:                 0
% 7.74/1.47  sim_tautology_del:                      17
% 7.74/1.47  sim_eq_tautology_del:                   38
% 7.74/1.47  sim_eq_res_simp:                        0
% 7.74/1.47  sim_fw_demodulated:                     22
% 7.74/1.47  sim_bw_demodulated:                     162
% 7.74/1.47  sim_light_normalised:                   131
% 7.74/1.47  sim_joinable_taut:                      0
% 7.74/1.47  sim_joinable_simp:                      0
% 7.74/1.47  sim_ac_normalised:                      0
% 7.74/1.47  sim_smt_subsumption:                    0
% 7.74/1.47  
%------------------------------------------------------------------------------
