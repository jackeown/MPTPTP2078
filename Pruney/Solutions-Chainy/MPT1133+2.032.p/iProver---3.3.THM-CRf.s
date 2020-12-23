%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:54 EST 2020

% Result     : Theorem 7.44s
% Output     : CNFRefutation 7.44s
% Verified   : 
% Statistics : Number of formulae       :  306 (28522 expanded)
%              Number of clauses        :  212 (6416 expanded)
%              Number of leaves         :   20 (8560 expanded)
%              Depth                    :   29
%              Number of atoms          : 1248 (333111 expanded)
%              Number of equality atoms :  531 (39682 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f94,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
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
    inference(flattening,[],[f26])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f101,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f71])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f40])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f97,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f58])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f56,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f16,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f52,plain,(
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

fof(f51,plain,(
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

fof(f50,plain,(
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

fof(f49,plain,
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

fof(f53,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f48,f52,f51,f50,f49])).

fof(f87,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f53])).

fof(f91,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f53])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f86,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f53])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f96,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f59])).

fof(f93,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f90,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(cnf_transformation,[],[f53])).

fof(f89,plain,(
    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(cnf_transformation,[],[f53])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f100,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f72])).

fof(f15,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f80,plain,(
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
    inference(cnf_transformation,[],[f46])).

fof(f105,plain,(
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
    inference(equality_resolution,[],[f80])).

fof(f81,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f82,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f83,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f84,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f88,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f30,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f31,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f76,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f28,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f74,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f75,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f79,plain,(
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
    inference(cnf_transformation,[],[f46])).

fof(f106,plain,(
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
    inference(equality_resolution,[],[f79])).

fof(f14,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f78,plain,(
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
    inference(cnf_transformation,[],[f45])).

fof(f103,plain,(
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
    inference(equality_resolution,[],[f78])).

fof(f92,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f77,plain,(
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
    inference(cnf_transformation,[],[f45])).

fof(f104,plain,(
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
    inference(equality_resolution,[],[f77])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2351,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2349,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2347,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3859,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2349,c_2347])).

cnf(c_14184,plain,
    ( k1_relset_1(X0,X1,k2_zfmisc_1(X0,X1)) = k1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(superposition,[status(thm)],[c_2351,c_3859])).

cnf(c_16,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_2344,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_2360,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2344,c_4])).

cnf(c_15673,plain,
    ( k1_relat_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_xboole_0
    | v1_funct_2(k2_zfmisc_1(k1_xboole_0,X0),k1_xboole_0,X0) = iProver_top
    | m1_subset_1(k2_zfmisc_1(k1_xboole_0,X0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14184,c_2360])).

cnf(c_6,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2350,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_12,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_10,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_514,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_12,c_10])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_518,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_514,c_11])).

cnf(c_519,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_518])).

cnf(c_2321,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_519])).

cnf(c_3160,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2350,c_2321])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2348,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3292,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2350,c_2348])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2352,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4397,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3292,c_2352])).

cnf(c_4838,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3160,c_4397])).

cnf(c_15674,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15673,c_4,c_4838])).

cnf(c_15675,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_15674])).

cnf(c_112,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_114,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_112])).

cnf(c_17410,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15675,c_114])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2328,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_29,negated_conjecture,
    ( sK2 = sK3 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2355,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2328,c_29])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2341,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5269,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3) = u1_struct_0(sK0)
    | u1_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2355,c_2341])).

cnf(c_3861,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2355,c_2347])).

cnf(c_5272,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK0) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5269,c_3861])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2327,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_2354,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2327,c_29])).

cnf(c_5280,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | u1_struct_0(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5272,c_2354])).

cnf(c_5281,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK0) = k1_relat_1(sK3) ),
    inference(renaming,[status(thm)],[c_5280])).

cnf(c_3294,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2355,c_2348])).

cnf(c_5304,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5281,c_3294])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_5312,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5304,c_3])).

cnf(c_5776,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5312,c_4397])).

cnf(c_27,negated_conjecture,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2333,plain,
    ( v5_pre_topc(sK2,sK0,sK1) != iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2358,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v5_pre_topc(sK3,sK0,sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2333,c_29])).

cnf(c_15413,plain,
    ( sK3 = k1_xboole_0
    | v5_pre_topc(sK3,g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v5_pre_topc(sK3,sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5776,c_2358])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2331,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_5268,plain,
    ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2331,c_2341])).

cnf(c_3860,plain,
    ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2331,c_2347])).

cnf(c_5273,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5268,c_3860])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_5277,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5273])).

cnf(c_6208,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5273,c_31,c_5277])).

cnf(c_6209,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
    inference(renaming,[status(thm)],[c_6208])).

cnf(c_6233,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6209,c_2331])).

cnf(c_6235,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6233,c_3])).

cnf(c_5310,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(sK0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5281,c_2354])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_2345,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X1,X0,k1_xboole_0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2361,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2345,c_3])).

cnf(c_5405,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | u1_struct_0(sK0) = k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5310,c_2361])).

cnf(c_2666,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | r1_tarski(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2667,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK3)) != iProver_top
    | r1_tarski(X0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2666])).

cnf(c_2669,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) != iProver_top
    | r1_tarski(k1_xboole_0,sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2667])).

cnf(c_2698,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2699,plain,
    ( sK3 = X0
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2698])).

cnf(c_2701,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK3,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2699])).

cnf(c_3279,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3280,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3279])).

cnf(c_4005,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | r1_tarski(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_4006,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4005])).

cnf(c_4008,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4006])).

cnf(c_6200,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5405,c_2669,c_2701,c_3280,c_4008])).

cnf(c_6340,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6235,c_6200])).

cnf(c_25,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
    | ~ v1_funct_1(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_2335,plain,
    ( v5_pre_topc(X0,X1,X2) = iProver_top
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3702,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2331,c_2335])).

cnf(c_39,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_40,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_38,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_41,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_37,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_42,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_36,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_43,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_47,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_48,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_22,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2487,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_2488,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2487])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2709,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_2710,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2709])).

cnf(c_21,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2903,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_2904,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2903])).

cnf(c_26,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
    | ~ v1_funct_1(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_2334,plain,
    ( v5_pre_topc(X0,X1,X2) != iProver_top
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) = iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3286,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2331,c_2334])).

cnf(c_23,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_2873,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)
    | v5_pre_topc(sK3,sK0,X0)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X0))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(X0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X0))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
    | ~ v1_funct_1(sK3)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_3172,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK3,sK0,sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK3)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_2873])).

cnf(c_3173,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
    | v5_pre_topc(sK3,sK0,sK1) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3172])).

cnf(c_3510,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3286,c_40,c_41,c_42,c_43,c_47,c_48,c_2355,c_2354,c_2358,c_2488,c_2710,c_2904,c_3173])).

cnf(c_3511,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3510])).

cnf(c_4061,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3702,c_40,c_41,c_42,c_43,c_47,c_48,c_2355,c_2354,c_2358,c_2488,c_2710,c_2904,c_3173,c_3286])).

cnf(c_4062,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4061])).

cnf(c_5298,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5281,c_4062])).

cnf(c_28,negated_conjecture,
    ( v5_pre_topc(sK2,sK0,sK1)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2332,plain,
    ( v5_pre_topc(sK2,sK0,sK1) = iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2357,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v5_pre_topc(sK3,sK0,sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2332,c_29])).

cnf(c_4065,plain,
    ( v5_pre_topc(sK3,sK0,sK1) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2357,c_4062])).

cnf(c_24,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_3072,plain,
    ( ~ v5_pre_topc(sK3,X0,sK1)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(sK1))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK3)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_4472,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v5_pre_topc(sK3,sK0,sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK3)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_3072])).

cnf(c_4473,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top
    | v5_pre_topc(sK3,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4472])).

cnf(c_5652,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5298,c_40,c_41,c_42,c_43,c_47,c_2355,c_2354,c_3511,c_4065,c_4473])).

cnf(c_9880,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6340,c_5652])).

cnf(c_11010,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6340,c_9880])).

cnf(c_15416,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5776,c_2355])).

cnf(c_15417,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5776,c_2354])).

cnf(c_15834,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_15413,c_11010,c_15416,c_15417])).

cnf(c_5656,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2349,c_5652])).

cnf(c_15891,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_15834,c_5656])).

cnf(c_17690,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3292,c_15891])).

cnf(c_4402,plain,
    ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = sK3
    | r1_tarski(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3294,c_2352])).

cnf(c_5294,plain,
    ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = sK3
    | u1_struct_0(sK0) = k1_relat_1(sK3)
    | r1_tarski(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5281,c_4402])).

cnf(c_5317,plain,
    ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = sK3
    | u1_struct_0(sK0) = k1_relat_1(sK3)
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5294,c_3])).

cnf(c_5929,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5317,c_2669,c_3280])).

cnf(c_5930,plain,
    ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = sK3
    | u1_struct_0(sK0) = k1_relat_1(sK3) ),
    inference(renaming,[status(thm)],[c_5929])).

cnf(c_15671,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3) = k1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | u1_struct_0(sK0) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_5930,c_14184])).

cnf(c_15676,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | k1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = k1_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_15671,c_3861])).

cnf(c_18207,plain,
    ( u1_struct_0(sK0) = k1_xboole_0
    | k1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_15676,c_4838,c_15834])).

cnf(c_2370,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2360])).

cnf(c_3858,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2350,c_2347])).

cnf(c_4842,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4838,c_3858])).

cnf(c_4844,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4842])).

cnf(c_2330,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_6234,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6209,c_2330])).

cnf(c_5657,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5281,c_5652])).

cnf(c_5658,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5657,c_3])).

cnf(c_5309,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5281,c_2355])).

cnf(c_5311,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5309,c_3])).

cnf(c_5948,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | u1_struct_0(sK0) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5658,c_5311])).

cnf(c_5949,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5948])).

cnf(c_5952,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5281,c_5949])).

cnf(c_6682,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | u1_struct_0(sK0) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_6234,c_5952])).

cnf(c_6798,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | v1_funct_2(sK3,k1_relat_1(sK3),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6682,c_5952])).

cnf(c_15897,plain,
    ( u1_struct_0(sK0) = k1_relat_1(k1_xboole_0)
    | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_15834,c_6798])).

cnf(c_15992,plain,
    ( u1_struct_0(sK0) = k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15897,c_4838])).

cnf(c_18208,plain,
    ( u1_struct_0(sK0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_18207,c_114,c_2370,c_4844,c_15992])).

cnf(c_3293,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2331,c_2348])).

cnf(c_4398,plain,
    ( k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = sK3
    | r1_tarski(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3293,c_2352])).

cnf(c_6228,plain,
    ( k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = sK3
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | r1_tarski(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6209,c_4398])).

cnf(c_6239,plain,
    ( k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = sK3
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6228,c_3])).

cnf(c_7068,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6239,c_2669,c_3280])).

cnf(c_7069,plain,
    ( k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = sK3
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
    inference(renaming,[status(thm)],[c_7068])).

cnf(c_15670,plain,
    ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3) = k1_relat_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_7069,c_14184])).

cnf(c_15677,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | k1_relat_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) = k1_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_15670,c_3860])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_115,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_116,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2336,plain,
    ( v5_pre_topc(X0,X1,X2) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) = iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4279,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2331,c_2336])).

cnf(c_49,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_2502,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_2503,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2502])).

cnf(c_2719,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_2720,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2719])).

cnf(c_2914,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_2915,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2914])).

cnf(c_2644,plain,
    ( ~ v5_pre_topc(sK3,X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK3,X0,sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK3)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_3142,plain,
    ( ~ v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK3,sK0,sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK3)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_2644])).

cnf(c_3143,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v5_pre_topc(sK3,sK0,sK1) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3142])).

cnf(c_3181,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_1(sK3)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_2873])).

cnf(c_3182,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3181])).

cnf(c_3112,plain,
    ( ~ v5_pre_topc(sK3,sK0,X0)
    | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(X0))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
    | ~ v1_funct_1(sK3)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_4481,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK3,sK0,sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK3)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_3112])).

cnf(c_4482,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v5_pre_topc(sK3,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4481])).

cnf(c_4523,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4279,c_40,c_41,c_42,c_43,c_47,c_48,c_49,c_2357,c_2355,c_2354,c_2358,c_2503,c_2720,c_2915,c_3143,c_3182,c_4482])).

cnf(c_4524,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4523])).

cnf(c_4527,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4524,c_40,c_41,c_42,c_43,c_47,c_48,c_49,c_2357,c_2355,c_2354,c_2503,c_2720,c_2915,c_3182,c_4482])).

cnf(c_4531,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2349,c_4527])).

cnf(c_6229,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6209,c_4531])).

cnf(c_6238,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6229,c_3])).

cnf(c_6232,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6209,c_3293])).

cnf(c_6236,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6232,c_3])).

cnf(c_6450,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6238,c_6236])).

cnf(c_6451,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6450])).

cnf(c_6454,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(sK0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6209,c_6451])).

cnf(c_1559,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_10246,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(sK3,u1_struct_0(sK0),X3)
    | X3 != X2
    | u1_struct_0(sK0) != X1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1559])).

cnf(c_10247,plain,
    ( X0 != X1
    | u1_struct_0(sK0) != X2
    | sK3 != X3
    | v1_funct_2(X3,X2,X1) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10246])).

cnf(c_10249,plain,
    ( u1_struct_0(sK0) != k1_xboole_0
    | sK3 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | v1_funct_2(sK3,u1_struct_0(sK0),k1_xboole_0) = iProver_top
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_10247])).

cnf(c_19578,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15677,c_114,c_115,c_116,c_2370,c_4844,c_6454,c_10249,c_11010,c_15416,c_15417,c_15992])).

cnf(c_19580,plain,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_19578,c_4838,c_15834,c_18208])).

cnf(c_20049,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17690,c_18208,c_19580])).

cnf(c_20051,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_17410,c_20049])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:38:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 7.44/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.44/1.48  
% 7.44/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.44/1.48  
% 7.44/1.48  ------  iProver source info
% 7.44/1.48  
% 7.44/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.44/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.44/1.48  git: non_committed_changes: false
% 7.44/1.48  git: last_make_outside_of_git: false
% 7.44/1.48  
% 7.44/1.48  ------ 
% 7.44/1.48  
% 7.44/1.48  ------ Input Options
% 7.44/1.48  
% 7.44/1.48  --out_options                           all
% 7.44/1.48  --tptp_safe_out                         true
% 7.44/1.48  --problem_path                          ""
% 7.44/1.48  --include_path                          ""
% 7.44/1.48  --clausifier                            res/vclausify_rel
% 7.44/1.48  --clausifier_options                    ""
% 7.44/1.48  --stdin                                 false
% 7.44/1.48  --stats_out                             all
% 7.44/1.48  
% 7.44/1.48  ------ General Options
% 7.44/1.48  
% 7.44/1.48  --fof                                   false
% 7.44/1.48  --time_out_real                         305.
% 7.44/1.48  --time_out_virtual                      -1.
% 7.44/1.48  --symbol_type_check                     false
% 7.44/1.48  --clausify_out                          false
% 7.44/1.48  --sig_cnt_out                           false
% 7.44/1.48  --trig_cnt_out                          false
% 7.44/1.48  --trig_cnt_out_tolerance                1.
% 7.44/1.48  --trig_cnt_out_sk_spl                   false
% 7.44/1.48  --abstr_cl_out                          false
% 7.44/1.48  
% 7.44/1.48  ------ Global Options
% 7.44/1.48  
% 7.44/1.48  --schedule                              default
% 7.44/1.48  --add_important_lit                     false
% 7.44/1.48  --prop_solver_per_cl                    1000
% 7.44/1.48  --min_unsat_core                        false
% 7.44/1.48  --soft_assumptions                      false
% 7.44/1.48  --soft_lemma_size                       3
% 7.44/1.48  --prop_impl_unit_size                   0
% 7.44/1.48  --prop_impl_unit                        []
% 7.44/1.48  --share_sel_clauses                     true
% 7.44/1.48  --reset_solvers                         false
% 7.44/1.48  --bc_imp_inh                            [conj_cone]
% 7.44/1.48  --conj_cone_tolerance                   3.
% 7.44/1.48  --extra_neg_conj                        none
% 7.44/1.48  --large_theory_mode                     true
% 7.44/1.48  --prolific_symb_bound                   200
% 7.44/1.48  --lt_threshold                          2000
% 7.44/1.48  --clause_weak_htbl                      true
% 7.44/1.48  --gc_record_bc_elim                     false
% 7.44/1.48  
% 7.44/1.48  ------ Preprocessing Options
% 7.44/1.48  
% 7.44/1.48  --preprocessing_flag                    true
% 7.44/1.48  --time_out_prep_mult                    0.1
% 7.44/1.48  --splitting_mode                        input
% 7.44/1.48  --splitting_grd                         true
% 7.44/1.48  --splitting_cvd                         false
% 7.44/1.48  --splitting_cvd_svl                     false
% 7.44/1.48  --splitting_nvd                         32
% 7.44/1.48  --sub_typing                            true
% 7.44/1.48  --prep_gs_sim                           true
% 7.44/1.48  --prep_unflatten                        true
% 7.44/1.48  --prep_res_sim                          true
% 7.44/1.48  --prep_upred                            true
% 7.44/1.48  --prep_sem_filter                       exhaustive
% 7.44/1.48  --prep_sem_filter_out                   false
% 7.44/1.48  --pred_elim                             true
% 7.44/1.48  --res_sim_input                         true
% 7.44/1.48  --eq_ax_congr_red                       true
% 7.44/1.48  --pure_diseq_elim                       true
% 7.44/1.48  --brand_transform                       false
% 7.44/1.48  --non_eq_to_eq                          false
% 7.44/1.48  --prep_def_merge                        true
% 7.44/1.48  --prep_def_merge_prop_impl              false
% 7.44/1.48  --prep_def_merge_mbd                    true
% 7.44/1.48  --prep_def_merge_tr_red                 false
% 7.44/1.48  --prep_def_merge_tr_cl                  false
% 7.44/1.48  --smt_preprocessing                     true
% 7.44/1.48  --smt_ac_axioms                         fast
% 7.44/1.48  --preprocessed_out                      false
% 7.44/1.48  --preprocessed_stats                    false
% 7.44/1.48  
% 7.44/1.48  ------ Abstraction refinement Options
% 7.44/1.48  
% 7.44/1.48  --abstr_ref                             []
% 7.44/1.48  --abstr_ref_prep                        false
% 7.44/1.48  --abstr_ref_until_sat                   false
% 7.44/1.48  --abstr_ref_sig_restrict                funpre
% 7.44/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.44/1.48  --abstr_ref_under                       []
% 7.44/1.48  
% 7.44/1.48  ------ SAT Options
% 7.44/1.48  
% 7.44/1.48  --sat_mode                              false
% 7.44/1.48  --sat_fm_restart_options                ""
% 7.44/1.48  --sat_gr_def                            false
% 7.44/1.48  --sat_epr_types                         true
% 7.44/1.48  --sat_non_cyclic_types                  false
% 7.44/1.48  --sat_finite_models                     false
% 7.44/1.48  --sat_fm_lemmas                         false
% 7.44/1.48  --sat_fm_prep                           false
% 7.44/1.48  --sat_fm_uc_incr                        true
% 7.44/1.48  --sat_out_model                         small
% 7.44/1.48  --sat_out_clauses                       false
% 7.44/1.48  
% 7.44/1.48  ------ QBF Options
% 7.44/1.48  
% 7.44/1.48  --qbf_mode                              false
% 7.44/1.48  --qbf_elim_univ                         false
% 7.44/1.48  --qbf_dom_inst                          none
% 7.44/1.48  --qbf_dom_pre_inst                      false
% 7.44/1.48  --qbf_sk_in                             false
% 7.44/1.48  --qbf_pred_elim                         true
% 7.44/1.48  --qbf_split                             512
% 7.44/1.48  
% 7.44/1.48  ------ BMC1 Options
% 7.44/1.48  
% 7.44/1.48  --bmc1_incremental                      false
% 7.44/1.48  --bmc1_axioms                           reachable_all
% 7.44/1.48  --bmc1_min_bound                        0
% 7.44/1.48  --bmc1_max_bound                        -1
% 7.44/1.48  --bmc1_max_bound_default                -1
% 7.44/1.48  --bmc1_symbol_reachability              true
% 7.44/1.48  --bmc1_property_lemmas                  false
% 7.44/1.48  --bmc1_k_induction                      false
% 7.44/1.48  --bmc1_non_equiv_states                 false
% 7.44/1.48  --bmc1_deadlock                         false
% 7.44/1.48  --bmc1_ucm                              false
% 7.44/1.48  --bmc1_add_unsat_core                   none
% 7.44/1.48  --bmc1_unsat_core_children              false
% 7.44/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.44/1.48  --bmc1_out_stat                         full
% 7.44/1.48  --bmc1_ground_init                      false
% 7.44/1.48  --bmc1_pre_inst_next_state              false
% 7.44/1.48  --bmc1_pre_inst_state                   false
% 7.44/1.48  --bmc1_pre_inst_reach_state             false
% 7.44/1.48  --bmc1_out_unsat_core                   false
% 7.44/1.48  --bmc1_aig_witness_out                  false
% 7.44/1.48  --bmc1_verbose                          false
% 7.44/1.48  --bmc1_dump_clauses_tptp                false
% 7.44/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.44/1.48  --bmc1_dump_file                        -
% 7.44/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.44/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.44/1.48  --bmc1_ucm_extend_mode                  1
% 7.44/1.48  --bmc1_ucm_init_mode                    2
% 7.44/1.48  --bmc1_ucm_cone_mode                    none
% 7.44/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.44/1.48  --bmc1_ucm_relax_model                  4
% 7.44/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.44/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.44/1.48  --bmc1_ucm_layered_model                none
% 7.44/1.48  --bmc1_ucm_max_lemma_size               10
% 7.44/1.48  
% 7.44/1.48  ------ AIG Options
% 7.44/1.48  
% 7.44/1.48  --aig_mode                              false
% 7.44/1.48  
% 7.44/1.48  ------ Instantiation Options
% 7.44/1.48  
% 7.44/1.48  --instantiation_flag                    true
% 7.44/1.48  --inst_sos_flag                         true
% 7.44/1.48  --inst_sos_phase                        true
% 7.44/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.44/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.44/1.48  --inst_lit_sel_side                     num_symb
% 7.44/1.48  --inst_solver_per_active                1400
% 7.44/1.48  --inst_solver_calls_frac                1.
% 7.44/1.48  --inst_passive_queue_type               priority_queues
% 7.44/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.44/1.48  --inst_passive_queues_freq              [25;2]
% 7.44/1.48  --inst_dismatching                      true
% 7.44/1.48  --inst_eager_unprocessed_to_passive     true
% 7.44/1.48  --inst_prop_sim_given                   true
% 7.44/1.48  --inst_prop_sim_new                     false
% 7.44/1.48  --inst_subs_new                         false
% 7.44/1.48  --inst_eq_res_simp                      false
% 7.44/1.48  --inst_subs_given                       false
% 7.44/1.48  --inst_orphan_elimination               true
% 7.44/1.48  --inst_learning_loop_flag               true
% 7.44/1.48  --inst_learning_start                   3000
% 7.44/1.48  --inst_learning_factor                  2
% 7.44/1.48  --inst_start_prop_sim_after_learn       3
% 7.44/1.48  --inst_sel_renew                        solver
% 7.44/1.48  --inst_lit_activity_flag                true
% 7.44/1.48  --inst_restr_to_given                   false
% 7.44/1.48  --inst_activity_threshold               500
% 7.44/1.48  --inst_out_proof                        true
% 7.44/1.48  
% 7.44/1.48  ------ Resolution Options
% 7.44/1.48  
% 7.44/1.48  --resolution_flag                       true
% 7.44/1.48  --res_lit_sel                           adaptive
% 7.44/1.48  --res_lit_sel_side                      none
% 7.44/1.48  --res_ordering                          kbo
% 7.44/1.48  --res_to_prop_solver                    active
% 7.44/1.48  --res_prop_simpl_new                    false
% 7.44/1.48  --res_prop_simpl_given                  true
% 7.44/1.48  --res_passive_queue_type                priority_queues
% 7.44/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.44/1.48  --res_passive_queues_freq               [15;5]
% 7.44/1.48  --res_forward_subs                      full
% 7.44/1.48  --res_backward_subs                     full
% 7.44/1.48  --res_forward_subs_resolution           true
% 7.44/1.48  --res_backward_subs_resolution          true
% 7.44/1.48  --res_orphan_elimination                true
% 7.44/1.48  --res_time_limit                        2.
% 7.44/1.48  --res_out_proof                         true
% 7.44/1.48  
% 7.44/1.48  ------ Superposition Options
% 7.44/1.48  
% 7.44/1.48  --superposition_flag                    true
% 7.44/1.48  --sup_passive_queue_type                priority_queues
% 7.44/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.44/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.44/1.48  --demod_completeness_check              fast
% 7.44/1.48  --demod_use_ground                      true
% 7.44/1.48  --sup_to_prop_solver                    passive
% 7.44/1.48  --sup_prop_simpl_new                    true
% 7.44/1.48  --sup_prop_simpl_given                  true
% 7.44/1.48  --sup_fun_splitting                     true
% 7.44/1.48  --sup_smt_interval                      50000
% 7.44/1.48  
% 7.44/1.48  ------ Superposition Simplification Setup
% 7.44/1.48  
% 7.44/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.44/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.44/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.44/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.44/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.44/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.44/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.44/1.48  --sup_immed_triv                        [TrivRules]
% 7.44/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.44/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.44/1.48  --sup_immed_bw_main                     []
% 7.44/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.44/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.44/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.44/1.48  --sup_input_bw                          []
% 7.44/1.48  
% 7.44/1.48  ------ Combination Options
% 7.44/1.48  
% 7.44/1.48  --comb_res_mult                         3
% 7.44/1.48  --comb_sup_mult                         2
% 7.44/1.48  --comb_inst_mult                        10
% 7.44/1.48  
% 7.44/1.48  ------ Debug Options
% 7.44/1.48  
% 7.44/1.48  --dbg_backtrace                         false
% 7.44/1.48  --dbg_dump_prop_clauses                 false
% 7.44/1.48  --dbg_dump_prop_clauses_file            -
% 7.44/1.48  --dbg_out_stat                          false
% 7.44/1.48  ------ Parsing...
% 7.44/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.44/1.48  
% 7.44/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.44/1.48  
% 7.44/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.44/1.48  
% 7.44/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.44/1.48  ------ Proving...
% 7.44/1.48  ------ Problem Properties 
% 7.44/1.48  
% 7.44/1.48  
% 7.44/1.48  clauses                                 36
% 7.44/1.48  conjectures                             13
% 7.44/1.48  EPR                                     9
% 7.44/1.48  Horn                                    30
% 7.44/1.48  unary                                   15
% 7.44/1.48  binary                                  8
% 7.44/1.48  lits                                    105
% 7.44/1.48  lits eq                                 17
% 7.44/1.48  fd_pure                                 0
% 7.44/1.48  fd_pseudo                               0
% 7.44/1.48  fd_cond                                 4
% 7.44/1.48  fd_pseudo_cond                          1
% 7.44/1.48  AC symbols                              0
% 7.44/1.48  
% 7.44/1.48  ------ Schedule dynamic 5 is on 
% 7.44/1.48  
% 7.44/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.44/1.48  
% 7.44/1.48  
% 7.44/1.48  ------ 
% 7.44/1.48  Current options:
% 7.44/1.48  ------ 
% 7.44/1.48  
% 7.44/1.48  ------ Input Options
% 7.44/1.48  
% 7.44/1.48  --out_options                           all
% 7.44/1.48  --tptp_safe_out                         true
% 7.44/1.48  --problem_path                          ""
% 7.44/1.48  --include_path                          ""
% 7.44/1.48  --clausifier                            res/vclausify_rel
% 7.44/1.48  --clausifier_options                    ""
% 7.44/1.48  --stdin                                 false
% 7.44/1.48  --stats_out                             all
% 7.44/1.48  
% 7.44/1.48  ------ General Options
% 7.44/1.48  
% 7.44/1.48  --fof                                   false
% 7.44/1.48  --time_out_real                         305.
% 7.44/1.48  --time_out_virtual                      -1.
% 7.44/1.48  --symbol_type_check                     false
% 7.44/1.48  --clausify_out                          false
% 7.44/1.48  --sig_cnt_out                           false
% 7.44/1.48  --trig_cnt_out                          false
% 7.44/1.48  --trig_cnt_out_tolerance                1.
% 7.44/1.48  --trig_cnt_out_sk_spl                   false
% 7.44/1.48  --abstr_cl_out                          false
% 7.44/1.48  
% 7.44/1.48  ------ Global Options
% 7.44/1.48  
% 7.44/1.48  --schedule                              default
% 7.44/1.48  --add_important_lit                     false
% 7.44/1.48  --prop_solver_per_cl                    1000
% 7.44/1.48  --min_unsat_core                        false
% 7.44/1.48  --soft_assumptions                      false
% 7.44/1.48  --soft_lemma_size                       3
% 7.44/1.48  --prop_impl_unit_size                   0
% 7.44/1.48  --prop_impl_unit                        []
% 7.44/1.48  --share_sel_clauses                     true
% 7.44/1.48  --reset_solvers                         false
% 7.44/1.48  --bc_imp_inh                            [conj_cone]
% 7.44/1.48  --conj_cone_tolerance                   3.
% 7.44/1.48  --extra_neg_conj                        none
% 7.44/1.48  --large_theory_mode                     true
% 7.44/1.48  --prolific_symb_bound                   200
% 7.44/1.48  --lt_threshold                          2000
% 7.44/1.48  --clause_weak_htbl                      true
% 7.44/1.48  --gc_record_bc_elim                     false
% 7.44/1.48  
% 7.44/1.48  ------ Preprocessing Options
% 7.44/1.48  
% 7.44/1.48  --preprocessing_flag                    true
% 7.44/1.48  --time_out_prep_mult                    0.1
% 7.44/1.48  --splitting_mode                        input
% 7.44/1.48  --splitting_grd                         true
% 7.44/1.48  --splitting_cvd                         false
% 7.44/1.48  --splitting_cvd_svl                     false
% 7.44/1.48  --splitting_nvd                         32
% 7.44/1.48  --sub_typing                            true
% 7.44/1.48  --prep_gs_sim                           true
% 7.44/1.48  --prep_unflatten                        true
% 7.44/1.48  --prep_res_sim                          true
% 7.44/1.48  --prep_upred                            true
% 7.44/1.48  --prep_sem_filter                       exhaustive
% 7.44/1.48  --prep_sem_filter_out                   false
% 7.44/1.48  --pred_elim                             true
% 7.44/1.48  --res_sim_input                         true
% 7.44/1.48  --eq_ax_congr_red                       true
% 7.44/1.48  --pure_diseq_elim                       true
% 7.44/1.48  --brand_transform                       false
% 7.44/1.48  --non_eq_to_eq                          false
% 7.44/1.48  --prep_def_merge                        true
% 7.44/1.48  --prep_def_merge_prop_impl              false
% 7.44/1.48  --prep_def_merge_mbd                    true
% 7.44/1.48  --prep_def_merge_tr_red                 false
% 7.44/1.48  --prep_def_merge_tr_cl                  false
% 7.44/1.48  --smt_preprocessing                     true
% 7.44/1.48  --smt_ac_axioms                         fast
% 7.44/1.48  --preprocessed_out                      false
% 7.44/1.48  --preprocessed_stats                    false
% 7.44/1.48  
% 7.44/1.48  ------ Abstraction refinement Options
% 7.44/1.48  
% 7.44/1.48  --abstr_ref                             []
% 7.44/1.48  --abstr_ref_prep                        false
% 7.44/1.48  --abstr_ref_until_sat                   false
% 7.44/1.48  --abstr_ref_sig_restrict                funpre
% 7.44/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.44/1.48  --abstr_ref_under                       []
% 7.44/1.48  
% 7.44/1.48  ------ SAT Options
% 7.44/1.48  
% 7.44/1.48  --sat_mode                              false
% 7.44/1.48  --sat_fm_restart_options                ""
% 7.44/1.48  --sat_gr_def                            false
% 7.44/1.48  --sat_epr_types                         true
% 7.44/1.48  --sat_non_cyclic_types                  false
% 7.44/1.48  --sat_finite_models                     false
% 7.44/1.48  --sat_fm_lemmas                         false
% 7.44/1.48  --sat_fm_prep                           false
% 7.44/1.48  --sat_fm_uc_incr                        true
% 7.44/1.48  --sat_out_model                         small
% 7.44/1.48  --sat_out_clauses                       false
% 7.44/1.48  
% 7.44/1.48  ------ QBF Options
% 7.44/1.48  
% 7.44/1.48  --qbf_mode                              false
% 7.44/1.48  --qbf_elim_univ                         false
% 7.44/1.48  --qbf_dom_inst                          none
% 7.44/1.48  --qbf_dom_pre_inst                      false
% 7.44/1.48  --qbf_sk_in                             false
% 7.44/1.48  --qbf_pred_elim                         true
% 7.44/1.48  --qbf_split                             512
% 7.44/1.48  
% 7.44/1.48  ------ BMC1 Options
% 7.44/1.48  
% 7.44/1.48  --bmc1_incremental                      false
% 7.44/1.48  --bmc1_axioms                           reachable_all
% 7.44/1.48  --bmc1_min_bound                        0
% 7.44/1.48  --bmc1_max_bound                        -1
% 7.44/1.48  --bmc1_max_bound_default                -1
% 7.44/1.48  --bmc1_symbol_reachability              true
% 7.44/1.48  --bmc1_property_lemmas                  false
% 7.44/1.48  --bmc1_k_induction                      false
% 7.44/1.48  --bmc1_non_equiv_states                 false
% 7.44/1.48  --bmc1_deadlock                         false
% 7.44/1.48  --bmc1_ucm                              false
% 7.44/1.48  --bmc1_add_unsat_core                   none
% 7.44/1.48  --bmc1_unsat_core_children              false
% 7.44/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.44/1.48  --bmc1_out_stat                         full
% 7.44/1.48  --bmc1_ground_init                      false
% 7.44/1.48  --bmc1_pre_inst_next_state              false
% 7.44/1.48  --bmc1_pre_inst_state                   false
% 7.44/1.48  --bmc1_pre_inst_reach_state             false
% 7.44/1.48  --bmc1_out_unsat_core                   false
% 7.44/1.48  --bmc1_aig_witness_out                  false
% 7.44/1.48  --bmc1_verbose                          false
% 7.44/1.48  --bmc1_dump_clauses_tptp                false
% 7.44/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.44/1.48  --bmc1_dump_file                        -
% 7.44/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.44/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.44/1.48  --bmc1_ucm_extend_mode                  1
% 7.44/1.48  --bmc1_ucm_init_mode                    2
% 7.44/1.48  --bmc1_ucm_cone_mode                    none
% 7.44/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.44/1.48  --bmc1_ucm_relax_model                  4
% 7.44/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.44/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.44/1.48  --bmc1_ucm_layered_model                none
% 7.44/1.48  --bmc1_ucm_max_lemma_size               10
% 7.44/1.48  
% 7.44/1.48  ------ AIG Options
% 7.44/1.48  
% 7.44/1.48  --aig_mode                              false
% 7.44/1.48  
% 7.44/1.48  ------ Instantiation Options
% 7.44/1.48  
% 7.44/1.48  --instantiation_flag                    true
% 7.44/1.48  --inst_sos_flag                         true
% 7.44/1.48  --inst_sos_phase                        true
% 7.44/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.44/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.44/1.48  --inst_lit_sel_side                     none
% 7.44/1.48  --inst_solver_per_active                1400
% 7.44/1.48  --inst_solver_calls_frac                1.
% 7.44/1.48  --inst_passive_queue_type               priority_queues
% 7.44/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.44/1.48  --inst_passive_queues_freq              [25;2]
% 7.44/1.48  --inst_dismatching                      true
% 7.44/1.48  --inst_eager_unprocessed_to_passive     true
% 7.44/1.48  --inst_prop_sim_given                   true
% 7.44/1.48  --inst_prop_sim_new                     false
% 7.44/1.48  --inst_subs_new                         false
% 7.44/1.48  --inst_eq_res_simp                      false
% 7.44/1.48  --inst_subs_given                       false
% 7.44/1.48  --inst_orphan_elimination               true
% 7.44/1.48  --inst_learning_loop_flag               true
% 7.44/1.48  --inst_learning_start                   3000
% 7.44/1.48  --inst_learning_factor                  2
% 7.44/1.48  --inst_start_prop_sim_after_learn       3
% 7.44/1.48  --inst_sel_renew                        solver
% 7.44/1.48  --inst_lit_activity_flag                true
% 7.44/1.48  --inst_restr_to_given                   false
% 7.44/1.48  --inst_activity_threshold               500
% 7.44/1.48  --inst_out_proof                        true
% 7.44/1.48  
% 7.44/1.48  ------ Resolution Options
% 7.44/1.48  
% 7.44/1.48  --resolution_flag                       false
% 7.44/1.48  --res_lit_sel                           adaptive
% 7.44/1.48  --res_lit_sel_side                      none
% 7.44/1.48  --res_ordering                          kbo
% 7.44/1.48  --res_to_prop_solver                    active
% 7.44/1.48  --res_prop_simpl_new                    false
% 7.44/1.48  --res_prop_simpl_given                  true
% 7.44/1.48  --res_passive_queue_type                priority_queues
% 7.44/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.44/1.48  --res_passive_queues_freq               [15;5]
% 7.44/1.48  --res_forward_subs                      full
% 7.44/1.48  --res_backward_subs                     full
% 7.44/1.48  --res_forward_subs_resolution           true
% 7.44/1.48  --res_backward_subs_resolution          true
% 7.44/1.48  --res_orphan_elimination                true
% 7.44/1.48  --res_time_limit                        2.
% 7.44/1.48  --res_out_proof                         true
% 7.44/1.48  
% 7.44/1.48  ------ Superposition Options
% 7.44/1.48  
% 7.44/1.48  --superposition_flag                    true
% 7.44/1.48  --sup_passive_queue_type                priority_queues
% 7.44/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.44/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.44/1.48  --demod_completeness_check              fast
% 7.44/1.48  --demod_use_ground                      true
% 7.44/1.48  --sup_to_prop_solver                    passive
% 7.44/1.48  --sup_prop_simpl_new                    true
% 7.44/1.48  --sup_prop_simpl_given                  true
% 7.44/1.48  --sup_fun_splitting                     true
% 7.44/1.48  --sup_smt_interval                      50000
% 7.44/1.48  
% 7.44/1.48  ------ Superposition Simplification Setup
% 7.44/1.48  
% 7.44/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.44/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.44/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.44/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.44/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.44/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.44/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.44/1.48  --sup_immed_triv                        [TrivRules]
% 7.44/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.44/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.44/1.48  --sup_immed_bw_main                     []
% 7.44/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.44/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.44/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.44/1.48  --sup_input_bw                          []
% 7.44/1.48  
% 7.44/1.48  ------ Combination Options
% 7.44/1.48  
% 7.44/1.48  --comb_res_mult                         3
% 7.44/1.48  --comb_sup_mult                         2
% 7.44/1.48  --comb_inst_mult                        10
% 7.44/1.48  
% 7.44/1.48  ------ Debug Options
% 7.44/1.48  
% 7.44/1.48  --dbg_backtrace                         false
% 7.44/1.48  --dbg_dump_prop_clauses                 false
% 7.44/1.48  --dbg_dump_prop_clauses_file            -
% 7.44/1.48  --dbg_out_stat                          false
% 7.44/1.48  
% 7.44/1.48  
% 7.44/1.48  
% 7.44/1.48  
% 7.44/1.48  ------ Proving...
% 7.44/1.48  
% 7.44/1.48  
% 7.44/1.48  % SZS status Theorem for theBenchmark.p
% 7.44/1.48  
% 7.44/1.48   Resolution empty clause
% 7.44/1.48  
% 7.44/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.44/1.48  
% 7.44/1.48  fof(f1,axiom,(
% 7.44/1.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.44/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.48  
% 7.44/1.48  fof(f38,plain,(
% 7.44/1.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.44/1.48    inference(nnf_transformation,[],[f1])).
% 7.44/1.48  
% 7.44/1.48  fof(f39,plain,(
% 7.44/1.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.44/1.48    inference(flattening,[],[f38])).
% 7.44/1.48  
% 7.44/1.48  fof(f55,plain,(
% 7.44/1.48    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 7.44/1.48    inference(cnf_transformation,[],[f39])).
% 7.44/1.48  
% 7.44/1.48  fof(f94,plain,(
% 7.44/1.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.44/1.48    inference(equality_resolution,[],[f55])).
% 7.44/1.48  
% 7.44/1.48  fof(f4,axiom,(
% 7.44/1.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.44/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.48  
% 7.44/1.48  fof(f42,plain,(
% 7.44/1.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.44/1.48    inference(nnf_transformation,[],[f4])).
% 7.44/1.48  
% 7.44/1.48  fof(f62,plain,(
% 7.44/1.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.44/1.48    inference(cnf_transformation,[],[f42])).
% 7.44/1.48  
% 7.44/1.48  fof(f9,axiom,(
% 7.44/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.44/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.48  
% 7.44/1.48  fof(f25,plain,(
% 7.44/1.48    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.44/1.48    inference(ennf_transformation,[],[f9])).
% 7.44/1.48  
% 7.44/1.48  fof(f67,plain,(
% 7.44/1.48    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.44/1.48    inference(cnf_transformation,[],[f25])).
% 7.44/1.48  
% 7.44/1.48  fof(f10,axiom,(
% 7.44/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.44/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.48  
% 7.44/1.48  fof(f26,plain,(
% 7.44/1.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.44/1.48    inference(ennf_transformation,[],[f10])).
% 7.44/1.48  
% 7.44/1.48  fof(f27,plain,(
% 7.44/1.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.44/1.48    inference(flattening,[],[f26])).
% 7.44/1.48  
% 7.44/1.48  fof(f44,plain,(
% 7.44/1.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.44/1.48    inference(nnf_transformation,[],[f27])).
% 7.44/1.48  
% 7.44/1.48  fof(f71,plain,(
% 7.44/1.48    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.44/1.48    inference(cnf_transformation,[],[f44])).
% 7.44/1.48  
% 7.44/1.48  fof(f101,plain,(
% 7.44/1.48    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 7.44/1.48    inference(equality_resolution,[],[f71])).
% 7.44/1.48  
% 7.44/1.48  fof(f2,axiom,(
% 7.44/1.48    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.44/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.48  
% 7.44/1.48  fof(f40,plain,(
% 7.44/1.48    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 7.44/1.48    inference(nnf_transformation,[],[f2])).
% 7.44/1.48  
% 7.44/1.48  fof(f41,plain,(
% 7.44/1.48    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 7.44/1.48    inference(flattening,[],[f40])).
% 7.44/1.48  
% 7.44/1.48  fof(f58,plain,(
% 7.44/1.48    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 7.44/1.48    inference(cnf_transformation,[],[f41])).
% 7.44/1.48  
% 7.44/1.48  fof(f97,plain,(
% 7.44/1.48    ( ! [X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0) )),
% 7.44/1.48    inference(equality_resolution,[],[f58])).
% 7.44/1.48  
% 7.44/1.48  fof(f3,axiom,(
% 7.44/1.48    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 7.44/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.48  
% 7.44/1.48  fof(f60,plain,(
% 7.44/1.48    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 7.44/1.48    inference(cnf_transformation,[],[f3])).
% 7.44/1.48  
% 7.44/1.48  fof(f8,axiom,(
% 7.44/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.44/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.48  
% 7.44/1.48  fof(f20,plain,(
% 7.44/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.44/1.48    inference(pure_predicate_removal,[],[f8])).
% 7.44/1.48  
% 7.44/1.48  fof(f24,plain,(
% 7.44/1.48    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.44/1.48    inference(ennf_transformation,[],[f20])).
% 7.44/1.48  
% 7.44/1.48  fof(f66,plain,(
% 7.44/1.48    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.44/1.48    inference(cnf_transformation,[],[f24])).
% 7.44/1.48  
% 7.44/1.48  fof(f6,axiom,(
% 7.44/1.48    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 7.44/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.48  
% 7.44/1.48  fof(f22,plain,(
% 7.44/1.48    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.44/1.48    inference(ennf_transformation,[],[f6])).
% 7.44/1.48  
% 7.44/1.48  fof(f43,plain,(
% 7.44/1.48    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.44/1.48    inference(nnf_transformation,[],[f22])).
% 7.44/1.48  
% 7.44/1.48  fof(f63,plain,(
% 7.44/1.48    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.44/1.48    inference(cnf_transformation,[],[f43])).
% 7.44/1.48  
% 7.44/1.48  fof(f7,axiom,(
% 7.44/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.44/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.48  
% 7.44/1.48  fof(f23,plain,(
% 7.44/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.44/1.48    inference(ennf_transformation,[],[f7])).
% 7.44/1.48  
% 7.44/1.48  fof(f65,plain,(
% 7.44/1.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.44/1.48    inference(cnf_transformation,[],[f23])).
% 7.44/1.48  
% 7.44/1.48  fof(f61,plain,(
% 7.44/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.44/1.48    inference(cnf_transformation,[],[f42])).
% 7.44/1.48  
% 7.44/1.48  fof(f56,plain,(
% 7.44/1.48    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.44/1.48    inference(cnf_transformation,[],[f39])).
% 7.44/1.48  
% 7.44/1.48  fof(f16,conjecture,(
% 7.44/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 7.44/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.48  
% 7.44/1.48  fof(f17,negated_conjecture,(
% 7.44/1.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 7.44/1.48    inference(negated_conjecture,[],[f16])).
% 7.44/1.48  
% 7.44/1.48  fof(f36,plain,(
% 7.44/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 7.44/1.48    inference(ennf_transformation,[],[f17])).
% 7.44/1.48  
% 7.44/1.48  fof(f37,plain,(
% 7.44/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.44/1.48    inference(flattening,[],[f36])).
% 7.44/1.48  
% 7.44/1.48  fof(f47,plain,(
% 7.44/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.44/1.48    inference(nnf_transformation,[],[f37])).
% 7.44/1.48  
% 7.44/1.48  fof(f48,plain,(
% 7.44/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.44/1.48    inference(flattening,[],[f47])).
% 7.44/1.48  
% 7.44/1.48  fof(f52,plain,(
% 7.44/1.48    ( ! [X2,X0,X1] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => ((~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & sK3 = X2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(sK3))) )),
% 7.44/1.48    introduced(choice_axiom,[])).
% 7.44/1.48  
% 7.44/1.48  fof(f51,plain,(
% 7.44/1.48    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(sK2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK2,X0,X1)) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 7.44/1.48    introduced(choice_axiom,[])).
% 7.44/1.48  
% 7.44/1.48  fof(f50,plain,(
% 7.44/1.48    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(X2,X0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X2,X0,sK1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))) )),
% 7.44/1.48    introduced(choice_axiom,[])).
% 7.44/1.48  
% 7.44/1.48  fof(f49,plain,(
% 7.44/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 7.44/1.48    introduced(choice_axiom,[])).
% 7.44/1.48  
% 7.44/1.48  fof(f53,plain,(
% 7.44/1.48    ((((~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 7.44/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f48,f52,f51,f50,f49])).
% 7.44/1.48  
% 7.44/1.48  fof(f87,plain,(
% 7.44/1.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 7.44/1.48    inference(cnf_transformation,[],[f53])).
% 7.44/1.48  
% 7.44/1.48  fof(f91,plain,(
% 7.44/1.48    sK2 = sK3),
% 7.44/1.48    inference(cnf_transformation,[],[f53])).
% 7.44/1.48  
% 7.44/1.48  fof(f68,plain,(
% 7.44/1.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.44/1.48    inference(cnf_transformation,[],[f44])).
% 7.44/1.48  
% 7.44/1.48  fof(f86,plain,(
% 7.44/1.48    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 7.44/1.48    inference(cnf_transformation,[],[f53])).
% 7.44/1.48  
% 7.44/1.48  fof(f59,plain,(
% 7.44/1.48    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 7.44/1.48    inference(cnf_transformation,[],[f41])).
% 7.44/1.48  
% 7.44/1.48  fof(f96,plain,(
% 7.44/1.48    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.44/1.48    inference(equality_resolution,[],[f59])).
% 7.44/1.48  
% 7.44/1.48  fof(f93,plain,(
% 7.44/1.48    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)),
% 7.44/1.48    inference(cnf_transformation,[],[f53])).
% 7.44/1.48  
% 7.44/1.48  fof(f90,plain,(
% 7.44/1.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 7.44/1.48    inference(cnf_transformation,[],[f53])).
% 7.44/1.48  
% 7.44/1.48  fof(f89,plain,(
% 7.44/1.48    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 7.44/1.48    inference(cnf_transformation,[],[f53])).
% 7.44/1.48  
% 7.44/1.48  fof(f72,plain,(
% 7.44/1.48    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.44/1.48    inference(cnf_transformation,[],[f44])).
% 7.44/1.48  
% 7.44/1.48  fof(f100,plain,(
% 7.44/1.48    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 7.44/1.48    inference(equality_resolution,[],[f72])).
% 7.44/1.48  
% 7.44/1.48  fof(f15,axiom,(
% 7.44/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 7.44/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.48  
% 7.44/1.48  fof(f34,plain,(
% 7.44/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.44/1.48    inference(ennf_transformation,[],[f15])).
% 7.44/1.48  
% 7.44/1.48  fof(f35,plain,(
% 7.44/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.44/1.48    inference(flattening,[],[f34])).
% 7.44/1.48  
% 7.44/1.48  fof(f46,plain,(
% 7.44/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.44/1.48    inference(nnf_transformation,[],[f35])).
% 7.44/1.48  
% 7.44/1.48  fof(f80,plain,(
% 7.44/1.48    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.44/1.48    inference(cnf_transformation,[],[f46])).
% 7.44/1.48  
% 7.44/1.48  fof(f105,plain,(
% 7.44/1.48    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.44/1.48    inference(equality_resolution,[],[f80])).
% 7.44/1.48  
% 7.44/1.48  fof(f81,plain,(
% 7.44/1.48    v2_pre_topc(sK0)),
% 7.44/1.48    inference(cnf_transformation,[],[f53])).
% 7.44/1.48  
% 7.44/1.48  fof(f82,plain,(
% 7.44/1.48    l1_pre_topc(sK0)),
% 7.44/1.48    inference(cnf_transformation,[],[f53])).
% 7.44/1.48  
% 7.44/1.48  fof(f83,plain,(
% 7.44/1.48    v2_pre_topc(sK1)),
% 7.44/1.48    inference(cnf_transformation,[],[f53])).
% 7.44/1.48  
% 7.44/1.48  fof(f84,plain,(
% 7.44/1.48    l1_pre_topc(sK1)),
% 7.44/1.48    inference(cnf_transformation,[],[f53])).
% 7.44/1.48  
% 7.44/1.48  fof(f88,plain,(
% 7.44/1.48    v1_funct_1(sK3)),
% 7.44/1.48    inference(cnf_transformation,[],[f53])).
% 7.44/1.48  
% 7.44/1.48  fof(f13,axiom,(
% 7.44/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 7.44/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.48  
% 7.44/1.48  fof(f18,plain,(
% 7.44/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 7.44/1.48    inference(pure_predicate_removal,[],[f13])).
% 7.44/1.48  
% 7.44/1.48  fof(f30,plain,(
% 7.44/1.48    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.44/1.48    inference(ennf_transformation,[],[f18])).
% 7.44/1.48  
% 7.44/1.48  fof(f31,plain,(
% 7.44/1.48    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.44/1.48    inference(flattening,[],[f30])).
% 7.44/1.48  
% 7.44/1.48  fof(f76,plain,(
% 7.44/1.48    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.44/1.48    inference(cnf_transformation,[],[f31])).
% 7.44/1.48  
% 7.44/1.48  fof(f11,axiom,(
% 7.44/1.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 7.44/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.48  
% 7.44/1.48  fof(f19,plain,(
% 7.44/1.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 7.44/1.48    inference(pure_predicate_removal,[],[f11])).
% 7.44/1.48  
% 7.44/1.48  fof(f28,plain,(
% 7.44/1.48    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 7.44/1.48    inference(ennf_transformation,[],[f19])).
% 7.44/1.48  
% 7.44/1.48  fof(f74,plain,(
% 7.44/1.48    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 7.44/1.48    inference(cnf_transformation,[],[f28])).
% 7.44/1.48  
% 7.44/1.48  fof(f12,axiom,(
% 7.44/1.48    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.44/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.48  
% 7.44/1.48  fof(f29,plain,(
% 7.44/1.48    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.44/1.48    inference(ennf_transformation,[],[f12])).
% 7.44/1.48  
% 7.44/1.48  fof(f75,plain,(
% 7.44/1.48    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 7.44/1.48    inference(cnf_transformation,[],[f29])).
% 7.44/1.48  
% 7.44/1.48  fof(f79,plain,(
% 7.44/1.48    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.44/1.48    inference(cnf_transformation,[],[f46])).
% 7.44/1.48  
% 7.44/1.48  fof(f106,plain,(
% 7.44/1.48    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.44/1.48    inference(equality_resolution,[],[f79])).
% 7.44/1.48  
% 7.44/1.48  fof(f14,axiom,(
% 7.44/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 7.44/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.48  
% 7.44/1.48  fof(f32,plain,(
% 7.44/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.44/1.48    inference(ennf_transformation,[],[f14])).
% 7.44/1.48  
% 7.44/1.48  fof(f33,plain,(
% 7.44/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.44/1.48    inference(flattening,[],[f32])).
% 7.44/1.48  
% 7.44/1.48  fof(f45,plain,(
% 7.44/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.44/1.48    inference(nnf_transformation,[],[f33])).
% 7.44/1.48  
% 7.44/1.48  fof(f78,plain,(
% 7.44/1.48    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.44/1.48    inference(cnf_transformation,[],[f45])).
% 7.44/1.48  
% 7.44/1.48  fof(f103,plain,(
% 7.44/1.48    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.44/1.48    inference(equality_resolution,[],[f78])).
% 7.44/1.48  
% 7.44/1.48  fof(f92,plain,(
% 7.44/1.48    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)),
% 7.44/1.48    inference(cnf_transformation,[],[f53])).
% 7.44/1.48  
% 7.44/1.48  fof(f77,plain,(
% 7.44/1.48    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.44/1.48    inference(cnf_transformation,[],[f45])).
% 7.44/1.48  
% 7.44/1.48  fof(f104,plain,(
% 7.44/1.48    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.44/1.48    inference(equality_resolution,[],[f77])).
% 7.44/1.48  
% 7.44/1.48  fof(f57,plain,(
% 7.44/1.48    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0) )),
% 7.44/1.48    inference(cnf_transformation,[],[f41])).
% 7.44/1.48  
% 7.44/1.48  cnf(c_1,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f94]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_2351,plain,
% 7.44/1.48      ( r1_tarski(X0,X0) = iProver_top ),
% 7.44/1.48      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_7,plain,
% 7.44/1.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.44/1.48      inference(cnf_transformation,[],[f62]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_2349,plain,
% 7.44/1.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.44/1.48      | r1_tarski(X0,X1) != iProver_top ),
% 7.44/1.48      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_13,plain,
% 7.44/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.44/1.48      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.44/1.48      inference(cnf_transformation,[],[f67]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_2347,plain,
% 7.44/1.48      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.44/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.44/1.48      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_3859,plain,
% 7.44/1.48      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.44/1.48      | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 7.44/1.48      inference(superposition,[status(thm)],[c_2349,c_2347]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_14184,plain,
% 7.44/1.48      ( k1_relset_1(X0,X1,k2_zfmisc_1(X0,X1)) = k1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.44/1.48      inference(superposition,[status(thm)],[c_2351,c_3859]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_16,plain,
% 7.44/1.48      ( v1_funct_2(X0,k1_xboole_0,X1)
% 7.44/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.44/1.48      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 7.44/1.48      inference(cnf_transformation,[],[f101]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_2344,plain,
% 7.44/1.48      ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
% 7.44/1.48      | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
% 7.44/1.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 7.44/1.48      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_4,plain,
% 7.44/1.48      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.44/1.48      inference(cnf_transformation,[],[f97]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_2360,plain,
% 7.44/1.48      ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
% 7.44/1.48      | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
% 7.44/1.48      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.44/1.48      inference(light_normalisation,[status(thm)],[c_2344,c_4]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_15673,plain,
% 7.44/1.48      ( k1_relat_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_xboole_0
% 7.44/1.48      | v1_funct_2(k2_zfmisc_1(k1_xboole_0,X0),k1_xboole_0,X0) = iProver_top
% 7.44/1.48      | m1_subset_1(k2_zfmisc_1(k1_xboole_0,X0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.44/1.48      inference(superposition,[status(thm)],[c_14184,c_2360]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_6,plain,
% 7.44/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 7.44/1.48      inference(cnf_transformation,[],[f60]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_2350,plain,
% 7.44/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.44/1.48      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_12,plain,
% 7.44/1.48      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.44/1.48      inference(cnf_transformation,[],[f66]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_10,plain,
% 7.44/1.48      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 7.44/1.48      inference(cnf_transformation,[],[f63]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_514,plain,
% 7.44/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.44/1.48      | r1_tarski(k1_relat_1(X0),X1)
% 7.44/1.48      | ~ v1_relat_1(X0) ),
% 7.44/1.48      inference(resolution,[status(thm)],[c_12,c_10]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_11,plain,
% 7.44/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 7.44/1.48      inference(cnf_transformation,[],[f65]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_518,plain,
% 7.44/1.48      ( r1_tarski(k1_relat_1(X0),X1)
% 7.44/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.44/1.48      inference(global_propositional_subsumption,[status(thm)],[c_514,c_11]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_519,plain,
% 7.44/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.44/1.48      | r1_tarski(k1_relat_1(X0),X1) ),
% 7.44/1.48      inference(renaming,[status(thm)],[c_518]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_2321,plain,
% 7.44/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.44/1.48      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 7.44/1.48      inference(predicate_to_equality,[status(thm)],[c_519]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_3160,plain,
% 7.44/1.48      ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
% 7.44/1.48      inference(superposition,[status(thm)],[c_2350,c_2321]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_8,plain,
% 7.44/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.44/1.48      inference(cnf_transformation,[],[f61]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_2348,plain,
% 7.44/1.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.44/1.48      | r1_tarski(X0,X1) = iProver_top ),
% 7.44/1.48      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_3292,plain,
% 7.44/1.48      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.44/1.48      inference(superposition,[status(thm)],[c_2350,c_2348]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_0,plain,
% 7.44/1.48      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.44/1.48      inference(cnf_transformation,[],[f56]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_2352,plain,
% 7.44/1.48      ( X0 = X1
% 7.44/1.48      | r1_tarski(X0,X1) != iProver_top
% 7.44/1.48      | r1_tarski(X1,X0) != iProver_top ),
% 7.44/1.48      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_4397,plain,
% 7.44/1.48      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 7.44/1.48      inference(superposition,[status(thm)],[c_3292,c_2352]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_4838,plain,
% 7.44/1.48      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.44/1.48      inference(superposition,[status(thm)],[c_3160,c_4397]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_15674,plain,
% 7.44/1.48      ( k1_xboole_0 != k1_xboole_0
% 7.44/1.48      | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top
% 7.44/1.48      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.44/1.48      inference(light_normalisation,[status(thm)],[c_15673,c_4,c_4838]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_15675,plain,
% 7.44/1.48      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top
% 7.44/1.48      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.44/1.48      inference(equality_resolution_simp,[status(thm)],[c_15674]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_112,plain,
% 7.44/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.44/1.48      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_114,plain,
% 7.44/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.44/1.48      inference(instantiation,[status(thm)],[c_112]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_17410,plain,
% 7.44/1.48      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top ),
% 7.44/1.48      inference(global_propositional_subsumption,[status(thm)],[c_15675,c_114]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_33,negated_conjecture,
% 7.44/1.48      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 7.44/1.48      inference(cnf_transformation,[],[f87]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_2328,plain,
% 7.44/1.48      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 7.44/1.48      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_29,negated_conjecture,
% 7.44/1.48      ( sK2 = sK3 ),
% 7.44/1.48      inference(cnf_transformation,[],[f91]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_2355,plain,
% 7.44/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 7.44/1.48      inference(light_normalisation,[status(thm)],[c_2328,c_29]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_19,plain,
% 7.44/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.44/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.44/1.48      | k1_relset_1(X1,X2,X0) = X1
% 7.44/1.48      | k1_xboole_0 = X2 ),
% 7.44/1.48      inference(cnf_transformation,[],[f68]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_2341,plain,
% 7.44/1.48      ( k1_relset_1(X0,X1,X2) = X0
% 7.44/1.48      | k1_xboole_0 = X1
% 7.44/1.48      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.44/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.44/1.48      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_5269,plain,
% 7.44/1.48      ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3) = u1_struct_0(sK0)
% 7.44/1.48      | u1_struct_0(sK1) = k1_xboole_0
% 7.44/1.48      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top ),
% 7.44/1.48      inference(superposition,[status(thm)],[c_2355,c_2341]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_3861,plain,
% 7.44/1.48      ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3) = k1_relat_1(sK3) ),
% 7.44/1.48      inference(superposition,[status(thm)],[c_2355,c_2347]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_5272,plain,
% 7.44/1.48      ( u1_struct_0(sK1) = k1_xboole_0
% 7.44/1.48      | u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.44/1.48      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top ),
% 7.44/1.48      inference(light_normalisation,[status(thm)],[c_5269,c_3861]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_34,negated_conjecture,
% 7.44/1.48      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 7.44/1.48      inference(cnf_transformation,[],[f86]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_2327,plain,
% 7.44/1.48      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 7.44/1.48      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_2354,plain,
% 7.44/1.48      ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 7.44/1.48      inference(light_normalisation,[status(thm)],[c_2327,c_29]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_5280,plain,
% 7.44/1.48      ( u1_struct_0(sK0) = k1_relat_1(sK3) | u1_struct_0(sK1) = k1_xboole_0 ),
% 7.44/1.48      inference(global_propositional_subsumption,[status(thm)],[c_5272,c_2354]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_5281,plain,
% 7.44/1.48      ( u1_struct_0(sK1) = k1_xboole_0 | u1_struct_0(sK0) = k1_relat_1(sK3) ),
% 7.44/1.48      inference(renaming,[status(thm)],[c_5280]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_3294,plain,
% 7.44/1.48      ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 7.44/1.48      inference(superposition,[status(thm)],[c_2355,c_2348]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_5304,plain,
% 7.44/1.48      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.44/1.48      | r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)) = iProver_top ),
% 7.44/1.48      inference(superposition,[status(thm)],[c_5281,c_3294]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_3,plain,
% 7.44/1.48      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.44/1.48      inference(cnf_transformation,[],[f96]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_5312,plain,
% 7.44/1.48      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.44/1.48      | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 7.44/1.48      inference(demodulation,[status(thm)],[c_5304,c_3]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_5776,plain,
% 7.44/1.48      ( u1_struct_0(sK0) = k1_relat_1(sK3) | sK3 = k1_xboole_0 ),
% 7.44/1.48      inference(superposition,[status(thm)],[c_5312,c_4397]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_27,negated_conjecture,
% 7.44/1.48      ( ~ v5_pre_topc(sK2,sK0,sK1)
% 7.44/1.48      | ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 7.44/1.48      inference(cnf_transformation,[],[f93]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_2333,plain,
% 7.44/1.48      ( v5_pre_topc(sK2,sK0,sK1) != iProver_top
% 7.44/1.48      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 7.44/1.48      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_2358,plain,
% 7.44/1.48      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.44/1.48      | v5_pre_topc(sK3,sK0,sK1) != iProver_top ),
% 7.44/1.48      inference(light_normalisation,[status(thm)],[c_2333,c_29]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_15413,plain,
% 7.44/1.48      ( sK3 = k1_xboole_0
% 7.44/1.48      | v5_pre_topc(sK3,g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.44/1.48      | v5_pre_topc(sK3,sK0,sK1) != iProver_top ),
% 7.44/1.48      inference(superposition,[status(thm)],[c_5776,c_2358]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_30,negated_conjecture,
% 7.44/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
% 7.44/1.48      inference(cnf_transformation,[],[f90]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_2331,plain,
% 7.44/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
% 7.44/1.48      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_5268,plain,
% 7.44/1.48      ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 7.44/1.48      | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
% 7.44/1.48      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
% 7.44/1.48      inference(superposition,[status(thm)],[c_2331,c_2341]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_3860,plain,
% 7.44/1.48      ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3) = k1_relat_1(sK3) ),
% 7.44/1.48      inference(superposition,[status(thm)],[c_2331,c_2347]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_5273,plain,
% 7.44/1.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
% 7.44/1.48      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.44/1.48      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
% 7.44/1.48      inference(light_normalisation,[status(thm)],[c_5268,c_3860]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_31,negated_conjecture,
% 7.44/1.48      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
% 7.44/1.48      inference(cnf_transformation,[],[f89]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_5277,plain,
% 7.44/1.48      ( ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 7.44/1.48      | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
% 7.44/1.48      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
% 7.44/1.48      inference(predicate_to_equality_rev,[status(thm)],[c_5273]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_6208,plain,
% 7.44/1.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.44/1.48      | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0 ),
% 7.44/1.48      inference(global_propositional_subsumption,
% 7.44/1.48                [status(thm)],
% 7.44/1.48                [c_5273,c_31,c_5277]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_6209,plain,
% 7.44/1.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
% 7.44/1.48      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
% 7.44/1.48      inference(renaming,[status(thm)],[c_6208]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_6233,plain,
% 7.44/1.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.44/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) = iProver_top ),
% 7.44/1.48      inference(superposition,[status(thm)],[c_6209,c_2331]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_6235,plain,
% 7.44/1.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.44/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.44/1.48      inference(demodulation,[status(thm)],[c_6233,c_3]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_5310,plain,
% 7.44/1.48      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.44/1.48      | v1_funct_2(sK3,u1_struct_0(sK0),k1_xboole_0) = iProver_top ),
% 7.44/1.48      inference(superposition,[status(thm)],[c_5281,c_2354]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_15,plain,
% 7.44/1.48      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 7.44/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 7.44/1.48      | k1_xboole_0 = X1
% 7.44/1.48      | k1_xboole_0 = X0 ),
% 7.44/1.48      inference(cnf_transformation,[],[f100]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_2345,plain,
% 7.44/1.48      ( k1_xboole_0 = X0
% 7.44/1.48      | k1_xboole_0 = X1
% 7.44/1.48      | v1_funct_2(X1,X0,k1_xboole_0) != iProver_top
% 7.44/1.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) != iProver_top ),
% 7.44/1.48      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_2361,plain,
% 7.44/1.48      ( k1_xboole_0 = X0
% 7.44/1.48      | k1_xboole_0 = X1
% 7.44/1.48      | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
% 7.44/1.48      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.44/1.48      inference(light_normalisation,[status(thm)],[c_2345,c_3]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_5405,plain,
% 7.44/1.48      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.44/1.48      | u1_struct_0(sK0) = k1_xboole_0
% 7.44/1.48      | sK3 = k1_xboole_0
% 7.44/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.44/1.48      inference(superposition,[status(thm)],[c_5310,c_2361]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_2666,plain,
% 7.44/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3)) | r1_tarski(X0,sK3) ),
% 7.44/1.48      inference(instantiation,[status(thm)],[c_8]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_2667,plain,
% 7.44/1.48      ( m1_subset_1(X0,k1_zfmisc_1(sK3)) != iProver_top
% 7.44/1.48      | r1_tarski(X0,sK3) = iProver_top ),
% 7.44/1.48      inference(predicate_to_equality,[status(thm)],[c_2666]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_2669,plain,
% 7.44/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) != iProver_top
% 7.44/1.48      | r1_tarski(k1_xboole_0,sK3) = iProver_top ),
% 7.44/1.48      inference(instantiation,[status(thm)],[c_2667]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_2698,plain,
% 7.44/1.48      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | sK3 = X0 ),
% 7.44/1.48      inference(instantiation,[status(thm)],[c_0]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_2699,plain,
% 7.44/1.48      ( sK3 = X0
% 7.44/1.48      | r1_tarski(X0,sK3) != iProver_top
% 7.44/1.48      | r1_tarski(sK3,X0) != iProver_top ),
% 7.44/1.48      inference(predicate_to_equality,[status(thm)],[c_2698]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_2701,plain,
% 7.44/1.48      ( sK3 = k1_xboole_0
% 7.44/1.48      | r1_tarski(sK3,k1_xboole_0) != iProver_top
% 7.44/1.48      | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 7.44/1.48      inference(instantiation,[status(thm)],[c_2699]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_3279,plain,
% 7.44/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) ),
% 7.44/1.48      inference(instantiation,[status(thm)],[c_6]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_3280,plain,
% 7.44/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) = iProver_top ),
% 7.44/1.48      inference(predicate_to_equality,[status(thm)],[c_3279]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_4005,plain,
% 7.44/1.48      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0)) | r1_tarski(sK3,X0) ),
% 7.44/1.48      inference(instantiation,[status(thm)],[c_8]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_4006,plain,
% 7.44/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 7.44/1.48      | r1_tarski(sK3,X0) = iProver_top ),
% 7.44/1.48      inference(predicate_to_equality,[status(thm)],[c_4005]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_4008,plain,
% 7.44/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.44/1.48      | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 7.44/1.48      inference(instantiation,[status(thm)],[c_4006]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_6200,plain,
% 7.44/1.48      ( sK3 = k1_xboole_0
% 7.44/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.44/1.48      inference(global_propositional_subsumption,
% 7.44/1.48                [status(thm)],
% 7.44/1.48                [c_5405,c_2669,c_2701,c_3280,c_4008]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_6340,plain,
% 7.44/1.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.44/1.48      | sK3 = k1_xboole_0 ),
% 7.44/1.48      inference(superposition,[status(thm)],[c_6235,c_6200]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_25,plain,
% 7.44/1.48      ( v5_pre_topc(X0,X1,X2)
% 7.44/1.48      | ~ v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 7.44/1.48      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.44/1.48      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 7.44/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.44/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 7.44/1.48      | ~ v1_funct_1(X0)
% 7.44/1.48      | ~ v2_pre_topc(X1)
% 7.44/1.48      | ~ v2_pre_topc(X2)
% 7.44/1.48      | ~ l1_pre_topc(X1)
% 7.44/1.48      | ~ l1_pre_topc(X2) ),
% 7.44/1.48      inference(cnf_transformation,[],[f105]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_2335,plain,
% 7.44/1.48      ( v5_pre_topc(X0,X1,X2) = iProver_top
% 7.44/1.48      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) != iProver_top
% 7.44/1.48      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 7.44/1.48      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 7.44/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 7.44/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 7.44/1.48      | v1_funct_1(X0) != iProver_top
% 7.44/1.48      | v2_pre_topc(X1) != iProver_top
% 7.44/1.48      | v2_pre_topc(X2) != iProver_top
% 7.44/1.48      | l1_pre_topc(X1) != iProver_top
% 7.44/1.48      | l1_pre_topc(X2) != iProver_top ),
% 7.44/1.48      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_3702,plain,
% 7.44/1.48      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.44/1.48      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top
% 7.44/1.48      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.44/1.48      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 7.44/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 7.44/1.48      | v1_funct_1(sK3) != iProver_top
% 7.44/1.48      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 7.44/1.48      | v2_pre_topc(sK1) != iProver_top
% 7.44/1.48      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 7.44/1.48      | l1_pre_topc(sK1) != iProver_top ),
% 7.44/1.48      inference(superposition,[status(thm)],[c_2331,c_2335]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_39,negated_conjecture,
% 7.44/1.48      ( v2_pre_topc(sK0) ),
% 7.44/1.48      inference(cnf_transformation,[],[f81]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_40,plain,
% 7.44/1.48      ( v2_pre_topc(sK0) = iProver_top ),
% 7.44/1.48      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_38,negated_conjecture,
% 7.44/1.48      ( l1_pre_topc(sK0) ),
% 7.44/1.48      inference(cnf_transformation,[],[f82]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_41,plain,
% 7.44/1.48      ( l1_pre_topc(sK0) = iProver_top ),
% 7.44/1.48      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_37,negated_conjecture,
% 7.44/1.48      ( v2_pre_topc(sK1) ),
% 7.44/1.48      inference(cnf_transformation,[],[f83]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_42,plain,
% 7.44/1.48      ( v2_pre_topc(sK1) = iProver_top ),
% 7.44/1.48      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_36,negated_conjecture,
% 7.44/1.48      ( l1_pre_topc(sK1) ),
% 7.44/1.48      inference(cnf_transformation,[],[f84]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_43,plain,
% 7.44/1.48      ( l1_pre_topc(sK1) = iProver_top ),
% 7.44/1.48      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_32,negated_conjecture,
% 7.44/1.48      ( v1_funct_1(sK3) ),
% 7.44/1.48      inference(cnf_transformation,[],[f88]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_47,plain,
% 7.44/1.48      ( v1_funct_1(sK3) = iProver_top ),
% 7.44/1.48      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_48,plain,
% 7.44/1.48      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
% 7.44/1.48      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_22,plain,
% 7.44/1.48      ( ~ v2_pre_topc(X0)
% 7.44/1.48      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 7.44/1.48      | ~ l1_pre_topc(X0) ),
% 7.44/1.48      inference(cnf_transformation,[],[f76]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_2487,plain,
% 7.44/1.48      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 7.44/1.48      | ~ v2_pre_topc(sK0)
% 7.44/1.48      | ~ l1_pre_topc(sK0) ),
% 7.44/1.48      inference(instantiation,[status(thm)],[c_22]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_2488,plain,
% 7.44/1.48      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
% 7.44/1.48      | v2_pre_topc(sK0) != iProver_top
% 7.44/1.48      | l1_pre_topc(sK0) != iProver_top ),
% 7.44/1.48      inference(predicate_to_equality,[status(thm)],[c_2487]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_20,plain,
% 7.44/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 7.44/1.48      | l1_pre_topc(g1_pre_topc(X1,X0)) ),
% 7.44/1.48      inference(cnf_transformation,[],[f74]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_2709,plain,
% 7.44/1.48      ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 7.44/1.48      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 7.44/1.48      inference(instantiation,[status(thm)],[c_20]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_2710,plain,
% 7.44/1.48      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 7.44/1.48      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top ),
% 7.44/1.48      inference(predicate_to_equality,[status(thm)],[c_2709]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_21,plain,
% 7.44/1.48      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 7.44/1.48      | ~ l1_pre_topc(X0) ),
% 7.44/1.48      inference(cnf_transformation,[],[f75]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_2903,plain,
% 7.44/1.48      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 7.44/1.48      | ~ l1_pre_topc(sK0) ),
% 7.44/1.48      inference(instantiation,[status(thm)],[c_21]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_2904,plain,
% 7.44/1.48      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 7.44/1.48      | l1_pre_topc(sK0) != iProver_top ),
% 7.44/1.48      inference(predicate_to_equality,[status(thm)],[c_2903]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_26,plain,
% 7.44/1.48      ( ~ v5_pre_topc(X0,X1,X2)
% 7.44/1.48      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 7.44/1.48      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.44/1.48      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 7.44/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.44/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 7.44/1.48      | ~ v1_funct_1(X0)
% 7.44/1.48      | ~ v2_pre_topc(X1)
% 7.44/1.48      | ~ v2_pre_topc(X2)
% 7.44/1.48      | ~ l1_pre_topc(X1)
% 7.44/1.48      | ~ l1_pre_topc(X2) ),
% 7.44/1.48      inference(cnf_transformation,[],[f106]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_2334,plain,
% 7.44/1.48      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 7.44/1.48      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) = iProver_top
% 7.44/1.48      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 7.44/1.48      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 7.44/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 7.44/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 7.44/1.48      | v1_funct_1(X0) != iProver_top
% 7.44/1.48      | v2_pre_topc(X1) != iProver_top
% 7.44/1.48      | v2_pre_topc(X2) != iProver_top
% 7.44/1.48      | l1_pre_topc(X1) != iProver_top
% 7.44/1.48      | l1_pre_topc(X2) != iProver_top ),
% 7.44/1.48      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_3286,plain,
% 7.44/1.48      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 7.44/1.48      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
% 7.44/1.48      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.44/1.48      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 7.44/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 7.44/1.48      | v1_funct_1(sK3) != iProver_top
% 7.44/1.48      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 7.44/1.48      | v2_pre_topc(sK1) != iProver_top
% 7.44/1.48      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 7.44/1.48      | l1_pre_topc(sK1) != iProver_top ),
% 7.44/1.48      inference(superposition,[status(thm)],[c_2331,c_2334]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_23,plain,
% 7.44/1.48      ( v5_pre_topc(X0,X1,X2)
% 7.44/1.48      | ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 7.44/1.48      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.44/1.48      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 7.44/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.44/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 7.44/1.48      | ~ v1_funct_1(X0)
% 7.44/1.48      | ~ v2_pre_topc(X1)
% 7.44/1.48      | ~ v2_pre_topc(X2)
% 7.44/1.48      | ~ l1_pre_topc(X1)
% 7.44/1.48      | ~ l1_pre_topc(X2) ),
% 7.44/1.48      inference(cnf_transformation,[],[f103]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_2873,plain,
% 7.44/1.48      ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)
% 7.44/1.48      | v5_pre_topc(sK3,sK0,X0)
% 7.44/1.48      | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X0))
% 7.44/1.48      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(X0))
% 7.44/1.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X0))))
% 7.44/1.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
% 7.44/1.48      | ~ v1_funct_1(sK3)
% 7.44/1.48      | ~ v2_pre_topc(X0)
% 7.44/1.48      | ~ v2_pre_topc(sK0)
% 7.44/1.48      | ~ l1_pre_topc(X0)
% 7.44/1.48      | ~ l1_pre_topc(sK0) ),
% 7.44/1.48      inference(instantiation,[status(thm)],[c_23]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_3172,plain,
% 7.44/1.48      ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
% 7.44/1.48      | v5_pre_topc(sK3,sK0,sK1)
% 7.44/1.48      | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
% 7.44/1.48      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
% 7.44/1.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
% 7.44/1.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 7.44/1.48      | ~ v1_funct_1(sK3)
% 7.44/1.48      | ~ v2_pre_topc(sK1)
% 7.44/1.48      | ~ v2_pre_topc(sK0)
% 7.44/1.48      | ~ l1_pre_topc(sK1)
% 7.44/1.48      | ~ l1_pre_topc(sK0) ),
% 7.44/1.48      inference(instantiation,[status(thm)],[c_2873]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_3173,plain,
% 7.44/1.48      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
% 7.44/1.48      | v5_pre_topc(sK3,sK0,sK1) = iProver_top
% 7.44/1.48      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 7.44/1.48      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.44/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 7.44/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 7.44/1.48      | v1_funct_1(sK3) != iProver_top
% 7.44/1.48      | v2_pre_topc(sK1) != iProver_top
% 7.44/1.48      | v2_pre_topc(sK0) != iProver_top
% 7.44/1.48      | l1_pre_topc(sK1) != iProver_top
% 7.44/1.48      | l1_pre_topc(sK0) != iProver_top ),
% 7.44/1.48      inference(predicate_to_equality,[status(thm)],[c_3172]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_3510,plain,
% 7.44/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 7.44/1.48      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 7.44/1.48      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top ),
% 7.44/1.48      inference(global_propositional_subsumption,
% 7.44/1.48                [status(thm)],
% 7.44/1.48                [c_3286,c_40,c_41,c_42,c_43,c_47,c_48,c_2355,c_2354,c_2358,
% 7.44/1.48                 c_2488,c_2710,c_2904,c_3173]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_3511,plain,
% 7.44/1.48      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
% 7.44/1.48      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 7.44/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
% 7.44/1.48      inference(renaming,[status(thm)],[c_3510]) ).
% 7.44/1.48  
% 7.44/1.48  cnf(c_4061,plain,
% 7.44/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 7.44/1.48      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 7.44/1.48      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 7.44/1.48      inference(global_propositional_subsumption,
% 7.44/1.48                [status(thm)],
% 7.44/1.48                [c_3702,c_40,c_41,c_42,c_43,c_47,c_48,c_2355,c_2354,c_2358,
% 7.44/1.48                 c_2488,c_2710,c_2904,c_3173,c_3286]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_4062,plain,
% 7.44/1.49      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.44/1.49      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 7.44/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
% 7.44/1.49      inference(renaming,[status(thm)],[c_4061]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_5298,plain,
% 7.44/1.49      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.44/1.49      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) != iProver_top
% 7.44/1.49      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 7.44/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_5281,c_4062]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_28,negated_conjecture,
% 7.44/1.49      ( v5_pre_topc(sK2,sK0,sK1)
% 7.44/1.49      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 7.44/1.49      inference(cnf_transformation,[],[f92]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_2332,plain,
% 7.44/1.49      ( v5_pre_topc(sK2,sK0,sK1) = iProver_top
% 7.44/1.49      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
% 7.44/1.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_2357,plain,
% 7.44/1.49      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 7.44/1.49      | v5_pre_topc(sK3,sK0,sK1) = iProver_top ),
% 7.44/1.49      inference(light_normalisation,[status(thm)],[c_2332,c_29]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_4065,plain,
% 7.44/1.49      ( v5_pre_topc(sK3,sK0,sK1) = iProver_top
% 7.44/1.49      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 7.44/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_2357,c_4062]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_24,plain,
% 7.44/1.49      ( ~ v5_pre_topc(X0,X1,X2)
% 7.44/1.49      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 7.44/1.49      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.44/1.49      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 7.44/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.44/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 7.44/1.49      | ~ v1_funct_1(X0)
% 7.44/1.49      | ~ v2_pre_topc(X1)
% 7.44/1.49      | ~ v2_pre_topc(X2)
% 7.44/1.49      | ~ l1_pre_topc(X1)
% 7.44/1.49      | ~ l1_pre_topc(X2) ),
% 7.44/1.49      inference(cnf_transformation,[],[f104]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_3072,plain,
% 7.44/1.49      ( ~ v5_pre_topc(sK3,X0,sK1)
% 7.44/1.49      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1)
% 7.44/1.49      | ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(sK1))
% 7.44/1.49      | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK1))
% 7.44/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
% 7.44/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK1))))
% 7.44/1.49      | ~ v1_funct_1(sK3)
% 7.44/1.49      | ~ v2_pre_topc(X0)
% 7.44/1.49      | ~ v2_pre_topc(sK1)
% 7.44/1.49      | ~ l1_pre_topc(X0)
% 7.44/1.49      | ~ l1_pre_topc(sK1) ),
% 7.44/1.49      inference(instantiation,[status(thm)],[c_24]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_4472,plain,
% 7.44/1.49      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
% 7.44/1.49      | ~ v5_pre_topc(sK3,sK0,sK1)
% 7.44/1.49      | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
% 7.44/1.49      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
% 7.44/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
% 7.44/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 7.44/1.49      | ~ v1_funct_1(sK3)
% 7.44/1.49      | ~ v2_pre_topc(sK1)
% 7.44/1.49      | ~ v2_pre_topc(sK0)
% 7.44/1.49      | ~ l1_pre_topc(sK1)
% 7.44/1.49      | ~ l1_pre_topc(sK0) ),
% 7.44/1.49      inference(instantiation,[status(thm)],[c_3072]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_4473,plain,
% 7.44/1.49      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top
% 7.44/1.49      | v5_pre_topc(sK3,sK0,sK1) != iProver_top
% 7.44/1.49      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 7.44/1.49      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.44/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 7.44/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 7.44/1.49      | v1_funct_1(sK3) != iProver_top
% 7.44/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.44/1.49      | v2_pre_topc(sK0) != iProver_top
% 7.44/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.44/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 7.44/1.49      inference(predicate_to_equality,[status(thm)],[c_4472]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_5652,plain,
% 7.44/1.49      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 7.44/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
% 7.44/1.49      inference(global_propositional_subsumption,
% 7.44/1.49                [status(thm)],
% 7.44/1.49                [c_5298,c_40,c_41,c_42,c_43,c_47,c_2355,c_2354,c_3511,c_4065,
% 7.44/1.49                 c_4473]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_9880,plain,
% 7.44/1.49      ( sK3 = k1_xboole_0
% 7.44/1.49      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 7.44/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1)))) != iProver_top ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_6340,c_5652]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_11010,plain,
% 7.44/1.49      ( sK3 = k1_xboole_0
% 7.44/1.49      | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK1)) != iProver_top
% 7.44/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1)))) != iProver_top ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_6340,c_9880]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_15416,plain,
% 7.44/1.49      ( sK3 = k1_xboole_0
% 7.44/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_5776,c_2355]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_15417,plain,
% 7.44/1.49      ( sK3 = k1_xboole_0
% 7.44/1.49      | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK1)) = iProver_top ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_5776,c_2354]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_15834,plain,
% 7.44/1.49      ( sK3 = k1_xboole_0 ),
% 7.44/1.49      inference(global_propositional_subsumption,
% 7.44/1.49                [status(thm)],
% 7.44/1.49                [c_15413,c_11010,c_15416,c_15417]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_5656,plain,
% 7.44/1.49      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 7.44/1.49      | r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))) != iProver_top ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_2349,c_5652]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_15891,plain,
% 7.44/1.49      ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 7.44/1.49      | r1_tarski(k1_xboole_0,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))) != iProver_top ),
% 7.44/1.49      inference(demodulation,[status(thm)],[c_15834,c_5656]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_17690,plain,
% 7.44/1.49      ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_3292,c_15891]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_4402,plain,
% 7.44/1.49      ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = sK3
% 7.44/1.49      | r1_tarski(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),sK3) != iProver_top ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_3294,c_2352]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_5294,plain,
% 7.44/1.49      ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = sK3
% 7.44/1.49      | u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.44/1.49      | r1_tarski(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0),sK3) != iProver_top ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_5281,c_4402]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_5317,plain,
% 7.44/1.49      ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = sK3
% 7.44/1.49      | u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.44/1.49      | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 7.44/1.49      inference(demodulation,[status(thm)],[c_5294,c_3]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_5929,plain,
% 7.44/1.49      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.44/1.49      | k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = sK3 ),
% 7.44/1.49      inference(global_propositional_subsumption,
% 7.44/1.49                [status(thm)],
% 7.44/1.49                [c_5317,c_2669,c_3280]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_5930,plain,
% 7.44/1.49      ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = sK3
% 7.44/1.49      | u1_struct_0(sK0) = k1_relat_1(sK3) ),
% 7.44/1.49      inference(renaming,[status(thm)],[c_5929]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_15671,plain,
% 7.44/1.49      ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3) = k1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 7.44/1.49      | u1_struct_0(sK0) = k1_relat_1(sK3) ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_5930,c_14184]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_15676,plain,
% 7.44/1.49      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.44/1.49      | k1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = k1_relat_1(sK3) ),
% 7.44/1.49      inference(light_normalisation,[status(thm)],[c_15671,c_3861]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_18207,plain,
% 7.44/1.49      ( u1_struct_0(sK0) = k1_xboole_0
% 7.44/1.49      | k1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = k1_xboole_0 ),
% 7.44/1.49      inference(light_normalisation,[status(thm)],[c_15676,c_4838,c_15834]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_2370,plain,
% 7.44/1.49      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 7.44/1.49      | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top
% 7.44/1.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.44/1.49      inference(instantiation,[status(thm)],[c_2360]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_3858,plain,
% 7.44/1.49      ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_2350,c_2347]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_4842,plain,
% 7.44/1.49      ( k1_relset_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
% 7.44/1.49      inference(demodulation,[status(thm)],[c_4838,c_3858]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_4844,plain,
% 7.44/1.49      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.44/1.49      inference(instantiation,[status(thm)],[c_4842]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_2330,plain,
% 7.44/1.49      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
% 7.44/1.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_6234,plain,
% 7.44/1.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.44/1.49      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) = iProver_top ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_6209,c_2330]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_5657,plain,
% 7.44/1.49      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.44/1.49      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 7.44/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) != iProver_top ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_5281,c_5652]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_5658,plain,
% 7.44/1.49      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.44/1.49      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 7.44/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.44/1.49      inference(demodulation,[status(thm)],[c_5657,c_3]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_5309,plain,
% 7.44/1.49      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.44/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) = iProver_top ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_5281,c_2355]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_5311,plain,
% 7.44/1.49      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.44/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.44/1.49      inference(demodulation,[status(thm)],[c_5309,c_3]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_5948,plain,
% 7.44/1.49      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 7.44/1.49      | u1_struct_0(sK0) = k1_relat_1(sK3) ),
% 7.44/1.49      inference(global_propositional_subsumption,[status(thm)],[c_5658,c_5311]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_5949,plain,
% 7.44/1.49      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.44/1.49      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top ),
% 7.44/1.49      inference(renaming,[status(thm)],[c_5948]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_5952,plain,
% 7.44/1.49      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.44/1.49      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) != iProver_top ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_5281,c_5949]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_6682,plain,
% 7.44/1.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.44/1.49      | u1_struct_0(sK0) = k1_relat_1(sK3) ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_6234,c_5952]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_6798,plain,
% 7.44/1.49      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.44/1.49      | v1_funct_2(sK3,k1_relat_1(sK3),k1_xboole_0) != iProver_top ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_6682,c_5952]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_15897,plain,
% 7.44/1.49      ( u1_struct_0(sK0) = k1_relat_1(k1_xboole_0)
% 7.44/1.49      | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top ),
% 7.44/1.49      inference(demodulation,[status(thm)],[c_15834,c_6798]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_15992,plain,
% 7.44/1.49      ( u1_struct_0(sK0) = k1_xboole_0
% 7.44/1.49      | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 7.44/1.49      inference(light_normalisation,[status(thm)],[c_15897,c_4838]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_18208,plain,
% 7.44/1.49      ( u1_struct_0(sK0) = k1_xboole_0 ),
% 7.44/1.49      inference(global_propositional_subsumption,
% 7.44/1.49                [status(thm)],
% 7.44/1.49                [c_18207,c_114,c_2370,c_4844,c_15992]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_3293,plain,
% 7.44/1.49      ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) = iProver_top ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_2331,c_2348]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_4398,plain,
% 7.44/1.49      ( k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = sK3
% 7.44/1.49      | r1_tarski(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),sK3) != iProver_top ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_3293,c_2352]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_6228,plain,
% 7.44/1.49      ( k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = sK3
% 7.44/1.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.44/1.49      | r1_tarski(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0),sK3) != iProver_top ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_6209,c_4398]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_6239,plain,
% 7.44/1.49      ( k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = sK3
% 7.44/1.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.44/1.49      | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 7.44/1.49      inference(demodulation,[status(thm)],[c_6228,c_3]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_7068,plain,
% 7.44/1.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.44/1.49      | k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = sK3 ),
% 7.44/1.49      inference(global_propositional_subsumption,
% 7.44/1.49                [status(thm)],
% 7.44/1.49                [c_6239,c_2669,c_3280]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_7069,plain,
% 7.44/1.49      ( k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = sK3
% 7.44/1.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
% 7.44/1.49      inference(renaming,[status(thm)],[c_7068]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_15670,plain,
% 7.44/1.49      ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3) = k1_relat_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
% 7.44/1.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_7069,c_14184]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_15677,plain,
% 7.44/1.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.44/1.49      | k1_relat_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) = k1_relat_1(sK3) ),
% 7.44/1.49      inference(light_normalisation,[status(thm)],[c_15670,c_3860]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_5,plain,
% 7.44/1.49      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 7.44/1.49      | k1_xboole_0 = X1
% 7.44/1.49      | k1_xboole_0 = X0 ),
% 7.44/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_115,plain,
% 7.44/1.49      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 7.44/1.49      | k1_xboole_0 = k1_xboole_0 ),
% 7.44/1.49      inference(instantiation,[status(thm)],[c_5]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_116,plain,
% 7.44/1.49      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.44/1.49      inference(instantiation,[status(thm)],[c_4]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_2336,plain,
% 7.44/1.49      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 7.44/1.49      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) = iProver_top
% 7.44/1.49      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 7.44/1.49      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
% 7.44/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 7.44/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
% 7.44/1.49      | v1_funct_1(X0) != iProver_top
% 7.44/1.49      | v2_pre_topc(X1) != iProver_top
% 7.44/1.49      | v2_pre_topc(X2) != iProver_top
% 7.44/1.49      | l1_pre_topc(X1) != iProver_top
% 7.44/1.49      | l1_pre_topc(X2) != iProver_top ),
% 7.44/1.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_4279,plain,
% 7.44/1.49      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 7.44/1.49      | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.44/1.49      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.44/1.49      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.44/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 7.44/1.49      | v1_funct_1(sK3) != iProver_top
% 7.44/1.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.44/1.49      | v2_pre_topc(sK0) != iProver_top
% 7.44/1.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.44/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_2331,c_2336]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_49,plain,
% 7.44/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
% 7.44/1.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_2502,plain,
% 7.44/1.49      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 7.44/1.49      | ~ v2_pre_topc(sK1)
% 7.44/1.49      | ~ l1_pre_topc(sK1) ),
% 7.44/1.49      inference(instantiation,[status(thm)],[c_22]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_2503,plain,
% 7.44/1.49      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 7.44/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.44/1.49      | l1_pre_topc(sK1) != iProver_top ),
% 7.44/1.49      inference(predicate_to_equality,[status(thm)],[c_2502]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_2719,plain,
% 7.44/1.49      ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 7.44/1.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 7.44/1.49      inference(instantiation,[status(thm)],[c_20]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_2720,plain,
% 7.44/1.49      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
% 7.44/1.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
% 7.44/1.49      inference(predicate_to_equality,[status(thm)],[c_2719]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_2914,plain,
% 7.44/1.49      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 7.44/1.49      | ~ l1_pre_topc(sK1) ),
% 7.44/1.49      inference(instantiation,[status(thm)],[c_21]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_2915,plain,
% 7.44/1.49      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
% 7.44/1.49      | l1_pre_topc(sK1) != iProver_top ),
% 7.44/1.49      inference(predicate_to_equality,[status(thm)],[c_2914]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_2644,plain,
% 7.44/1.49      ( ~ v5_pre_topc(sK3,X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 7.44/1.49      | v5_pre_topc(sK3,X0,sK1)
% 7.44/1.49      | ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 7.44/1.49      | ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(sK1))
% 7.44/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 7.44/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
% 7.44/1.49      | ~ v1_funct_1(sK3)
% 7.44/1.49      | ~ v2_pre_topc(X0)
% 7.44/1.49      | ~ v2_pre_topc(sK1)
% 7.44/1.49      | ~ l1_pre_topc(X0)
% 7.44/1.49      | ~ l1_pre_topc(sK1) ),
% 7.44/1.49      inference(instantiation,[status(thm)],[c_25]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_3142,plain,
% 7.44/1.49      ( ~ v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 7.44/1.49      | v5_pre_topc(sK3,sK0,sK1)
% 7.44/1.49      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 7.44/1.49      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
% 7.44/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 7.44/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 7.44/1.49      | ~ v1_funct_1(sK3)
% 7.44/1.49      | ~ v2_pre_topc(sK1)
% 7.44/1.49      | ~ v2_pre_topc(sK0)
% 7.44/1.49      | ~ l1_pre_topc(sK1)
% 7.44/1.49      | ~ l1_pre_topc(sK0) ),
% 7.44/1.49      inference(instantiation,[status(thm)],[c_2644]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_3143,plain,
% 7.44/1.49      ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.44/1.49      | v5_pre_topc(sK3,sK0,sK1) = iProver_top
% 7.44/1.49      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.44/1.49      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.44/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 7.44/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 7.44/1.49      | v1_funct_1(sK3) != iProver_top
% 7.44/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.44/1.49      | v2_pre_topc(sK0) != iProver_top
% 7.44/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.44/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 7.44/1.49      inference(predicate_to_equality,[status(thm)],[c_3142]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_3181,plain,
% 7.44/1.49      ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 7.44/1.49      | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 7.44/1.49      | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 7.44/1.49      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 7.44/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 7.44/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 7.44/1.49      | ~ v1_funct_1(sK3)
% 7.44/1.49      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 7.44/1.49      | ~ v2_pre_topc(sK0)
% 7.44/1.49      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 7.44/1.49      | ~ l1_pre_topc(sK0) ),
% 7.44/1.49      inference(instantiation,[status(thm)],[c_2873]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_3182,plain,
% 7.44/1.49      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.44/1.49      | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 7.44/1.49      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.44/1.49      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.44/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 7.44/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 7.44/1.49      | v1_funct_1(sK3) != iProver_top
% 7.44/1.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.44/1.49      | v2_pre_topc(sK0) != iProver_top
% 7.44/1.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.44/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 7.44/1.49      inference(predicate_to_equality,[status(thm)],[c_3181]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_3112,plain,
% 7.44/1.49      ( ~ v5_pre_topc(sK3,sK0,X0)
% 7.44/1.49      | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 7.44/1.49      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(X0))
% 7.44/1.49      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
% 7.44/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
% 7.44/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
% 7.44/1.49      | ~ v1_funct_1(sK3)
% 7.44/1.49      | ~ v2_pre_topc(X0)
% 7.44/1.49      | ~ v2_pre_topc(sK0)
% 7.44/1.49      | ~ l1_pre_topc(X0)
% 7.44/1.49      | ~ l1_pre_topc(sK0) ),
% 7.44/1.49      inference(instantiation,[status(thm)],[c_26]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_4481,plain,
% 7.44/1.49      ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 7.44/1.49      | ~ v5_pre_topc(sK3,sK0,sK1)
% 7.44/1.49      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 7.44/1.49      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
% 7.44/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 7.44/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 7.44/1.49      | ~ v1_funct_1(sK3)
% 7.44/1.49      | ~ v2_pre_topc(sK1)
% 7.44/1.49      | ~ v2_pre_topc(sK0)
% 7.44/1.49      | ~ l1_pre_topc(sK1)
% 7.44/1.49      | ~ l1_pre_topc(sK0) ),
% 7.44/1.49      inference(instantiation,[status(thm)],[c_3112]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_4482,plain,
% 7.44/1.49      ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 7.44/1.49      | v5_pre_topc(sK3,sK0,sK1) != iProver_top
% 7.44/1.49      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.44/1.49      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.44/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 7.44/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 7.44/1.49      | v1_funct_1(sK3) != iProver_top
% 7.44/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.44/1.49      | v2_pre_topc(sK0) != iProver_top
% 7.44/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.44/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 7.44/1.49      inference(predicate_to_equality,[status(thm)],[c_4481]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_4523,plain,
% 7.44/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 7.44/1.49      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.44/1.49      | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 7.44/1.49      inference(global_propositional_subsumption,
% 7.44/1.49                [status(thm)],
% 7.44/1.49                [c_4279,c_40,c_41,c_42,c_43,c_47,c_48,c_49,c_2357,c_2355,
% 7.44/1.49                 c_2354,c_2358,c_2503,c_2720,c_2915,c_3143,c_3182,c_4482]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_4524,plain,
% 7.44/1.49      ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.44/1.49      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.44/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
% 7.44/1.49      inference(renaming,[status(thm)],[c_4523]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_4527,plain,
% 7.44/1.49      ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.44/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
% 7.44/1.49      inference(global_propositional_subsumption,
% 7.44/1.49                [status(thm)],
% 7.44/1.49                [c_4524,c_40,c_41,c_42,c_43,c_47,c_48,c_49,c_2357,c_2355,
% 7.44/1.49                 c_2354,c_2503,c_2720,c_2915,c_3182,c_4482]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_4531,plain,
% 7.44/1.49      ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.44/1.49      | r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) != iProver_top ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_2349,c_4527]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_6229,plain,
% 7.44/1.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.44/1.49      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.44/1.49      | r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)) != iProver_top ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_6209,c_4531]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_6238,plain,
% 7.44/1.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.44/1.49      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.44/1.49      | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
% 7.44/1.49      inference(demodulation,[status(thm)],[c_6229,c_3]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_6232,plain,
% 7.44/1.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.44/1.49      | r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)) = iProver_top ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_6209,c_3293]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_6236,plain,
% 7.44/1.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.44/1.49      | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 7.44/1.49      inference(demodulation,[status(thm)],[c_6232,c_3]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_6450,plain,
% 7.44/1.49      ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.44/1.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
% 7.44/1.49      inference(global_propositional_subsumption,[status(thm)],[c_6238,c_6236]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_6451,plain,
% 7.44/1.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.44/1.49      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
% 7.44/1.49      inference(renaming,[status(thm)],[c_6450]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_6454,plain,
% 7.44/1.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.44/1.49      | v1_funct_2(sK3,u1_struct_0(sK0),k1_xboole_0) != iProver_top ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_6209,c_6451]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_1559,plain,
% 7.44/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.44/1.49      | v1_funct_2(X3,X4,X5)
% 7.44/1.49      | X3 != X0
% 7.44/1.49      | X4 != X1
% 7.44/1.49      | X5 != X2 ),
% 7.44/1.49      theory(equality) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_10246,plain,
% 7.44/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.44/1.49      | v1_funct_2(sK3,u1_struct_0(sK0),X3)
% 7.44/1.49      | X3 != X2
% 7.44/1.49      | u1_struct_0(sK0) != X1
% 7.44/1.49      | sK3 != X0 ),
% 7.44/1.49      inference(instantiation,[status(thm)],[c_1559]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_10247,plain,
% 7.44/1.49      ( X0 != X1
% 7.44/1.49      | u1_struct_0(sK0) != X2
% 7.44/1.49      | sK3 != X3
% 7.44/1.49      | v1_funct_2(X3,X2,X1) != iProver_top
% 7.44/1.49      | v1_funct_2(sK3,u1_struct_0(sK0),X0) = iProver_top ),
% 7.44/1.49      inference(predicate_to_equality,[status(thm)],[c_10246]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_10249,plain,
% 7.44/1.49      ( u1_struct_0(sK0) != k1_xboole_0
% 7.44/1.49      | sK3 != k1_xboole_0
% 7.44/1.49      | k1_xboole_0 != k1_xboole_0
% 7.44/1.49      | v1_funct_2(sK3,u1_struct_0(sK0),k1_xboole_0) = iProver_top
% 7.44/1.49      | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 7.44/1.49      inference(instantiation,[status(thm)],[c_10247]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_19578,plain,
% 7.44/1.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
% 7.44/1.49      inference(global_propositional_subsumption,
% 7.44/1.49                [status(thm)],
% 7.44/1.49                [c_15677,c_114,c_115,c_116,c_2370,c_4844,c_6454,c_10249,
% 7.44/1.49                 c_11010,c_15416,c_15417,c_15992]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_19580,plain,
% 7.44/1.49      ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) = k1_xboole_0 ),
% 7.44/1.49      inference(light_normalisation,
% 7.44/1.49                [status(thm)],
% 7.44/1.49                [c_19578,c_4838,c_15834,c_18208]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_20049,plain,
% 7.44/1.49      ( v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1)) != iProver_top ),
% 7.44/1.49      inference(light_normalisation,[status(thm)],[c_17690,c_18208,c_19580]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_20051,plain,
% 7.44/1.49      ( $false ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_17410,c_20049]) ).
% 7.44/1.49  
% 7.44/1.49  
% 7.44/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.44/1.49  
% 7.44/1.49  ------                               Statistics
% 7.44/1.49  
% 7.44/1.49  ------ General
% 7.44/1.49  
% 7.44/1.49  abstr_ref_over_cycles:                  0
% 7.44/1.49  abstr_ref_under_cycles:                 0
% 7.44/1.49  gc_basic_clause_elim:                   0
% 7.44/1.49  forced_gc_time:                         0
% 7.44/1.49  parsing_time:                           0.009
% 7.44/1.49  unif_index_cands_time:                  0.
% 7.44/1.49  unif_index_add_time:                    0.
% 7.44/1.49  orderings_time:                         0.
% 7.44/1.49  out_proof_time:                         0.021
% 7.44/1.49  total_time:                             0.6
% 7.44/1.49  num_of_symbols:                         52
% 7.44/1.49  num_of_terms:                           15722
% 7.44/1.49  
% 7.44/1.49  ------ Preprocessing
% 7.44/1.49  
% 7.44/1.49  num_of_splits:                          0
% 7.44/1.49  num_of_split_atoms:                     0
% 7.44/1.49  num_of_reused_defs:                     0
% 7.44/1.49  num_eq_ax_congr_red:                    15
% 7.44/1.49  num_of_sem_filtered_clauses:            1
% 7.44/1.49  num_of_subtypes:                        0
% 7.44/1.49  monotx_restored_types:                  0
% 7.44/1.49  sat_num_of_epr_types:                   0
% 7.44/1.49  sat_num_of_non_cyclic_types:            0
% 7.44/1.49  sat_guarded_non_collapsed_types:        0
% 7.44/1.49  num_pure_diseq_elim:                    0
% 7.44/1.49  simp_replaced_by:                       0
% 7.44/1.49  res_preprocessed:                       178
% 7.44/1.49  prep_upred:                             0
% 7.44/1.49  prep_unflattend:                        16
% 7.44/1.49  smt_new_axioms:                         0
% 7.44/1.49  pred_elim_cands:                        7
% 7.44/1.49  pred_elim:                              2
% 7.44/1.49  pred_elim_cl:                           3
% 7.44/1.49  pred_elim_cycles:                       5
% 7.44/1.49  merged_defs:                            16
% 7.44/1.49  merged_defs_ncl:                        0
% 7.44/1.49  bin_hyper_res:                          16
% 7.44/1.49  prep_cycles:                            4
% 7.44/1.49  pred_elim_time:                         0.028
% 7.44/1.49  splitting_time:                         0.
% 7.44/1.49  sem_filter_time:                        0.
% 7.44/1.49  monotx_time:                            0.
% 7.44/1.49  subtype_inf_time:                       0.
% 7.44/1.49  
% 7.44/1.49  ------ Problem properties
% 7.44/1.49  
% 7.44/1.49  clauses:                                36
% 7.44/1.49  conjectures:                            13
% 7.44/1.49  epr:                                    9
% 7.44/1.49  horn:                                   30
% 7.44/1.49  ground:                                 13
% 7.44/1.49  unary:                                  15
% 7.44/1.49  binary:                                 8
% 7.44/1.49  lits:                                   105
% 7.44/1.49  lits_eq:                                17
% 7.44/1.49  fd_pure:                                0
% 7.44/1.49  fd_pseudo:                              0
% 7.44/1.49  fd_cond:                                4
% 7.44/1.49  fd_pseudo_cond:                         1
% 7.44/1.49  ac_symbols:                             0
% 7.44/1.49  
% 7.44/1.49  ------ Propositional Solver
% 7.44/1.49  
% 7.44/1.49  prop_solver_calls:                      33
% 7.44/1.49  prop_fast_solver_calls:                 2425
% 7.44/1.49  smt_solver_calls:                       0
% 7.44/1.49  smt_fast_solver_calls:                  0
% 7.44/1.49  prop_num_of_clauses:                    8952
% 7.44/1.49  prop_preprocess_simplified:             17581
% 7.44/1.49  prop_fo_subsumed:                       144
% 7.44/1.49  prop_solver_time:                       0.
% 7.44/1.49  smt_solver_time:                        0.
% 7.44/1.49  smt_fast_solver_time:                   0.
% 7.44/1.49  prop_fast_solver_time:                  0.
% 7.44/1.49  prop_unsat_core_time:                   0.
% 7.44/1.49  
% 7.44/1.49  ------ QBF
% 7.44/1.49  
% 7.44/1.49  qbf_q_res:                              0
% 7.44/1.49  qbf_num_tautologies:                    0
% 7.44/1.49  qbf_prep_cycles:                        0
% 7.44/1.49  
% 7.44/1.49  ------ BMC1
% 7.44/1.49  
% 7.44/1.49  bmc1_current_bound:                     -1
% 7.44/1.49  bmc1_last_solved_bound:                 -1
% 7.44/1.49  bmc1_unsat_core_size:                   -1
% 7.44/1.49  bmc1_unsat_core_parents_size:           -1
% 7.44/1.49  bmc1_merge_next_fun:                    0
% 7.44/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.44/1.49  
% 7.44/1.49  ------ Instantiation
% 7.44/1.49  
% 7.44/1.49  inst_num_of_clauses:                    2376
% 7.44/1.49  inst_num_in_passive:                    1140
% 7.44/1.49  inst_num_in_active:                     807
% 7.44/1.49  inst_num_in_unprocessed:                429
% 7.44/1.49  inst_num_of_loops:                      1060
% 7.44/1.49  inst_num_of_learning_restarts:          0
% 7.44/1.49  inst_num_moves_active_passive:          247
% 7.44/1.49  inst_lit_activity:                      0
% 7.44/1.49  inst_lit_activity_moves:                0
% 7.44/1.49  inst_num_tautologies:                   0
% 7.44/1.49  inst_num_prop_implied:                  0
% 7.44/1.49  inst_num_existing_simplified:           0
% 7.44/1.49  inst_num_eq_res_simplified:             0
% 7.44/1.49  inst_num_child_elim:                    0
% 7.44/1.49  inst_num_of_dismatching_blockings:      1029
% 7.44/1.49  inst_num_of_non_proper_insts:           2467
% 7.44/1.49  inst_num_of_duplicates:                 0
% 7.44/1.49  inst_inst_num_from_inst_to_res:         0
% 7.44/1.49  inst_dismatching_checking_time:         0.
% 7.44/1.49  
% 7.44/1.49  ------ Resolution
% 7.44/1.49  
% 7.44/1.49  res_num_of_clauses:                     0
% 7.44/1.49  res_num_in_passive:                     0
% 7.44/1.49  res_num_in_active:                      0
% 7.44/1.49  res_num_of_loops:                       182
% 7.44/1.49  res_forward_subset_subsumed:            216
% 7.44/1.49  res_backward_subset_subsumed:           6
% 7.44/1.49  res_forward_subsumed:                   0
% 7.44/1.49  res_backward_subsumed:                  0
% 7.44/1.49  res_forward_subsumption_resolution:     0
% 7.44/1.49  res_backward_subsumption_resolution:    0
% 7.44/1.49  res_clause_to_clause_subsumption:       1706
% 7.44/1.49  res_orphan_elimination:                 0
% 7.44/1.49  res_tautology_del:                      111
% 7.44/1.49  res_num_eq_res_simplified:              0
% 7.44/1.49  res_num_sel_changes:                    0
% 7.44/1.49  res_moves_from_active_to_pass:          0
% 7.44/1.49  
% 7.44/1.49  ------ Superposition
% 7.44/1.49  
% 7.44/1.49  sup_time_total:                         0.
% 7.44/1.49  sup_time_generating:                    0.
% 7.44/1.49  sup_time_sim_full:                      0.
% 7.44/1.49  sup_time_sim_immed:                     0.
% 7.44/1.49  
% 7.44/1.49  sup_num_of_clauses:                     429
% 7.44/1.49  sup_num_in_active:                      71
% 7.44/1.49  sup_num_in_passive:                     358
% 7.44/1.49  sup_num_of_loops:                       211
% 7.44/1.49  sup_fw_superposition:                   469
% 7.44/1.49  sup_bw_superposition:                   555
% 7.44/1.49  sup_immediate_simplified:               535
% 7.44/1.49  sup_given_eliminated:                   0
% 7.44/1.49  comparisons_done:                       0
% 7.44/1.49  comparisons_avoided:                    37
% 7.44/1.49  
% 7.44/1.49  ------ Simplifications
% 7.44/1.49  
% 7.44/1.49  
% 7.44/1.49  sim_fw_subset_subsumed:                 303
% 7.44/1.49  sim_bw_subset_subsumed:                 109
% 7.44/1.49  sim_fw_subsumed:                        49
% 7.44/1.49  sim_bw_subsumed:                        10
% 7.44/1.49  sim_fw_subsumption_res:                 0
% 7.44/1.49  sim_bw_subsumption_res:                 0
% 7.44/1.49  sim_tautology_del:                      5
% 7.44/1.49  sim_eq_tautology_del:                   40
% 7.44/1.49  sim_eq_res_simp:                        2
% 7.44/1.49  sim_fw_demodulated:                     105
% 7.44/1.49  sim_bw_demodulated:                     126
% 7.44/1.49  sim_light_normalised:                   173
% 7.44/1.49  sim_joinable_taut:                      0
% 7.44/1.49  sim_joinable_simp:                      0
% 7.44/1.49  sim_ac_normalised:                      0
% 7.44/1.49  sim_smt_subsumption:                    0
% 7.44/1.49  
%------------------------------------------------------------------------------
