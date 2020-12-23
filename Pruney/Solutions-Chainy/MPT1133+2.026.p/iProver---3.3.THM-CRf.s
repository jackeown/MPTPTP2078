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
% DateTime   : Thu Dec  3 12:11:53 EST 2020

% Result     : Theorem 7.45s
% Output     : CNFRefutation 7.45s
% Verified   : 
% Statistics : Number of formulae       :  310 (13657 expanded)
%              Number of clauses        :  193 (3386 expanded)
%              Number of leaves         :   29 (3919 expanded)
%              Depth                    :   32
%              Number of atoms          : 1340 (141964 expanded)
%              Number of equality atoms :  483 (15024 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f98,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f7,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f97,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f20,axiom,(
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

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f73,plain,(
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
    inference(nnf_transformation,[],[f48])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f148,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f118])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f68])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f69])).

fof(f144,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f91])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f62,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f61])).

fof(f63,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f62,f63])).

fof(f85,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f99,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f103,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f88,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f27,conjecture,(
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

fof(f28,negated_conjecture,(
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
    inference(negated_conjecture,[],[f27])).

fof(f59,plain,(
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
    inference(ennf_transformation,[],[f28])).

fof(f60,plain,(
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
    inference(flattening,[],[f59])).

fof(f77,plain,(
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
    inference(nnf_transformation,[],[f60])).

fof(f78,plain,(
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
    inference(flattening,[],[f77])).

fof(f82,plain,(
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
     => ( ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
          | ~ v5_pre_topc(X2,X0,X1) )
        & ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
          | v5_pre_topc(X2,X0,X1) )
        & sK5 = X2
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        & v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f81,plain,(
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
              | ~ v5_pre_topc(sK4,X0,X1) )
            & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | v5_pre_topc(sK4,X0,X1) )
            & sK4 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
            & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
            & v1_funct_1(X3) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,(
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
                ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
                  | ~ v5_pre_topc(X2,X0,sK3) )
                & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
                  | v5_pre_topc(X2,X0,sK3) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
                & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK3)
        & v2_pre_topc(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,
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
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,sK2,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,sK2,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f83,plain,
    ( ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
      | ~ v5_pre_topc(sK4,sK2,sK3) )
    & ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
      | v5_pre_topc(sK4,sK2,sK3) )
    & sK4 = sK5
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    & v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    & v1_funct_1(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f78,f82,f81,f80,f79])).

fof(f136,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f83])).

fof(f140,plain,(
    sK4 = sK5 ),
    inference(cnf_transformation,[],[f83])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f43])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f49])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f121,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f137,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f83])).

fof(f135,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f83])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f139,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) ),
    inference(cnf_transformation,[],[f83])).

fof(f138,plain,(
    v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) ),
    inference(cnf_transformation,[],[f83])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_funct_2(X2,X0,X1)
              & ~ v1_xboole_0(X2)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_funct_2(X2,X0,X1)
            & ~ v1_xboole_0(X2)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_funct_2(X2,X0,X1)
            & ~ v1_xboole_0(X2)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f95,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f25,axiom,(
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

fof(f55,plain,(
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
    inference(ennf_transformation,[],[f25])).

fof(f56,plain,(
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
    inference(flattening,[],[f55])).

fof(f75,plain,(
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
    inference(nnf_transformation,[],[f56])).

fof(f126,plain,(
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
    inference(cnf_transformation,[],[f75])).

fof(f152,plain,(
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
    inference(equality_resolution,[],[f126])).

fof(f130,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f83])).

fof(f131,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f83])).

fof(f132,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f83])).

fof(f133,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f83])).

fof(f141,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f83])).

fof(f142,plain,
    ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f83])).

fof(f24,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f24])).

fof(f53,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f54,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f53])).

fof(f125,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f22])).

fof(f51,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f123,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f124,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f127,plain,(
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
    inference(cnf_transformation,[],[f75])).

fof(f151,plain,(
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
    inference(equality_resolution,[],[f127])).

fof(f26,axiom,(
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

fof(f57,plain,(
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
    inference(ennf_transformation,[],[f26])).

fof(f58,plain,(
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
    inference(flattening,[],[f57])).

fof(f76,plain,(
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
    inference(nnf_transformation,[],[f58])).

fof(f129,plain,(
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
    inference(cnf_transformation,[],[f76])).

fof(f153,plain,(
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
    inference(equality_resolution,[],[f129])).

fof(f128,plain,(
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
    inference(cnf_transformation,[],[f76])).

fof(f154,plain,(
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
    inference(equality_resolution,[],[f128])).

fof(f96,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_14,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_3139,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_13,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_3149,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3139,c_13])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_3135,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_6099,plain,
    ( k1_relset_1(X0,X1,k2_zfmisc_1(X0,X1)) = k1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(superposition,[status(thm)],[c_3149,c_3135])).

cnf(c_33,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f148])).

cnf(c_3131,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_7,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f144])).

cnf(c_3156,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3131,c_7])).

cnf(c_11212,plain,
    ( k1_relat_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_xboole_0
    | v1_funct_2(k2_zfmisc_1(k1_xboole_0,X0),k1_xboole_0,X0) = iProver_top
    | m1_subset_1(k2_zfmisc_1(k1_xboole_0,X0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6099,c_3156])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_3147,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_15,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_3138,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_21,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_23,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_20,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_764,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_23,c_20])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_768,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_764,c_22])).

cnf(c_769,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_768])).

cnf(c_808,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X4)
    | X1 != X3
    | k1_relat_1(X0) != X4 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_769])).

cnf(c_809,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X1,k1_relat_1(X0)) ),
    inference(unflattening,[status(thm)],[c_808])).

cnf(c_3104,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_809])).

cnf(c_4137,plain,
    ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3138,c_3104])).

cnf(c_4386,plain,
    ( v1_xboole_0(k1_relat_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3147,c_4137])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_797,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_21])).

cnf(c_798,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_797])).

cnf(c_3105,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_798])).

cnf(c_4186,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3147,c_3105])).

cnf(c_5,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_3143,plain,
    ( X0 = X1
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_5316,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4186,c_3143])).

cnf(c_10497,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4386,c_5316])).

cnf(c_11213,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11212,c_7,c_10497])).

cnf(c_11214,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_11213])).

cnf(c_151,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_153,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_151])).

cnf(c_5317,plain,
    ( k1_relat_1(k1_xboole_0) = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4386,c_3143])).

cnf(c_5321,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5317])).

cnf(c_6096,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3138,c_3135])).

cnf(c_10097,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6096,c_3156])).

cnf(c_17857,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11214,c_153,c_4186,c_5321,c_10097])).

cnf(c_52,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_3115,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_48,negated_conjecture,
    ( sK4 = sK5 ),
    inference(cnf_transformation,[],[f140])).

cnf(c_3151,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3115,c_48])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_38,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f121])).

cnf(c_698,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_26,c_38])).

cnf(c_702,plain,
    ( ~ v1_funct_1(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_698,c_23,c_22])).

cnf(c_703,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_702])).

cnf(c_3107,plain,
    ( k1_relat_1(X0) = X1
    | v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_703])).

cnf(c_5998,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3151,c_3107])).

cnf(c_51,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f137])).

cnf(c_66,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_53,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_3114,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_53])).

cnf(c_3150,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3114,c_48])).

cnf(c_6146,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5998,c_66,c_3150])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_3136,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_7950,plain,
    ( v1_xboole_0(u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3151,c_3136])).

cnf(c_8054,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_6146,c_7950])).

cnf(c_10496,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8054,c_5316])).

cnf(c_49,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) ),
    inference(cnf_transformation,[],[f139])).

cnf(c_3118,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_11765,plain,
    ( sK5 = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK5),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_10496,c_3118])).

cnf(c_12640,plain,
    ( u1_struct_0(g1_pre_topc(k1_relat_1(sK5),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | sK5 = k1_xboole_0
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(k1_relat_1(sK5),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_11765,c_3107])).

cnf(c_7947,plain,
    ( v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3118,c_3136])).

cnf(c_50,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) ),
    inference(cnf_transformation,[],[f138])).

cnf(c_3117,plain,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_11766,plain,
    ( sK5 = k1_xboole_0
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(k1_relat_1(sK5),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_10496,c_3117])).

cnf(c_11767,plain,
    ( sK5 = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_10496,c_3151])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_3134,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_12419,plain,
    ( sK5 = k1_xboole_0
    | v1_funct_2(sK5,k1_relat_1(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(k1_relat_1(sK5)) = iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_11767,c_3134])).

cnf(c_3569,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(sK5)
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3570,plain,
    ( sK5 = X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3569])).

cnf(c_3572,plain,
    ( sK5 = k1_xboole_0
    | v1_xboole_0(sK5) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3570])).

cnf(c_15558,plain,
    ( sK5 = k1_xboole_0
    | v1_xboole_0(sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12419,c_3572,c_4186])).

cnf(c_15816,plain,
    ( sK5 = k1_xboole_0
    | u1_struct_0(g1_pre_topc(k1_relat_1(sK5),u1_pre_topc(sK2))) = k1_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12640,c_66,c_3572,c_4186,c_7947,c_11766])).

cnf(c_15817,plain,
    ( u1_struct_0(g1_pre_topc(k1_relat_1(sK5),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | sK5 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_15816])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_3141,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_6300,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3118,c_3141])).

cnf(c_11753,plain,
    ( sK5 = k1_xboole_0
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK5),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_10496,c_6300])).

cnf(c_15330,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK5),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
    | sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11753,c_3572,c_4186])).

cnf(c_15331,plain,
    ( sK5 = k1_xboole_0
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK5),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top ),
    inference(renaming,[status(thm)],[c_15330])).

cnf(c_15832,plain,
    ( sK5 = k1_xboole_0
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_15817,c_15331])).

cnf(c_15839,plain,
    ( sK5 = k1_xboole_0
    | v1_funct_2(sK5,k1_relat_1(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_15817,c_11766])).

cnf(c_15838,plain,
    ( sK5 = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_15817,c_11765])).

cnf(c_43,plain,
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
    inference(cnf_transformation,[],[f152])).

cnf(c_3123,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_8386,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3118,c_3123])).

cnf(c_58,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_59,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_58])).

cnf(c_57,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_60,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57])).

cnf(c_56,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_61,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_56])).

cnf(c_55,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_62,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_55])).

cnf(c_67,plain,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_68,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_47,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(cnf_transformation,[],[f141])).

cnf(c_3119,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_3153,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v5_pre_topc(sK5,sK2,sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3119,c_48])).

cnf(c_46,negated_conjecture,
    ( ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(cnf_transformation,[],[f142])).

cnf(c_3120,plain,
    ( v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_3154,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v5_pre_topc(sK5,sK2,sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3120,c_48])).

cnf(c_41,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_3331,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_41])).

cnf(c_3332,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3331])).

cnf(c_39,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_3759,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(c_3760,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3759])).

cnf(c_40,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_4218,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_40])).

cnf(c_4219,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4218])).

cnf(c_42,plain,
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
    inference(cnf_transformation,[],[f151])).

cnf(c_3469,plain,
    ( v5_pre_topc(sK5,X0,X1)
    | ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_42])).

cnf(c_4056,plain,
    ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0)
    | v5_pre_topc(sK5,sK2,X0)
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(X0))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(X0))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_3469])).

cnf(c_5138,plain,
    ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_4056])).

cnf(c_5139,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5138])).

cnf(c_44,plain,
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
    inference(cnf_transformation,[],[f153])).

cnf(c_3470,plain,
    ( v5_pre_topc(sK5,X0,X1)
    | ~ v5_pre_topc(sK5,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_44])).

cnf(c_4081,plain,
    ( v5_pre_topc(sK5,sK2,X0)
    | ~ v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(X0))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_3470])).

cnf(c_5185,plain,
    ( ~ v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | v5_pre_topc(sK5,sK2,sK3)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_4081])).

cnf(c_5186,plain,
    ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v5_pre_topc(sK5,sK2,sK3) = iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5185])).

cnf(c_45,plain,
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
    inference(cnf_transformation,[],[f154])).

cnf(c_5340,plain,
    ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v5_pre_topc(sK5,sK2,sK3)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_45])).

cnf(c_5341,plain,
    ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v5_pre_topc(sK5,sK2,sK3) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5340])).

cnf(c_8579,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8386,c_59,c_60,c_61,c_62,c_66,c_67,c_68,c_3151,c_3150,c_3153,c_3154,c_3332,c_3760,c_4219,c_5139,c_5186,c_5341])).

cnf(c_8580,plain,
    ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top ),
    inference(renaming,[status(thm)],[c_8579])).

cnf(c_8583,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8580,c_59,c_60,c_61,c_62,c_66,c_67,c_68,c_3151,c_3150,c_3153,c_3332,c_3760,c_4219,c_5139,c_5341])).

cnf(c_11741,plain,
    ( sK5 = k1_xboole_0
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_10496,c_8583])).

cnf(c_16244,plain,
    ( sK5 = k1_xboole_0
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_15838,c_11741])).

cnf(c_18356,plain,
    ( sK5 = k1_xboole_0
    | v1_funct_2(sK5,k1_relat_1(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_10496,c_16244])).

cnf(c_18512,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_15832,c_15839,c_18356])).

cnf(c_18556,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_18512,c_8583])).

cnf(c_5996,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3118,c_3107])).

cnf(c_6173,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5996,c_66,c_67])).

cnf(c_6150,plain,
    ( u1_struct_0(sK3) = X0
    | u1_struct_0(sK2) = k1_relat_1(sK5)
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6146,c_3143])).

cnf(c_6185,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = u1_struct_0(sK3)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | u1_struct_0(sK2) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_6173,c_6150])).

cnf(c_6221,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | u1_struct_0(sK2) = k1_relat_1(sK5)
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6185,c_3118])).

cnf(c_3122,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_7880,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) = iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3118,c_3122])).

cnf(c_3318,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_41])).

cnf(c_3319,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3318])).

cnf(c_3749,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(c_3750,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3749])).

cnf(c_4199,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_40])).

cnf(c_4200,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4199])).

cnf(c_5343,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3)
    | ~ v5_pre_topc(sK5,sK2,sK3)
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_43])).

cnf(c_5344,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) = iProver_top
    | v5_pre_topc(sK5,sK2,sK3) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5343])).

cnf(c_3121,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_6660,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3118,c_3121])).

cnf(c_5129,plain,
    ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3)
    | v5_pre_topc(sK5,sK2,sK3)
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_4056])).

cnf(c_5130,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) != iProver_top
    | v5_pre_topc(sK5,sK2,sK3) = iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5129])).

cnf(c_6803,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6660,c_59,c_60,c_61,c_62,c_66,c_67,c_3151,c_3150,c_3154,c_3319,c_3750,c_4200,c_5130])).

cnf(c_6804,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6803])).

cnf(c_8091,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7880,c_59,c_60,c_61,c_62,c_66,c_67,c_3151,c_3150,c_3153,c_3319,c_3750,c_4200,c_5344,c_6804])).

cnf(c_8092,plain,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_8091])).

cnf(c_8096,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | u1_struct_0(sK2) = k1_relat_1(sK5)
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6221,c_8092])).

cnf(c_6222,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | u1_struct_0(sK2) = k1_relat_1(sK5)
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6185,c_3117])).

cnf(c_9826,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8096,c_6222])).

cnf(c_9827,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | u1_struct_0(sK2) = k1_relat_1(sK5) ),
    inference(renaming,[status(thm)],[c_9826])).

cnf(c_9,plain,
    ( m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_3142,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_8095,plain,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3142,c_8092])).

cnf(c_9839,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),u1_struct_0(sK3)))) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_9827,c_8095])).

cnf(c_11447,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | u1_struct_0(sK2) = k1_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9839,c_8054])).

cnf(c_11448,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),u1_struct_0(sK3)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_11447])).

cnf(c_11451,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | v1_funct_2(sK5,k1_relat_1(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),u1_struct_0(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9827,c_11448])).

cnf(c_18524,plain,
    ( u1_struct_0(sK2) = k1_relat_1(k1_xboole_0)
    | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(sK3)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_18512,c_11451])).

cnf(c_18626,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK3)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_18524,c_10497])).

cnf(c_18627,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_18626,c_7])).

cnf(c_9842,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),u1_struct_0(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9827,c_8092])).

cnf(c_10225,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | v1_funct_2(sK5,k1_relat_1(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),u1_struct_0(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9827,c_9842])).

cnf(c_18527,plain,
    ( u1_struct_0(sK2) = k1_relat_1(k1_xboole_0)
    | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(sK3)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_18512,c_10225])).

cnf(c_18621,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK3)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_18527,c_10497])).

cnf(c_18622,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_18621,c_7])).

cnf(c_20098,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK3)) != iProver_top
    | u1_struct_0(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_18627,c_153,c_18622])).

cnf(c_20099,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_20098])).

cnf(c_20102,plain,
    ( u1_struct_0(sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_17857,c_20099])).

cnf(c_20164,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_18556,c_20102])).

cnf(c_20165,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_20164,c_7])).

cnf(c_20167,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20165,c_153])).

cnf(c_20171,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_17857,c_20167])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:41:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.45/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.45/1.49  
% 7.45/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.45/1.49  
% 7.45/1.49  ------  iProver source info
% 7.45/1.49  
% 7.45/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.45/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.45/1.49  git: non_committed_changes: false
% 7.45/1.49  git: last_make_outside_of_git: false
% 7.45/1.49  
% 7.45/1.49  ------ 
% 7.45/1.49  
% 7.45/1.49  ------ Input Options
% 7.45/1.49  
% 7.45/1.49  --out_options                           all
% 7.45/1.49  --tptp_safe_out                         true
% 7.45/1.49  --problem_path                          ""
% 7.45/1.49  --include_path                          ""
% 7.45/1.49  --clausifier                            res/vclausify_rel
% 7.45/1.49  --clausifier_options                    ""
% 7.45/1.49  --stdin                                 false
% 7.45/1.49  --stats_out                             all
% 7.45/1.49  
% 7.45/1.49  ------ General Options
% 7.45/1.49  
% 7.45/1.49  --fof                                   false
% 7.45/1.49  --time_out_real                         305.
% 7.45/1.49  --time_out_virtual                      -1.
% 7.45/1.49  --symbol_type_check                     false
% 7.45/1.49  --clausify_out                          false
% 7.45/1.49  --sig_cnt_out                           false
% 7.45/1.49  --trig_cnt_out                          false
% 7.45/1.49  --trig_cnt_out_tolerance                1.
% 7.45/1.49  --trig_cnt_out_sk_spl                   false
% 7.45/1.49  --abstr_cl_out                          false
% 7.45/1.49  
% 7.45/1.49  ------ Global Options
% 7.45/1.49  
% 7.45/1.49  --schedule                              default
% 7.45/1.49  --add_important_lit                     false
% 7.45/1.49  --prop_solver_per_cl                    1000
% 7.45/1.49  --min_unsat_core                        false
% 7.45/1.49  --soft_assumptions                      false
% 7.45/1.49  --soft_lemma_size                       3
% 7.45/1.49  --prop_impl_unit_size                   0
% 7.45/1.49  --prop_impl_unit                        []
% 7.45/1.49  --share_sel_clauses                     true
% 7.45/1.49  --reset_solvers                         false
% 7.45/1.49  --bc_imp_inh                            [conj_cone]
% 7.45/1.49  --conj_cone_tolerance                   3.
% 7.45/1.49  --extra_neg_conj                        none
% 7.45/1.49  --large_theory_mode                     true
% 7.45/1.49  --prolific_symb_bound                   200
% 7.45/1.49  --lt_threshold                          2000
% 7.45/1.49  --clause_weak_htbl                      true
% 7.45/1.49  --gc_record_bc_elim                     false
% 7.45/1.49  
% 7.45/1.49  ------ Preprocessing Options
% 7.45/1.49  
% 7.45/1.49  --preprocessing_flag                    true
% 7.45/1.49  --time_out_prep_mult                    0.1
% 7.45/1.49  --splitting_mode                        input
% 7.45/1.49  --splitting_grd                         true
% 7.45/1.49  --splitting_cvd                         false
% 7.45/1.49  --splitting_cvd_svl                     false
% 7.45/1.49  --splitting_nvd                         32
% 7.45/1.49  --sub_typing                            true
% 7.45/1.49  --prep_gs_sim                           true
% 7.45/1.49  --prep_unflatten                        true
% 7.45/1.49  --prep_res_sim                          true
% 7.45/1.49  --prep_upred                            true
% 7.45/1.49  --prep_sem_filter                       exhaustive
% 7.45/1.49  --prep_sem_filter_out                   false
% 7.45/1.49  --pred_elim                             true
% 7.45/1.49  --res_sim_input                         true
% 7.45/1.49  --eq_ax_congr_red                       true
% 7.45/1.49  --pure_diseq_elim                       true
% 7.45/1.49  --brand_transform                       false
% 7.45/1.49  --non_eq_to_eq                          false
% 7.45/1.49  --prep_def_merge                        true
% 7.45/1.49  --prep_def_merge_prop_impl              false
% 7.45/1.49  --prep_def_merge_mbd                    true
% 7.45/1.49  --prep_def_merge_tr_red                 false
% 7.45/1.49  --prep_def_merge_tr_cl                  false
% 7.45/1.49  --smt_preprocessing                     true
% 7.45/1.49  --smt_ac_axioms                         fast
% 7.45/1.49  --preprocessed_out                      false
% 7.45/1.49  --preprocessed_stats                    false
% 7.45/1.49  
% 7.45/1.49  ------ Abstraction refinement Options
% 7.45/1.49  
% 7.45/1.49  --abstr_ref                             []
% 7.45/1.49  --abstr_ref_prep                        false
% 7.45/1.49  --abstr_ref_until_sat                   false
% 7.45/1.49  --abstr_ref_sig_restrict                funpre
% 7.45/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.45/1.49  --abstr_ref_under                       []
% 7.45/1.49  
% 7.45/1.49  ------ SAT Options
% 7.45/1.49  
% 7.45/1.49  --sat_mode                              false
% 7.45/1.49  --sat_fm_restart_options                ""
% 7.45/1.49  --sat_gr_def                            false
% 7.45/1.49  --sat_epr_types                         true
% 7.45/1.49  --sat_non_cyclic_types                  false
% 7.45/1.49  --sat_finite_models                     false
% 7.45/1.49  --sat_fm_lemmas                         false
% 7.45/1.49  --sat_fm_prep                           false
% 7.45/1.49  --sat_fm_uc_incr                        true
% 7.45/1.49  --sat_out_model                         small
% 7.45/1.49  --sat_out_clauses                       false
% 7.45/1.49  
% 7.45/1.49  ------ QBF Options
% 7.45/1.49  
% 7.45/1.49  --qbf_mode                              false
% 7.45/1.49  --qbf_elim_univ                         false
% 7.45/1.49  --qbf_dom_inst                          none
% 7.45/1.49  --qbf_dom_pre_inst                      false
% 7.45/1.49  --qbf_sk_in                             false
% 7.45/1.49  --qbf_pred_elim                         true
% 7.45/1.49  --qbf_split                             512
% 7.45/1.49  
% 7.45/1.49  ------ BMC1 Options
% 7.45/1.49  
% 7.45/1.49  --bmc1_incremental                      false
% 7.45/1.49  --bmc1_axioms                           reachable_all
% 7.45/1.49  --bmc1_min_bound                        0
% 7.45/1.49  --bmc1_max_bound                        -1
% 7.45/1.49  --bmc1_max_bound_default                -1
% 7.45/1.49  --bmc1_symbol_reachability              true
% 7.45/1.49  --bmc1_property_lemmas                  false
% 7.45/1.49  --bmc1_k_induction                      false
% 7.45/1.49  --bmc1_non_equiv_states                 false
% 7.45/1.49  --bmc1_deadlock                         false
% 7.45/1.49  --bmc1_ucm                              false
% 7.45/1.49  --bmc1_add_unsat_core                   none
% 7.45/1.49  --bmc1_unsat_core_children              false
% 7.45/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.45/1.49  --bmc1_out_stat                         full
% 7.45/1.49  --bmc1_ground_init                      false
% 7.45/1.49  --bmc1_pre_inst_next_state              false
% 7.45/1.49  --bmc1_pre_inst_state                   false
% 7.45/1.49  --bmc1_pre_inst_reach_state             false
% 7.45/1.49  --bmc1_out_unsat_core                   false
% 7.45/1.49  --bmc1_aig_witness_out                  false
% 7.45/1.49  --bmc1_verbose                          false
% 7.45/1.49  --bmc1_dump_clauses_tptp                false
% 7.45/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.45/1.49  --bmc1_dump_file                        -
% 7.45/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.45/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.45/1.49  --bmc1_ucm_extend_mode                  1
% 7.45/1.49  --bmc1_ucm_init_mode                    2
% 7.45/1.49  --bmc1_ucm_cone_mode                    none
% 7.45/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.45/1.49  --bmc1_ucm_relax_model                  4
% 7.45/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.45/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.45/1.49  --bmc1_ucm_layered_model                none
% 7.45/1.49  --bmc1_ucm_max_lemma_size               10
% 7.45/1.49  
% 7.45/1.49  ------ AIG Options
% 7.45/1.49  
% 7.45/1.49  --aig_mode                              false
% 7.45/1.49  
% 7.45/1.49  ------ Instantiation Options
% 7.45/1.49  
% 7.45/1.49  --instantiation_flag                    true
% 7.45/1.49  --inst_sos_flag                         true
% 7.45/1.49  --inst_sos_phase                        true
% 7.45/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.45/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.45/1.49  --inst_lit_sel_side                     num_symb
% 7.45/1.49  --inst_solver_per_active                1400
% 7.45/1.49  --inst_solver_calls_frac                1.
% 7.45/1.49  --inst_passive_queue_type               priority_queues
% 7.45/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.45/1.49  --inst_passive_queues_freq              [25;2]
% 7.45/1.49  --inst_dismatching                      true
% 7.45/1.49  --inst_eager_unprocessed_to_passive     true
% 7.45/1.49  --inst_prop_sim_given                   true
% 7.45/1.49  --inst_prop_sim_new                     false
% 7.45/1.49  --inst_subs_new                         false
% 7.45/1.49  --inst_eq_res_simp                      false
% 7.45/1.49  --inst_subs_given                       false
% 7.45/1.49  --inst_orphan_elimination               true
% 7.45/1.49  --inst_learning_loop_flag               true
% 7.45/1.49  --inst_learning_start                   3000
% 7.45/1.49  --inst_learning_factor                  2
% 7.45/1.49  --inst_start_prop_sim_after_learn       3
% 7.45/1.49  --inst_sel_renew                        solver
% 7.45/1.49  --inst_lit_activity_flag                true
% 7.45/1.49  --inst_restr_to_given                   false
% 7.45/1.49  --inst_activity_threshold               500
% 7.45/1.49  --inst_out_proof                        true
% 7.45/1.49  
% 7.45/1.49  ------ Resolution Options
% 7.45/1.49  
% 7.45/1.49  --resolution_flag                       true
% 7.45/1.49  --res_lit_sel                           adaptive
% 7.45/1.49  --res_lit_sel_side                      none
% 7.45/1.49  --res_ordering                          kbo
% 7.45/1.49  --res_to_prop_solver                    active
% 7.45/1.49  --res_prop_simpl_new                    false
% 7.45/1.49  --res_prop_simpl_given                  true
% 7.45/1.49  --res_passive_queue_type                priority_queues
% 7.45/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.45/1.49  --res_passive_queues_freq               [15;5]
% 7.45/1.49  --res_forward_subs                      full
% 7.45/1.49  --res_backward_subs                     full
% 7.45/1.49  --res_forward_subs_resolution           true
% 7.45/1.49  --res_backward_subs_resolution          true
% 7.45/1.49  --res_orphan_elimination                true
% 7.45/1.49  --res_time_limit                        2.
% 7.45/1.49  --res_out_proof                         true
% 7.45/1.49  
% 7.45/1.49  ------ Superposition Options
% 7.45/1.49  
% 7.45/1.49  --superposition_flag                    true
% 7.45/1.49  --sup_passive_queue_type                priority_queues
% 7.45/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.45/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.45/1.49  --demod_completeness_check              fast
% 7.45/1.49  --demod_use_ground                      true
% 7.45/1.49  --sup_to_prop_solver                    passive
% 7.45/1.49  --sup_prop_simpl_new                    true
% 7.45/1.49  --sup_prop_simpl_given                  true
% 7.45/1.49  --sup_fun_splitting                     true
% 7.45/1.49  --sup_smt_interval                      50000
% 7.45/1.49  
% 7.45/1.49  ------ Superposition Simplification Setup
% 7.45/1.49  
% 7.45/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.45/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.45/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.45/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.45/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.45/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.45/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.45/1.49  --sup_immed_triv                        [TrivRules]
% 7.45/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.45/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.45/1.49  --sup_immed_bw_main                     []
% 7.45/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.45/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.45/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.45/1.49  --sup_input_bw                          []
% 7.45/1.49  
% 7.45/1.49  ------ Combination Options
% 7.45/1.49  
% 7.45/1.49  --comb_res_mult                         3
% 7.45/1.49  --comb_sup_mult                         2
% 7.45/1.49  --comb_inst_mult                        10
% 7.45/1.49  
% 7.45/1.49  ------ Debug Options
% 7.45/1.49  
% 7.45/1.49  --dbg_backtrace                         false
% 7.45/1.49  --dbg_dump_prop_clauses                 false
% 7.45/1.49  --dbg_dump_prop_clauses_file            -
% 7.45/1.49  --dbg_out_stat                          false
% 7.45/1.49  ------ Parsing...
% 7.45/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.45/1.49  
% 7.45/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 7.45/1.49  
% 7.45/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.45/1.49  
% 7.45/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.45/1.49  ------ Proving...
% 7.45/1.49  ------ Problem Properties 
% 7.45/1.49  
% 7.45/1.49  
% 7.45/1.49  clauses                                 50
% 7.45/1.49  conjectures                             13
% 7.45/1.49  EPR                                     14
% 7.45/1.49  Horn                                    39
% 7.45/1.49  unary                                   17
% 7.45/1.49  binary                                  11
% 7.45/1.49  lits                                    145
% 7.45/1.49  lits eq                                 21
% 7.45/1.49  fd_pure                                 0
% 7.45/1.49  fd_pseudo                               0
% 7.45/1.49  fd_cond                                 4
% 7.45/1.49  fd_pseudo_cond                          4
% 7.45/1.49  AC symbols                              0
% 7.45/1.49  
% 7.45/1.49  ------ Schedule dynamic 5 is on 
% 7.45/1.49  
% 7.45/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.45/1.49  
% 7.45/1.49  
% 7.45/1.49  ------ 
% 7.45/1.49  Current options:
% 7.45/1.49  ------ 
% 7.45/1.49  
% 7.45/1.49  ------ Input Options
% 7.45/1.49  
% 7.45/1.49  --out_options                           all
% 7.45/1.49  --tptp_safe_out                         true
% 7.45/1.49  --problem_path                          ""
% 7.45/1.49  --include_path                          ""
% 7.45/1.49  --clausifier                            res/vclausify_rel
% 7.45/1.49  --clausifier_options                    ""
% 7.45/1.49  --stdin                                 false
% 7.45/1.49  --stats_out                             all
% 7.45/1.49  
% 7.45/1.49  ------ General Options
% 7.45/1.49  
% 7.45/1.49  --fof                                   false
% 7.45/1.49  --time_out_real                         305.
% 7.45/1.49  --time_out_virtual                      -1.
% 7.45/1.49  --symbol_type_check                     false
% 7.45/1.49  --clausify_out                          false
% 7.45/1.49  --sig_cnt_out                           false
% 7.45/1.49  --trig_cnt_out                          false
% 7.45/1.49  --trig_cnt_out_tolerance                1.
% 7.45/1.49  --trig_cnt_out_sk_spl                   false
% 7.45/1.49  --abstr_cl_out                          false
% 7.45/1.49  
% 7.45/1.49  ------ Global Options
% 7.45/1.49  
% 7.45/1.49  --schedule                              default
% 7.45/1.49  --add_important_lit                     false
% 7.45/1.49  --prop_solver_per_cl                    1000
% 7.45/1.49  --min_unsat_core                        false
% 7.45/1.49  --soft_assumptions                      false
% 7.45/1.49  --soft_lemma_size                       3
% 7.45/1.49  --prop_impl_unit_size                   0
% 7.45/1.49  --prop_impl_unit                        []
% 7.45/1.49  --share_sel_clauses                     true
% 7.45/1.49  --reset_solvers                         false
% 7.45/1.49  --bc_imp_inh                            [conj_cone]
% 7.45/1.49  --conj_cone_tolerance                   3.
% 7.45/1.49  --extra_neg_conj                        none
% 7.45/1.49  --large_theory_mode                     true
% 7.45/1.49  --prolific_symb_bound                   200
% 7.45/1.49  --lt_threshold                          2000
% 7.45/1.49  --clause_weak_htbl                      true
% 7.45/1.49  --gc_record_bc_elim                     false
% 7.45/1.49  
% 7.45/1.49  ------ Preprocessing Options
% 7.45/1.49  
% 7.45/1.49  --preprocessing_flag                    true
% 7.45/1.49  --time_out_prep_mult                    0.1
% 7.45/1.49  --splitting_mode                        input
% 7.45/1.49  --splitting_grd                         true
% 7.45/1.49  --splitting_cvd                         false
% 7.45/1.49  --splitting_cvd_svl                     false
% 7.45/1.49  --splitting_nvd                         32
% 7.45/1.49  --sub_typing                            true
% 7.45/1.49  --prep_gs_sim                           true
% 7.45/1.49  --prep_unflatten                        true
% 7.45/1.49  --prep_res_sim                          true
% 7.45/1.49  --prep_upred                            true
% 7.45/1.49  --prep_sem_filter                       exhaustive
% 7.45/1.49  --prep_sem_filter_out                   false
% 7.45/1.49  --pred_elim                             true
% 7.45/1.49  --res_sim_input                         true
% 7.45/1.49  --eq_ax_congr_red                       true
% 7.45/1.49  --pure_diseq_elim                       true
% 7.45/1.49  --brand_transform                       false
% 7.45/1.49  --non_eq_to_eq                          false
% 7.45/1.49  --prep_def_merge                        true
% 7.45/1.49  --prep_def_merge_prop_impl              false
% 7.45/1.49  --prep_def_merge_mbd                    true
% 7.45/1.49  --prep_def_merge_tr_red                 false
% 7.45/1.49  --prep_def_merge_tr_cl                  false
% 7.45/1.49  --smt_preprocessing                     true
% 7.45/1.49  --smt_ac_axioms                         fast
% 7.45/1.49  --preprocessed_out                      false
% 7.45/1.49  --preprocessed_stats                    false
% 7.45/1.49  
% 7.45/1.49  ------ Abstraction refinement Options
% 7.45/1.49  
% 7.45/1.49  --abstr_ref                             []
% 7.45/1.49  --abstr_ref_prep                        false
% 7.45/1.49  --abstr_ref_until_sat                   false
% 7.45/1.49  --abstr_ref_sig_restrict                funpre
% 7.45/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.45/1.49  --abstr_ref_under                       []
% 7.45/1.49  
% 7.45/1.49  ------ SAT Options
% 7.45/1.49  
% 7.45/1.49  --sat_mode                              false
% 7.45/1.49  --sat_fm_restart_options                ""
% 7.45/1.49  --sat_gr_def                            false
% 7.45/1.49  --sat_epr_types                         true
% 7.45/1.49  --sat_non_cyclic_types                  false
% 7.45/1.49  --sat_finite_models                     false
% 7.45/1.49  --sat_fm_lemmas                         false
% 7.45/1.49  --sat_fm_prep                           false
% 7.45/1.49  --sat_fm_uc_incr                        true
% 7.45/1.49  --sat_out_model                         small
% 7.45/1.49  --sat_out_clauses                       false
% 7.45/1.49  
% 7.45/1.49  ------ QBF Options
% 7.45/1.49  
% 7.45/1.49  --qbf_mode                              false
% 7.45/1.49  --qbf_elim_univ                         false
% 7.45/1.49  --qbf_dom_inst                          none
% 7.45/1.49  --qbf_dom_pre_inst                      false
% 7.45/1.49  --qbf_sk_in                             false
% 7.45/1.49  --qbf_pred_elim                         true
% 7.45/1.49  --qbf_split                             512
% 7.45/1.49  
% 7.45/1.49  ------ BMC1 Options
% 7.45/1.49  
% 7.45/1.49  --bmc1_incremental                      false
% 7.45/1.49  --bmc1_axioms                           reachable_all
% 7.45/1.49  --bmc1_min_bound                        0
% 7.45/1.49  --bmc1_max_bound                        -1
% 7.45/1.49  --bmc1_max_bound_default                -1
% 7.45/1.49  --bmc1_symbol_reachability              true
% 7.45/1.49  --bmc1_property_lemmas                  false
% 7.45/1.49  --bmc1_k_induction                      false
% 7.45/1.49  --bmc1_non_equiv_states                 false
% 7.45/1.49  --bmc1_deadlock                         false
% 7.45/1.49  --bmc1_ucm                              false
% 7.45/1.49  --bmc1_add_unsat_core                   none
% 7.45/1.49  --bmc1_unsat_core_children              false
% 7.45/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.45/1.49  --bmc1_out_stat                         full
% 7.45/1.49  --bmc1_ground_init                      false
% 7.45/1.49  --bmc1_pre_inst_next_state              false
% 7.45/1.49  --bmc1_pre_inst_state                   false
% 7.45/1.49  --bmc1_pre_inst_reach_state             false
% 7.45/1.49  --bmc1_out_unsat_core                   false
% 7.45/1.49  --bmc1_aig_witness_out                  false
% 7.45/1.49  --bmc1_verbose                          false
% 7.45/1.49  --bmc1_dump_clauses_tptp                false
% 7.45/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.45/1.49  --bmc1_dump_file                        -
% 7.45/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.45/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.45/1.49  --bmc1_ucm_extend_mode                  1
% 7.45/1.49  --bmc1_ucm_init_mode                    2
% 7.45/1.49  --bmc1_ucm_cone_mode                    none
% 7.45/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.45/1.49  --bmc1_ucm_relax_model                  4
% 7.45/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.45/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.45/1.49  --bmc1_ucm_layered_model                none
% 7.45/1.49  --bmc1_ucm_max_lemma_size               10
% 7.45/1.49  
% 7.45/1.49  ------ AIG Options
% 7.45/1.49  
% 7.45/1.49  --aig_mode                              false
% 7.45/1.49  
% 7.45/1.49  ------ Instantiation Options
% 7.45/1.49  
% 7.45/1.49  --instantiation_flag                    true
% 7.45/1.49  --inst_sos_flag                         true
% 7.45/1.49  --inst_sos_phase                        true
% 7.45/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.45/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.45/1.49  --inst_lit_sel_side                     none
% 7.45/1.49  --inst_solver_per_active                1400
% 7.45/1.49  --inst_solver_calls_frac                1.
% 7.45/1.49  --inst_passive_queue_type               priority_queues
% 7.45/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.45/1.49  --inst_passive_queues_freq              [25;2]
% 7.45/1.49  --inst_dismatching                      true
% 7.45/1.49  --inst_eager_unprocessed_to_passive     true
% 7.45/1.49  --inst_prop_sim_given                   true
% 7.45/1.49  --inst_prop_sim_new                     false
% 7.45/1.49  --inst_subs_new                         false
% 7.45/1.49  --inst_eq_res_simp                      false
% 7.45/1.49  --inst_subs_given                       false
% 7.45/1.49  --inst_orphan_elimination               true
% 7.45/1.49  --inst_learning_loop_flag               true
% 7.45/1.49  --inst_learning_start                   3000
% 7.45/1.49  --inst_learning_factor                  2
% 7.45/1.49  --inst_start_prop_sim_after_learn       3
% 7.45/1.49  --inst_sel_renew                        solver
% 7.45/1.49  --inst_lit_activity_flag                true
% 7.45/1.49  --inst_restr_to_given                   false
% 7.45/1.49  --inst_activity_threshold               500
% 7.45/1.49  --inst_out_proof                        true
% 7.45/1.49  
% 7.45/1.49  ------ Resolution Options
% 7.45/1.49  
% 7.45/1.49  --resolution_flag                       false
% 7.45/1.49  --res_lit_sel                           adaptive
% 7.45/1.49  --res_lit_sel_side                      none
% 7.45/1.49  --res_ordering                          kbo
% 7.45/1.49  --res_to_prop_solver                    active
% 7.45/1.49  --res_prop_simpl_new                    false
% 7.45/1.49  --res_prop_simpl_given                  true
% 7.45/1.49  --res_passive_queue_type                priority_queues
% 7.45/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.45/1.49  --res_passive_queues_freq               [15;5]
% 7.45/1.49  --res_forward_subs                      full
% 7.45/1.49  --res_backward_subs                     full
% 7.45/1.49  --res_forward_subs_resolution           true
% 7.45/1.49  --res_backward_subs_resolution          true
% 7.45/1.49  --res_orphan_elimination                true
% 7.45/1.49  --res_time_limit                        2.
% 7.45/1.49  --res_out_proof                         true
% 7.45/1.49  
% 7.45/1.49  ------ Superposition Options
% 7.45/1.49  
% 7.45/1.49  --superposition_flag                    true
% 7.45/1.49  --sup_passive_queue_type                priority_queues
% 7.45/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.45/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.45/1.49  --demod_completeness_check              fast
% 7.45/1.49  --demod_use_ground                      true
% 7.45/1.49  --sup_to_prop_solver                    passive
% 7.45/1.49  --sup_prop_simpl_new                    true
% 7.45/1.49  --sup_prop_simpl_given                  true
% 7.45/1.49  --sup_fun_splitting                     true
% 7.45/1.49  --sup_smt_interval                      50000
% 7.45/1.49  
% 7.45/1.49  ------ Superposition Simplification Setup
% 7.45/1.49  
% 7.45/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.45/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.45/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.45/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.45/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.45/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.45/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.45/1.49  --sup_immed_triv                        [TrivRules]
% 7.45/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.45/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.45/1.49  --sup_immed_bw_main                     []
% 7.45/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.45/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.45/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.45/1.49  --sup_input_bw                          []
% 7.45/1.49  
% 7.45/1.49  ------ Combination Options
% 7.45/1.49  
% 7.45/1.49  --comb_res_mult                         3
% 7.45/1.49  --comb_sup_mult                         2
% 7.45/1.49  --comb_inst_mult                        10
% 7.45/1.49  
% 7.45/1.49  ------ Debug Options
% 7.45/1.49  
% 7.45/1.49  --dbg_backtrace                         false
% 7.45/1.49  --dbg_dump_prop_clauses                 false
% 7.45/1.49  --dbg_dump_prop_clauses_file            -
% 7.45/1.49  --dbg_out_stat                          false
% 7.45/1.49  
% 7.45/1.49  
% 7.45/1.49  
% 7.45/1.49  
% 7.45/1.49  ------ Proving...
% 7.45/1.49  
% 7.45/1.49  
% 7.45/1.49  % SZS status Theorem for theBenchmark.p
% 7.45/1.49  
% 7.45/1.49   Resolution empty clause
% 7.45/1.49  
% 7.45/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.45/1.49  
% 7.45/1.49  fof(f8,axiom,(
% 7.45/1.49    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 7.45/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.49  
% 7.45/1.49  fof(f98,plain,(
% 7.45/1.49    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 7.45/1.49    inference(cnf_transformation,[],[f8])).
% 7.45/1.49  
% 7.45/1.49  fof(f7,axiom,(
% 7.45/1.49    ! [X0] : k2_subset_1(X0) = X0),
% 7.45/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.49  
% 7.45/1.49  fof(f97,plain,(
% 7.45/1.49    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 7.45/1.49    inference(cnf_transformation,[],[f7])).
% 7.45/1.49  
% 7.45/1.49  fof(f17,axiom,(
% 7.45/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.45/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.49  
% 7.45/1.49  fof(f42,plain,(
% 7.45/1.49    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.45/1.49    inference(ennf_transformation,[],[f17])).
% 7.45/1.49  
% 7.45/1.49  fof(f109,plain,(
% 7.45/1.49    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.45/1.49    inference(cnf_transformation,[],[f42])).
% 7.45/1.49  
% 7.45/1.49  fof(f20,axiom,(
% 7.45/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.45/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.49  
% 7.45/1.49  fof(f47,plain,(
% 7.45/1.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.45/1.49    inference(ennf_transformation,[],[f20])).
% 7.45/1.49  
% 7.45/1.49  fof(f48,plain,(
% 7.45/1.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.45/1.49    inference(flattening,[],[f47])).
% 7.45/1.49  
% 7.45/1.49  fof(f73,plain,(
% 7.45/1.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.45/1.49    inference(nnf_transformation,[],[f48])).
% 7.45/1.49  
% 7.45/1.49  fof(f118,plain,(
% 7.45/1.49    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.45/1.49    inference(cnf_transformation,[],[f73])).
% 7.45/1.49  
% 7.45/1.49  fof(f148,plain,(
% 7.45/1.49    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 7.45/1.49    inference(equality_resolution,[],[f118])).
% 7.45/1.49  
% 7.45/1.49  fof(f5,axiom,(
% 7.45/1.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.45/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.49  
% 7.45/1.49  fof(f68,plain,(
% 7.45/1.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.45/1.49    inference(nnf_transformation,[],[f5])).
% 7.45/1.49  
% 7.45/1.49  fof(f69,plain,(
% 7.45/1.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.45/1.49    inference(flattening,[],[f68])).
% 7.45/1.49  
% 7.45/1.49  fof(f91,plain,(
% 7.45/1.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 7.45/1.49    inference(cnf_transformation,[],[f69])).
% 7.45/1.49  
% 7.45/1.49  fof(f144,plain,(
% 7.45/1.49    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 7.45/1.49    inference(equality_resolution,[],[f91])).
% 7.45/1.49  
% 7.45/1.49  fof(f1,axiom,(
% 7.45/1.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 7.45/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.49  
% 7.45/1.49  fof(f61,plain,(
% 7.45/1.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 7.45/1.49    inference(nnf_transformation,[],[f1])).
% 7.45/1.49  
% 7.45/1.49  fof(f62,plain,(
% 7.45/1.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.45/1.49    inference(rectify,[],[f61])).
% 7.45/1.49  
% 7.45/1.49  fof(f63,plain,(
% 7.45/1.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 7.45/1.49    introduced(choice_axiom,[])).
% 7.45/1.49  
% 7.45/1.49  fof(f64,plain,(
% 7.45/1.49    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.45/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f62,f63])).
% 7.45/1.49  
% 7.45/1.49  fof(f85,plain,(
% 7.45/1.49    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 7.45/1.49    inference(cnf_transformation,[],[f64])).
% 7.45/1.49  
% 7.45/1.49  fof(f9,axiom,(
% 7.45/1.49    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 7.45/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.49  
% 7.45/1.49  fof(f99,plain,(
% 7.45/1.49    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 7.45/1.49    inference(cnf_transformation,[],[f9])).
% 7.45/1.49  
% 7.45/1.49  fof(f13,axiom,(
% 7.45/1.49    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 7.45/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.49  
% 7.45/1.49  fof(f38,plain,(
% 7.45/1.49    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 7.45/1.49    inference(ennf_transformation,[],[f13])).
% 7.45/1.49  
% 7.45/1.49  fof(f105,plain,(
% 7.45/1.49    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 7.45/1.49    inference(cnf_transformation,[],[f38])).
% 7.45/1.49  
% 7.45/1.49  fof(f15,axiom,(
% 7.45/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.45/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.49  
% 7.45/1.49  fof(f31,plain,(
% 7.45/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.45/1.49    inference(pure_predicate_removal,[],[f15])).
% 7.45/1.49  
% 7.45/1.49  fof(f40,plain,(
% 7.45/1.49    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.45/1.49    inference(ennf_transformation,[],[f31])).
% 7.45/1.49  
% 7.45/1.49  fof(f107,plain,(
% 7.45/1.49    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.45/1.49    inference(cnf_transformation,[],[f40])).
% 7.45/1.49  
% 7.45/1.49  fof(f12,axiom,(
% 7.45/1.49    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 7.45/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.49  
% 7.45/1.49  fof(f37,plain,(
% 7.45/1.49    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.45/1.49    inference(ennf_transformation,[],[f12])).
% 7.45/1.49  
% 7.45/1.49  fof(f72,plain,(
% 7.45/1.49    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.45/1.49    inference(nnf_transformation,[],[f37])).
% 7.45/1.49  
% 7.45/1.49  fof(f103,plain,(
% 7.45/1.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.45/1.49    inference(cnf_transformation,[],[f72])).
% 7.45/1.49  
% 7.45/1.49  fof(f14,axiom,(
% 7.45/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.45/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.49  
% 7.45/1.49  fof(f39,plain,(
% 7.45/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.45/1.49    inference(ennf_transformation,[],[f14])).
% 7.45/1.49  
% 7.45/1.49  fof(f106,plain,(
% 7.45/1.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.45/1.49    inference(cnf_transformation,[],[f39])).
% 7.45/1.49  
% 7.45/1.49  fof(f3,axiom,(
% 7.45/1.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.45/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.49  
% 7.45/1.49  fof(f88,plain,(
% 7.45/1.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.45/1.49    inference(cnf_transformation,[],[f3])).
% 7.45/1.49  
% 7.45/1.49  fof(f4,axiom,(
% 7.45/1.49    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 7.45/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.49  
% 7.45/1.49  fof(f33,plain,(
% 7.45/1.49    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 7.45/1.49    inference(ennf_transformation,[],[f4])).
% 7.45/1.49  
% 7.45/1.49  fof(f89,plain,(
% 7.45/1.49    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 7.45/1.49    inference(cnf_transformation,[],[f33])).
% 7.45/1.49  
% 7.45/1.49  fof(f27,conjecture,(
% 7.45/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 7.45/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.49  
% 7.45/1.49  fof(f28,negated_conjecture,(
% 7.45/1.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 7.45/1.49    inference(negated_conjecture,[],[f27])).
% 7.45/1.49  
% 7.45/1.49  fof(f59,plain,(
% 7.45/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 7.45/1.49    inference(ennf_transformation,[],[f28])).
% 7.45/1.49  
% 7.45/1.49  fof(f60,plain,(
% 7.45/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.45/1.49    inference(flattening,[],[f59])).
% 7.45/1.49  
% 7.45/1.49  fof(f77,plain,(
% 7.45/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.45/1.49    inference(nnf_transformation,[],[f60])).
% 7.45/1.49  
% 7.45/1.49  fof(f78,plain,(
% 7.45/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.45/1.49    inference(flattening,[],[f77])).
% 7.45/1.49  
% 7.45/1.49  fof(f82,plain,(
% 7.45/1.49    ( ! [X2,X0,X1] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => ((~v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & sK5 = X2 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(sK5))) )),
% 7.45/1.49    introduced(choice_axiom,[])).
% 7.45/1.49  
% 7.45/1.49  fof(f81,plain,(
% 7.45/1.49    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(sK4,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK4,X0,X1)) & sK4 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 7.45/1.49    introduced(choice_axiom,[])).
% 7.45/1.49  
% 7.45/1.49  fof(f80,plain,(
% 7.45/1.49    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~v5_pre_topc(X2,X0,sK3)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | v5_pre_topc(X2,X0,sK3)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) & v1_funct_1(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3))) )),
% 7.45/1.49    introduced(choice_axiom,[])).
% 7.45/1.49  
% 7.45/1.49  fof(f79,plain,(
% 7.45/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK2,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK2,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2))),
% 7.45/1.49    introduced(choice_axiom,[])).
% 7.45/1.49  
% 7.45/1.49  fof(f83,plain,(
% 7.45/1.49    ((((~v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~v5_pre_topc(sK4,sK2,sK3)) & (v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | v5_pre_topc(sK4,sK2,sK3)) & sK4 = sK5 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) & v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2)),
% 7.45/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f78,f82,f81,f80,f79])).
% 7.45/1.49  
% 7.45/1.49  fof(f136,plain,(
% 7.45/1.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 7.45/1.49    inference(cnf_transformation,[],[f83])).
% 7.45/1.49  
% 7.45/1.49  fof(f140,plain,(
% 7.45/1.49    sK4 = sK5),
% 7.45/1.49    inference(cnf_transformation,[],[f83])).
% 7.45/1.49  
% 7.45/1.49  fof(f18,axiom,(
% 7.45/1.49    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 7.45/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.49  
% 7.45/1.49  fof(f43,plain,(
% 7.45/1.49    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 7.45/1.49    inference(ennf_transformation,[],[f18])).
% 7.45/1.49  
% 7.45/1.49  fof(f44,plain,(
% 7.45/1.49    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 7.45/1.49    inference(flattening,[],[f43])).
% 7.45/1.49  
% 7.45/1.49  fof(f111,plain,(
% 7.45/1.49    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 7.45/1.49    inference(cnf_transformation,[],[f44])).
% 7.45/1.49  
% 7.45/1.49  fof(f21,axiom,(
% 7.45/1.49    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 7.45/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.49  
% 7.45/1.49  fof(f49,plain,(
% 7.45/1.49    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.45/1.49    inference(ennf_transformation,[],[f21])).
% 7.45/1.49  
% 7.45/1.49  fof(f50,plain,(
% 7.45/1.49    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.45/1.49    inference(flattening,[],[f49])).
% 7.45/1.49  
% 7.45/1.49  fof(f74,plain,(
% 7.45/1.49    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.45/1.49    inference(nnf_transformation,[],[f50])).
% 7.45/1.49  
% 7.45/1.49  fof(f121,plain,(
% 7.45/1.49    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.45/1.49    inference(cnf_transformation,[],[f74])).
% 7.45/1.49  
% 7.45/1.49  fof(f137,plain,(
% 7.45/1.49    v1_funct_1(sK5)),
% 7.45/1.49    inference(cnf_transformation,[],[f83])).
% 7.45/1.49  
% 7.45/1.49  fof(f135,plain,(
% 7.45/1.49    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))),
% 7.45/1.49    inference(cnf_transformation,[],[f83])).
% 7.45/1.49  
% 7.45/1.49  fof(f16,axiom,(
% 7.45/1.49    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 7.45/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.49  
% 7.45/1.49  fof(f41,plain,(
% 7.45/1.49    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 7.45/1.49    inference(ennf_transformation,[],[f16])).
% 7.45/1.49  
% 7.45/1.49  fof(f108,plain,(
% 7.45/1.49    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 7.45/1.49    inference(cnf_transformation,[],[f41])).
% 7.45/1.49  
% 7.45/1.49  fof(f139,plain,(
% 7.45/1.49    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))),
% 7.45/1.49    inference(cnf_transformation,[],[f83])).
% 7.45/1.49  
% 7.45/1.49  fof(f138,plain,(
% 7.45/1.49    v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))),
% 7.45/1.49    inference(cnf_transformation,[],[f83])).
% 7.45/1.49  
% 7.45/1.49  fof(f19,axiom,(
% 7.45/1.49    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)))))),
% 7.45/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.49  
% 7.45/1.49  fof(f45,plain,(
% 7.45/1.49    ! [X0,X1] : (! [X2] : (((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.45/1.49    inference(ennf_transformation,[],[f19])).
% 7.45/1.49  
% 7.45/1.49  fof(f46,plain,(
% 7.45/1.49    ! [X0,X1] : (! [X2] : ((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.45/1.49    inference(flattening,[],[f45])).
% 7.45/1.49  
% 7.45/1.49  fof(f113,plain,(
% 7.45/1.49    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.45/1.49    inference(cnf_transformation,[],[f46])).
% 7.45/1.49  
% 7.45/1.49  fof(f6,axiom,(
% 7.45/1.49    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 7.45/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.49  
% 7.45/1.49  fof(f34,plain,(
% 7.45/1.49    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 7.45/1.49    inference(ennf_transformation,[],[f6])).
% 7.45/1.49  
% 7.45/1.49  fof(f70,plain,(
% 7.45/1.49    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 7.45/1.49    inference(nnf_transformation,[],[f34])).
% 7.45/1.49  
% 7.45/1.49  fof(f95,plain,(
% 7.45/1.49    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,X0) | ~v1_xboole_0(X0)) )),
% 7.45/1.49    inference(cnf_transformation,[],[f70])).
% 7.45/1.49  
% 7.45/1.49  fof(f25,axiom,(
% 7.45/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 7.45/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.49  
% 7.45/1.49  fof(f55,plain,(
% 7.45/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.45/1.49    inference(ennf_transformation,[],[f25])).
% 7.45/1.49  
% 7.45/1.49  fof(f56,plain,(
% 7.45/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.45/1.49    inference(flattening,[],[f55])).
% 7.45/1.49  
% 7.45/1.49  fof(f75,plain,(
% 7.45/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.45/1.49    inference(nnf_transformation,[],[f56])).
% 7.45/1.49  
% 7.45/1.49  fof(f126,plain,(
% 7.45/1.49    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.45/1.49    inference(cnf_transformation,[],[f75])).
% 7.45/1.49  
% 7.45/1.49  fof(f152,plain,(
% 7.45/1.49    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.45/1.49    inference(equality_resolution,[],[f126])).
% 7.45/1.49  
% 7.45/1.49  fof(f130,plain,(
% 7.45/1.49    v2_pre_topc(sK2)),
% 7.45/1.49    inference(cnf_transformation,[],[f83])).
% 7.45/1.49  
% 7.45/1.49  fof(f131,plain,(
% 7.45/1.49    l1_pre_topc(sK2)),
% 7.45/1.49    inference(cnf_transformation,[],[f83])).
% 7.45/1.49  
% 7.45/1.49  fof(f132,plain,(
% 7.45/1.49    v2_pre_topc(sK3)),
% 7.45/1.49    inference(cnf_transformation,[],[f83])).
% 7.45/1.49  
% 7.45/1.49  fof(f133,plain,(
% 7.45/1.49    l1_pre_topc(sK3)),
% 7.45/1.49    inference(cnf_transformation,[],[f83])).
% 7.45/1.49  
% 7.45/1.49  fof(f141,plain,(
% 7.45/1.49    v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | v5_pre_topc(sK4,sK2,sK3)),
% 7.45/1.49    inference(cnf_transformation,[],[f83])).
% 7.45/1.49  
% 7.45/1.49  fof(f142,plain,(
% 7.45/1.49    ~v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~v5_pre_topc(sK4,sK2,sK3)),
% 7.45/1.49    inference(cnf_transformation,[],[f83])).
% 7.45/1.49  
% 7.45/1.49  fof(f24,axiom,(
% 7.45/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 7.45/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.49  
% 7.45/1.49  fof(f29,plain,(
% 7.45/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 7.45/1.49    inference(pure_predicate_removal,[],[f24])).
% 7.45/1.49  
% 7.45/1.49  fof(f53,plain,(
% 7.45/1.49    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.45/1.49    inference(ennf_transformation,[],[f29])).
% 7.45/1.49  
% 7.45/1.49  fof(f54,plain,(
% 7.45/1.49    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.45/1.49    inference(flattening,[],[f53])).
% 7.45/1.49  
% 7.45/1.49  fof(f125,plain,(
% 7.45/1.49    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.45/1.49    inference(cnf_transformation,[],[f54])).
% 7.45/1.49  
% 7.45/1.49  fof(f22,axiom,(
% 7.45/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 7.45/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.49  
% 7.45/1.49  fof(f30,plain,(
% 7.45/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 7.45/1.49    inference(pure_predicate_removal,[],[f22])).
% 7.45/1.49  
% 7.45/1.49  fof(f51,plain,(
% 7.45/1.49    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 7.45/1.49    inference(ennf_transformation,[],[f30])).
% 7.45/1.49  
% 7.45/1.49  fof(f123,plain,(
% 7.45/1.49    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 7.45/1.49    inference(cnf_transformation,[],[f51])).
% 7.45/1.49  
% 7.45/1.49  fof(f23,axiom,(
% 7.45/1.49    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.45/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.49  
% 7.45/1.49  fof(f52,plain,(
% 7.45/1.49    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.45/1.49    inference(ennf_transformation,[],[f23])).
% 7.45/1.49  
% 7.45/1.49  fof(f124,plain,(
% 7.45/1.49    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 7.45/1.49    inference(cnf_transformation,[],[f52])).
% 7.45/1.49  
% 7.45/1.49  fof(f127,plain,(
% 7.45/1.49    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.45/1.49    inference(cnf_transformation,[],[f75])).
% 7.45/1.49  
% 7.45/1.49  fof(f151,plain,(
% 7.45/1.49    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.45/1.49    inference(equality_resolution,[],[f127])).
% 7.45/1.49  
% 7.45/1.49  fof(f26,axiom,(
% 7.45/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 7.45/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.49  
% 7.45/1.49  fof(f57,plain,(
% 7.45/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.45/1.49    inference(ennf_transformation,[],[f26])).
% 7.45/1.49  
% 7.45/1.49  fof(f58,plain,(
% 7.45/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.45/1.49    inference(flattening,[],[f57])).
% 7.45/1.49  
% 7.45/1.49  fof(f76,plain,(
% 7.45/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.45/1.49    inference(nnf_transformation,[],[f58])).
% 7.45/1.49  
% 7.45/1.49  fof(f129,plain,(
% 7.45/1.49    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.45/1.49    inference(cnf_transformation,[],[f76])).
% 7.45/1.49  
% 7.45/1.49  fof(f153,plain,(
% 7.45/1.49    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.45/1.49    inference(equality_resolution,[],[f129])).
% 7.45/1.49  
% 7.45/1.49  fof(f128,plain,(
% 7.45/1.49    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.45/1.49    inference(cnf_transformation,[],[f76])).
% 7.45/1.49  
% 7.45/1.49  fof(f154,plain,(
% 7.45/1.49    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.45/1.49    inference(equality_resolution,[],[f128])).
% 7.45/1.49  
% 7.45/1.49  fof(f96,plain,(
% 7.45/1.49    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 7.45/1.49    inference(cnf_transformation,[],[f70])).
% 7.45/1.49  
% 7.45/1.49  cnf(c_14,plain,
% 7.45/1.49      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 7.45/1.49      inference(cnf_transformation,[],[f98]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_3139,plain,
% 7.45/1.49      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_13,plain,
% 7.45/1.49      ( k2_subset_1(X0) = X0 ),
% 7.45/1.49      inference(cnf_transformation,[],[f97]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_3149,plain,
% 7.45/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.45/1.49      inference(light_normalisation,[status(thm)],[c_3139,c_13]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_25,plain,
% 7.45/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.45/1.49      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.45/1.49      inference(cnf_transformation,[],[f109]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_3135,plain,
% 7.45/1.49      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.45/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_6099,plain,
% 7.45/1.49      ( k1_relset_1(X0,X1,k2_zfmisc_1(X0,X1)) = k1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_3149,c_3135]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_33,plain,
% 7.45/1.49      ( v1_funct_2(X0,k1_xboole_0,X1)
% 7.45/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.45/1.49      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 7.45/1.49      inference(cnf_transformation,[],[f148]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_3131,plain,
% 7.45/1.49      ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
% 7.45/1.49      | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
% 7.45/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_7,plain,
% 7.45/1.49      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.45/1.49      inference(cnf_transformation,[],[f144]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_3156,plain,
% 7.45/1.49      ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
% 7.45/1.49      | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
% 7.45/1.49      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.45/1.49      inference(light_normalisation,[status(thm)],[c_3131,c_7]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_11212,plain,
% 7.45/1.49      ( k1_relat_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_xboole_0
% 7.45/1.49      | v1_funct_2(k2_zfmisc_1(k1_xboole_0,X0),k1_xboole_0,X0) = iProver_top
% 7.45/1.49      | m1_subset_1(k2_zfmisc_1(k1_xboole_0,X0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_6099,c_3156]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_0,plain,
% 7.45/1.49      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 7.45/1.49      inference(cnf_transformation,[],[f85]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_3147,plain,
% 7.45/1.49      ( r2_hidden(sK0(X0),X0) = iProver_top | v1_xboole_0(X0) = iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_15,plain,
% 7.45/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 7.45/1.49      inference(cnf_transformation,[],[f99]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_3138,plain,
% 7.45/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_21,plain,
% 7.45/1.49      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 7.45/1.49      inference(cnf_transformation,[],[f105]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_23,plain,
% 7.45/1.49      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.45/1.49      inference(cnf_transformation,[],[f107]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_20,plain,
% 7.45/1.49      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 7.45/1.49      inference(cnf_transformation,[],[f103]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_764,plain,
% 7.45/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.45/1.49      | r1_tarski(k1_relat_1(X0),X1)
% 7.45/1.49      | ~ v1_relat_1(X0) ),
% 7.45/1.49      inference(resolution,[status(thm)],[c_23,c_20]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_22,plain,
% 7.45/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 7.45/1.49      inference(cnf_transformation,[],[f106]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_768,plain,
% 7.45/1.49      ( r1_tarski(k1_relat_1(X0),X1)
% 7.45/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.45/1.49      inference(global_propositional_subsumption,[status(thm)],[c_764,c_22]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_769,plain,
% 7.45/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.45/1.49      | r1_tarski(k1_relat_1(X0),X1) ),
% 7.45/1.49      inference(renaming,[status(thm)],[c_768]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_808,plain,
% 7.45/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.45/1.49      | ~ r2_hidden(X3,X4)
% 7.45/1.49      | X1 != X3
% 7.45/1.49      | k1_relat_1(X0) != X4 ),
% 7.45/1.49      inference(resolution_lifted,[status(thm)],[c_21,c_769]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_809,plain,
% 7.45/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.45/1.49      | ~ r2_hidden(X1,k1_relat_1(X0)) ),
% 7.45/1.49      inference(unflattening,[status(thm)],[c_808]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_3104,plain,
% 7.45/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.45/1.49      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_809]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_4137,plain,
% 7.45/1.49      ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_3138,c_3104]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_4386,plain,
% 7.45/1.49      ( v1_xboole_0(k1_relat_1(k1_xboole_0)) = iProver_top ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_3147,c_4137]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_4,plain,
% 7.45/1.49      ( r1_tarski(k1_xboole_0,X0) ),
% 7.45/1.49      inference(cnf_transformation,[],[f88]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_797,plain,
% 7.45/1.49      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 7.45/1.49      inference(resolution_lifted,[status(thm)],[c_4,c_21]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_798,plain,
% 7.45/1.49      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 7.45/1.49      inference(unflattening,[status(thm)],[c_797]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_3105,plain,
% 7.45/1.49      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_798]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_4186,plain,
% 7.45/1.49      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_3147,c_3105]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_5,plain,
% 7.45/1.49      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 7.45/1.49      inference(cnf_transformation,[],[f89]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_3143,plain,
% 7.45/1.49      ( X0 = X1
% 7.45/1.49      | v1_xboole_0(X0) != iProver_top
% 7.45/1.49      | v1_xboole_0(X1) != iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_5316,plain,
% 7.45/1.49      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_4186,c_3143]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_10497,plain,
% 7.45/1.49      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_4386,c_5316]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_11213,plain,
% 7.45/1.49      ( k1_xboole_0 != k1_xboole_0
% 7.45/1.49      | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top
% 7.45/1.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.45/1.49      inference(light_normalisation,[status(thm)],[c_11212,c_7,c_10497]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_11214,plain,
% 7.45/1.49      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top
% 7.45/1.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.45/1.49      inference(equality_resolution_simp,[status(thm)],[c_11213]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_151,plain,
% 7.45/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_153,plain,
% 7.45/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.45/1.49      inference(instantiation,[status(thm)],[c_151]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_5317,plain,
% 7.45/1.49      ( k1_relat_1(k1_xboole_0) = X0 | v1_xboole_0(X0) != iProver_top ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_4386,c_3143]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_5321,plain,
% 7.45/1.49      ( k1_relat_1(k1_xboole_0) = k1_xboole_0
% 7.45/1.49      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 7.45/1.49      inference(instantiation,[status(thm)],[c_5317]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_6096,plain,
% 7.45/1.49      ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_3138,c_3135]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_10097,plain,
% 7.45/1.49      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 7.45/1.49      | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top
% 7.45/1.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_6096,c_3156]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_17857,plain,
% 7.45/1.49      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top ),
% 7.45/1.49      inference(global_propositional_subsumption,
% 7.45/1.49                [status(thm)],
% 7.45/1.49                [c_11214,c_153,c_4186,c_5321,c_10097]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_52,negated_conjecture,
% 7.45/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
% 7.45/1.49      inference(cnf_transformation,[],[f136]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_3115,plain,
% 7.45/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_52]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_48,negated_conjecture,
% 7.45/1.49      ( sK4 = sK5 ),
% 7.45/1.49      inference(cnf_transformation,[],[f140]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_3151,plain,
% 7.45/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 7.45/1.49      inference(light_normalisation,[status(thm)],[c_3115,c_48]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_26,plain,
% 7.45/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.45/1.49      | v1_partfun1(X0,X1)
% 7.45/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.45/1.49      | ~ v1_funct_1(X0)
% 7.45/1.49      | v1_xboole_0(X2) ),
% 7.45/1.49      inference(cnf_transformation,[],[f111]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_38,plain,
% 7.45/1.49      ( ~ v1_partfun1(X0,X1)
% 7.45/1.49      | ~ v4_relat_1(X0,X1)
% 7.45/1.49      | ~ v1_relat_1(X0)
% 7.45/1.49      | k1_relat_1(X0) = X1 ),
% 7.45/1.49      inference(cnf_transformation,[],[f121]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_698,plain,
% 7.45/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.45/1.49      | ~ v4_relat_1(X0,X1)
% 7.45/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.45/1.49      | ~ v1_funct_1(X0)
% 7.45/1.49      | ~ v1_relat_1(X0)
% 7.45/1.49      | v1_xboole_0(X2)
% 7.45/1.49      | k1_relat_1(X0) = X1 ),
% 7.45/1.49      inference(resolution,[status(thm)],[c_26,c_38]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_702,plain,
% 7.45/1.49      ( ~ v1_funct_1(X0)
% 7.45/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.45/1.49      | ~ v1_funct_2(X0,X1,X2)
% 7.45/1.49      | v1_xboole_0(X2)
% 7.45/1.49      | k1_relat_1(X0) = X1 ),
% 7.45/1.49      inference(global_propositional_subsumption,
% 7.45/1.49                [status(thm)],
% 7.45/1.49                [c_698,c_23,c_22]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_703,plain,
% 7.45/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.45/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.45/1.49      | ~ v1_funct_1(X0)
% 7.45/1.49      | v1_xboole_0(X2)
% 7.45/1.49      | k1_relat_1(X0) = X1 ),
% 7.45/1.49      inference(renaming,[status(thm)],[c_702]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_3107,plain,
% 7.45/1.49      ( k1_relat_1(X0) = X1
% 7.45/1.49      | v1_funct_2(X0,X1,X2) != iProver_top
% 7.45/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.45/1.49      | v1_funct_1(X0) != iProver_top
% 7.45/1.49      | v1_xboole_0(X2) = iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_703]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_5998,plain,
% 7.45/1.49      ( u1_struct_0(sK2) = k1_relat_1(sK5)
% 7.45/1.49      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.45/1.49      | v1_funct_1(sK5) != iProver_top
% 7.45/1.49      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_3151,c_3107]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_51,negated_conjecture,
% 7.45/1.49      ( v1_funct_1(sK5) ),
% 7.45/1.49      inference(cnf_transformation,[],[f137]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_66,plain,
% 7.45/1.49      ( v1_funct_1(sK5) = iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_53,negated_conjecture,
% 7.45/1.49      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 7.45/1.49      inference(cnf_transformation,[],[f135]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_3114,plain,
% 7.45/1.49      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_53]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_3150,plain,
% 7.45/1.49      ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
% 7.45/1.49      inference(light_normalisation,[status(thm)],[c_3114,c_48]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_6146,plain,
% 7.45/1.49      ( u1_struct_0(sK2) = k1_relat_1(sK5)
% 7.45/1.49      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 7.45/1.49      inference(global_propositional_subsumption,
% 7.45/1.49                [status(thm)],
% 7.45/1.49                [c_5998,c_66,c_3150]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_24,plain,
% 7.45/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.45/1.49      | ~ v1_xboole_0(X2)
% 7.45/1.49      | v1_xboole_0(X0) ),
% 7.45/1.49      inference(cnf_transformation,[],[f108]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_3136,plain,
% 7.45/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.45/1.49      | v1_xboole_0(X2) != iProver_top
% 7.45/1.49      | v1_xboole_0(X0) = iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_7950,plain,
% 7.45/1.49      ( v1_xboole_0(u1_struct_0(sK3)) != iProver_top
% 7.45/1.49      | v1_xboole_0(sK5) = iProver_top ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_3151,c_3136]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_8054,plain,
% 7.45/1.49      ( u1_struct_0(sK2) = k1_relat_1(sK5) | v1_xboole_0(sK5) = iProver_top ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_6146,c_7950]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_10496,plain,
% 7.45/1.49      ( u1_struct_0(sK2) = k1_relat_1(sK5) | sK5 = k1_xboole_0 ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_8054,c_5316]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_49,negated_conjecture,
% 7.45/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) ),
% 7.45/1.49      inference(cnf_transformation,[],[f139]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_3118,plain,
% 7.45/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) = iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_11765,plain,
% 7.45/1.49      ( sK5 = k1_xboole_0
% 7.45/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK5),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) = iProver_top ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_10496,c_3118]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_12640,plain,
% 7.45/1.49      ( u1_struct_0(g1_pre_topc(k1_relat_1(sK5),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 7.45/1.49      | sK5 = k1_xboole_0
% 7.45/1.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(k1_relat_1(sK5),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 7.45/1.49      | v1_funct_1(sK5) != iProver_top
% 7.45/1.49      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_11765,c_3107]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_7947,plain,
% 7.45/1.49      ( v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 7.45/1.49      | v1_xboole_0(sK5) = iProver_top ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_3118,c_3136]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_50,negated_conjecture,
% 7.45/1.49      ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) ),
% 7.45/1.49      inference(cnf_transformation,[],[f138]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_3117,plain,
% 7.45/1.49      ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_11766,plain,
% 7.45/1.49      ( sK5 = k1_xboole_0
% 7.45/1.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(k1_relat_1(sK5),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_10496,c_3117]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_11767,plain,
% 7.45/1.49      ( sK5 = k1_xboole_0
% 7.45/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),u1_struct_0(sK3)))) = iProver_top ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_10496,c_3151]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_29,plain,
% 7.45/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.45/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.45/1.49      | ~ v1_funct_1(X0)
% 7.45/1.49      | ~ v1_xboole_0(X0)
% 7.45/1.49      | v1_xboole_0(X1)
% 7.45/1.49      | v1_xboole_0(X2) ),
% 7.45/1.49      inference(cnf_transformation,[],[f113]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_3134,plain,
% 7.45/1.49      ( v1_funct_2(X0,X1,X2) != iProver_top
% 7.45/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.45/1.49      | v1_funct_1(X0) != iProver_top
% 7.45/1.49      | v1_xboole_0(X0) != iProver_top
% 7.45/1.49      | v1_xboole_0(X1) = iProver_top
% 7.45/1.49      | v1_xboole_0(X2) = iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_12419,plain,
% 7.45/1.49      ( sK5 = k1_xboole_0
% 7.45/1.49      | v1_funct_2(sK5,k1_relat_1(sK5),u1_struct_0(sK3)) != iProver_top
% 7.45/1.49      | v1_funct_1(sK5) != iProver_top
% 7.45/1.49      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
% 7.45/1.49      | v1_xboole_0(k1_relat_1(sK5)) = iProver_top
% 7.45/1.49      | v1_xboole_0(sK5) != iProver_top ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_11767,c_3134]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_3569,plain,
% 7.45/1.49      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(sK5) | sK5 = X0 ),
% 7.45/1.49      inference(instantiation,[status(thm)],[c_5]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_3570,plain,
% 7.45/1.49      ( sK5 = X0
% 7.45/1.49      | v1_xboole_0(X0) != iProver_top
% 7.45/1.49      | v1_xboole_0(sK5) != iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_3569]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_3572,plain,
% 7.45/1.49      ( sK5 = k1_xboole_0
% 7.45/1.49      | v1_xboole_0(sK5) != iProver_top
% 7.45/1.49      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 7.45/1.49      inference(instantiation,[status(thm)],[c_3570]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_15558,plain,
% 7.45/1.49      ( sK5 = k1_xboole_0 | v1_xboole_0(sK5) != iProver_top ),
% 7.45/1.49      inference(global_propositional_subsumption,
% 7.45/1.49                [status(thm)],
% 7.45/1.49                [c_12419,c_3572,c_4186]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_15816,plain,
% 7.45/1.49      ( sK5 = k1_xboole_0
% 7.45/1.49      | u1_struct_0(g1_pre_topc(k1_relat_1(sK5),u1_pre_topc(sK2))) = k1_relat_1(sK5) ),
% 7.45/1.49      inference(global_propositional_subsumption,
% 7.45/1.49                [status(thm)],
% 7.45/1.49                [c_12640,c_66,c_3572,c_4186,c_7947,c_11766]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_15817,plain,
% 7.45/1.49      ( u1_struct_0(g1_pre_topc(k1_relat_1(sK5),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 7.45/1.49      | sK5 = k1_xboole_0 ),
% 7.45/1.49      inference(renaming,[status(thm)],[c_15816]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_10,plain,
% 7.45/1.49      ( ~ m1_subset_1(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 7.45/1.49      inference(cnf_transformation,[],[f95]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_3141,plain,
% 7.45/1.49      ( m1_subset_1(X0,X1) != iProver_top
% 7.45/1.49      | v1_xboole_0(X1) != iProver_top
% 7.45/1.49      | v1_xboole_0(X0) = iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_6300,plain,
% 7.45/1.49      ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
% 7.45/1.49      | v1_xboole_0(sK5) = iProver_top ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_3118,c_3141]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_11753,plain,
% 7.45/1.49      ( sK5 = k1_xboole_0
% 7.45/1.49      | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK5),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
% 7.45/1.49      | v1_xboole_0(sK5) = iProver_top ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_10496,c_6300]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_15330,plain,
% 7.45/1.49      ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK5),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
% 7.45/1.49      | sK5 = k1_xboole_0 ),
% 7.45/1.49      inference(global_propositional_subsumption,
% 7.45/1.49                [status(thm)],
% 7.45/1.49                [c_11753,c_3572,c_4186]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_15331,plain,
% 7.45/1.49      ( sK5 = k1_xboole_0
% 7.45/1.49      | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK5),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top ),
% 7.45/1.49      inference(renaming,[status(thm)],[c_15330]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_15832,plain,
% 7.45/1.49      ( sK5 = k1_xboole_0
% 7.45/1.49      | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_15817,c_15331]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_15839,plain,
% 7.45/1.49      ( sK5 = k1_xboole_0
% 7.45/1.49      | v1_funct_2(sK5,k1_relat_1(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_15817,c_11766]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_15838,plain,
% 7.45/1.49      ( sK5 = k1_xboole_0
% 7.45/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) = iProver_top ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_15817,c_11765]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_43,plain,
% 7.45/1.49      ( ~ v5_pre_topc(X0,X1,X2)
% 7.45/1.49      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 7.45/1.49      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.45/1.49      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 7.45/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.45/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 7.45/1.49      | ~ v2_pre_topc(X1)
% 7.45/1.49      | ~ v2_pre_topc(X2)
% 7.45/1.49      | ~ l1_pre_topc(X1)
% 7.45/1.49      | ~ l1_pre_topc(X2)
% 7.45/1.49      | ~ v1_funct_1(X0) ),
% 7.45/1.49      inference(cnf_transformation,[],[f152]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_3123,plain,
% 7.45/1.49      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 7.45/1.49      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) = iProver_top
% 7.45/1.49      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 7.45/1.49      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
% 7.45/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 7.45/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
% 7.45/1.49      | v2_pre_topc(X1) != iProver_top
% 7.45/1.49      | v2_pre_topc(X2) != iProver_top
% 7.45/1.49      | l1_pre_topc(X1) != iProver_top
% 7.45/1.49      | l1_pre_topc(X2) != iProver_top
% 7.45/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_8386,plain,
% 7.45/1.49      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 7.45/1.49      | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 7.45/1.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 7.45/1.49      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 7.45/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
% 7.45/1.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 7.45/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.45/1.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 7.45/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.45/1.49      | v1_funct_1(sK5) != iProver_top ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_3118,c_3123]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_58,negated_conjecture,
% 7.45/1.49      ( v2_pre_topc(sK2) ),
% 7.45/1.49      inference(cnf_transformation,[],[f130]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_59,plain,
% 7.45/1.49      ( v2_pre_topc(sK2) = iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_58]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_57,negated_conjecture,
% 7.45/1.49      ( l1_pre_topc(sK2) ),
% 7.45/1.49      inference(cnf_transformation,[],[f131]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_60,plain,
% 7.45/1.49      ( l1_pre_topc(sK2) = iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_57]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_56,negated_conjecture,
% 7.45/1.49      ( v2_pre_topc(sK3) ),
% 7.45/1.49      inference(cnf_transformation,[],[f132]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_61,plain,
% 7.45/1.49      ( v2_pre_topc(sK3) = iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_56]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_55,negated_conjecture,
% 7.45/1.49      ( l1_pre_topc(sK3) ),
% 7.45/1.49      inference(cnf_transformation,[],[f133]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_62,plain,
% 7.45/1.49      ( l1_pre_topc(sK3) = iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_55]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_67,plain,
% 7.45/1.49      ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_68,plain,
% 7.45/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) = iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_47,negated_conjecture,
% 7.45/1.49      ( v5_pre_topc(sK4,sK2,sK3)
% 7.45/1.49      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
% 7.45/1.49      inference(cnf_transformation,[],[f141]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_3119,plain,
% 7.45/1.49      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.45/1.49      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_3153,plain,
% 7.45/1.49      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 7.45/1.49      | v5_pre_topc(sK5,sK2,sK3) = iProver_top ),
% 7.45/1.49      inference(light_normalisation,[status(thm)],[c_3119,c_48]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_46,negated_conjecture,
% 7.45/1.49      ( ~ v5_pre_topc(sK4,sK2,sK3)
% 7.45/1.49      | ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
% 7.45/1.49      inference(cnf_transformation,[],[f142]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_3120,plain,
% 7.45/1.49      ( v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.45/1.49      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_3154,plain,
% 7.45/1.49      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 7.45/1.49      | v5_pre_topc(sK5,sK2,sK3) != iProver_top ),
% 7.45/1.49      inference(light_normalisation,[status(thm)],[c_3120,c_48]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_41,plain,
% 7.45/1.49      ( ~ v2_pre_topc(X0)
% 7.45/1.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 7.45/1.49      | ~ l1_pre_topc(X0) ),
% 7.45/1.49      inference(cnf_transformation,[],[f125]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_3331,plain,
% 7.45/1.49      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 7.45/1.49      | ~ v2_pre_topc(sK3)
% 7.45/1.49      | ~ l1_pre_topc(sK3) ),
% 7.45/1.49      inference(instantiation,[status(thm)],[c_41]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_3332,plain,
% 7.45/1.49      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 7.45/1.49      | v2_pre_topc(sK3) != iProver_top
% 7.45/1.49      | l1_pre_topc(sK3) != iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_3331]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_39,plain,
% 7.45/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 7.45/1.49      | l1_pre_topc(g1_pre_topc(X1,X0)) ),
% 7.45/1.49      inference(cnf_transformation,[],[f123]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_3759,plain,
% 7.45/1.49      ( ~ m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
% 7.45/1.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
% 7.45/1.49      inference(instantiation,[status(thm)],[c_39]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_3760,plain,
% 7.45/1.49      ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
% 7.45/1.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_3759]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_40,plain,
% 7.45/1.49      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 7.45/1.49      | ~ l1_pre_topc(X0) ),
% 7.45/1.49      inference(cnf_transformation,[],[f124]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_4218,plain,
% 7.45/1.49      ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
% 7.45/1.49      | ~ l1_pre_topc(sK3) ),
% 7.45/1.49      inference(instantiation,[status(thm)],[c_40]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_4219,plain,
% 7.45/1.49      ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top
% 7.45/1.49      | l1_pre_topc(sK3) != iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_4218]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_42,plain,
% 7.45/1.49      ( v5_pre_topc(X0,X1,X2)
% 7.45/1.49      | ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 7.45/1.49      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.45/1.49      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 7.45/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.45/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 7.45/1.49      | ~ v2_pre_topc(X1)
% 7.45/1.49      | ~ v2_pre_topc(X2)
% 7.45/1.49      | ~ l1_pre_topc(X1)
% 7.45/1.49      | ~ l1_pre_topc(X2)
% 7.45/1.49      | ~ v1_funct_1(X0) ),
% 7.45/1.49      inference(cnf_transformation,[],[f151]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_3469,plain,
% 7.45/1.49      ( v5_pre_topc(sK5,X0,X1)
% 7.45/1.49      | ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 7.45/1.49      | ~ v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(X1))
% 7.45/1.49      | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
% 7.45/1.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.45/1.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
% 7.45/1.49      | ~ v2_pre_topc(X0)
% 7.45/1.49      | ~ v2_pre_topc(X1)
% 7.45/1.49      | ~ l1_pre_topc(X0)
% 7.45/1.49      | ~ l1_pre_topc(X1)
% 7.45/1.49      | ~ v1_funct_1(sK5) ),
% 7.45/1.49      inference(instantiation,[status(thm)],[c_42]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_4056,plain,
% 7.45/1.49      ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0)
% 7.45/1.49      | v5_pre_topc(sK5,sK2,X0)
% 7.45/1.49      | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(X0))
% 7.45/1.49      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(X0))
% 7.45/1.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(X0))))
% 7.45/1.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 7.45/1.49      | ~ v2_pre_topc(X0)
% 7.45/1.49      | ~ v2_pre_topc(sK2)
% 7.45/1.49      | ~ l1_pre_topc(X0)
% 7.45/1.49      | ~ l1_pre_topc(sK2)
% 7.45/1.49      | ~ v1_funct_1(sK5) ),
% 7.45/1.49      inference(instantiation,[status(thm)],[c_3469]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_5138,plain,
% 7.45/1.49      ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 7.45/1.49      | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 7.45/1.49      | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
% 7.45/1.49      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
% 7.45/1.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
% 7.45/1.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
% 7.45/1.49      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 7.45/1.49      | ~ v2_pre_topc(sK2)
% 7.45/1.49      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 7.45/1.49      | ~ l1_pre_topc(sK2)
% 7.45/1.49      | ~ v1_funct_1(sK5) ),
% 7.45/1.49      inference(instantiation,[status(thm)],[c_4056]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_5139,plain,
% 7.45/1.49      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 7.45/1.49      | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 7.45/1.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 7.45/1.49      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 7.45/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
% 7.45/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
% 7.45/1.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 7.45/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.45/1.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 7.45/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.45/1.49      | v1_funct_1(sK5) != iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_5138]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_44,plain,
% 7.45/1.49      ( v5_pre_topc(X0,X1,X2)
% 7.45/1.49      | ~ v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 7.45/1.49      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.45/1.49      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 7.45/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.45/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 7.45/1.49      | ~ v2_pre_topc(X1)
% 7.45/1.49      | ~ v2_pre_topc(X2)
% 7.45/1.49      | ~ l1_pre_topc(X1)
% 7.45/1.49      | ~ l1_pre_topc(X2)
% 7.45/1.49      | ~ v1_funct_1(X0) ),
% 7.45/1.49      inference(cnf_transformation,[],[f153]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_3470,plain,
% 7.45/1.49      ( v5_pre_topc(sK5,X0,X1)
% 7.45/1.49      | ~ v5_pre_topc(sK5,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 7.45/1.49      | ~ v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(X1))
% 7.45/1.49      | ~ v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
% 7.45/1.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.45/1.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
% 7.45/1.49      | ~ v2_pre_topc(X0)
% 7.45/1.49      | ~ v2_pre_topc(X1)
% 7.45/1.49      | ~ l1_pre_topc(X0)
% 7.45/1.49      | ~ l1_pre_topc(X1)
% 7.45/1.49      | ~ v1_funct_1(sK5) ),
% 7.45/1.49      inference(instantiation,[status(thm)],[c_44]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_4081,plain,
% 7.45/1.49      ( v5_pre_topc(sK5,sK2,X0)
% 7.45/1.49      | ~ v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 7.45/1.49      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(X0))
% 7.45/1.49      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
% 7.45/1.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 7.45/1.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
% 7.45/1.49      | ~ v2_pre_topc(X0)
% 7.45/1.49      | ~ v2_pre_topc(sK2)
% 7.45/1.49      | ~ l1_pre_topc(X0)
% 7.45/1.49      | ~ l1_pre_topc(sK2)
% 7.45/1.49      | ~ v1_funct_1(sK5) ),
% 7.45/1.49      inference(instantiation,[status(thm)],[c_3470]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_5185,plain,
% 7.45/1.49      ( ~ v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 7.45/1.49      | v5_pre_topc(sK5,sK2,sK3)
% 7.45/1.49      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
% 7.45/1.49      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.45/1.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
% 7.45/1.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.45/1.49      | ~ v2_pre_topc(sK3)
% 7.45/1.49      | ~ v2_pre_topc(sK2)
% 7.45/1.49      | ~ l1_pre_topc(sK3)
% 7.45/1.49      | ~ l1_pre_topc(sK2)
% 7.45/1.49      | ~ v1_funct_1(sK5) ),
% 7.45/1.49      inference(instantiation,[status(thm)],[c_4081]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_5186,plain,
% 7.45/1.49      ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 7.45/1.49      | v5_pre_topc(sK5,sK2,sK3) = iProver_top
% 7.45/1.49      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 7.45/1.49      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.45/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
% 7.45/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.45/1.49      | v2_pre_topc(sK3) != iProver_top
% 7.45/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.45/1.49      | l1_pre_topc(sK3) != iProver_top
% 7.45/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.45/1.49      | v1_funct_1(sK5) != iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_5185]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_45,plain,
% 7.45/1.49      ( ~ v5_pre_topc(X0,X1,X2)
% 7.45/1.49      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 7.45/1.49      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.45/1.49      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 7.45/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.45/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 7.45/1.49      | ~ v2_pre_topc(X1)
% 7.45/1.49      | ~ v2_pre_topc(X2)
% 7.45/1.49      | ~ l1_pre_topc(X1)
% 7.45/1.49      | ~ l1_pre_topc(X2)
% 7.45/1.49      | ~ v1_funct_1(X0) ),
% 7.45/1.49      inference(cnf_transformation,[],[f154]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_5340,plain,
% 7.45/1.49      ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 7.45/1.49      | ~ v5_pre_topc(sK5,sK2,sK3)
% 7.45/1.49      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
% 7.45/1.49      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.45/1.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
% 7.45/1.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.45/1.49      | ~ v2_pre_topc(sK3)
% 7.45/1.49      | ~ v2_pre_topc(sK2)
% 7.45/1.49      | ~ l1_pre_topc(sK3)
% 7.45/1.49      | ~ l1_pre_topc(sK2)
% 7.45/1.49      | ~ v1_funct_1(sK5) ),
% 7.45/1.49      inference(instantiation,[status(thm)],[c_45]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_5341,plain,
% 7.45/1.49      ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 7.45/1.49      | v5_pre_topc(sK5,sK2,sK3) != iProver_top
% 7.45/1.49      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 7.45/1.49      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.45/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
% 7.45/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.45/1.49      | v2_pre_topc(sK3) != iProver_top
% 7.45/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.45/1.49      | l1_pre_topc(sK3) != iProver_top
% 7.45/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.45/1.49      | v1_funct_1(sK5) != iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_5340]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_8579,plain,
% 7.45/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
% 7.45/1.49      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 7.45/1.49      | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
% 7.45/1.49      inference(global_propositional_subsumption,
% 7.45/1.49                [status(thm)],
% 7.45/1.49                [c_8386,c_59,c_60,c_61,c_62,c_66,c_67,c_68,c_3151,c_3150,
% 7.45/1.49                 c_3153,c_3154,c_3332,c_3760,c_4219,c_5139,c_5186,c_5341]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_8580,plain,
% 7.45/1.49      ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 7.45/1.49      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 7.45/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top ),
% 7.45/1.49      inference(renaming,[status(thm)],[c_8579]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_8583,plain,
% 7.45/1.49      ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 7.45/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top ),
% 7.45/1.49      inference(global_propositional_subsumption,
% 7.45/1.49                [status(thm)],
% 7.45/1.49                [c_8580,c_59,c_60,c_61,c_62,c_66,c_67,c_68,c_3151,c_3150,
% 7.45/1.49                 c_3153,c_3332,c_3760,c_4219,c_5139,c_5341]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_11741,plain,
% 7.45/1.49      ( sK5 = k1_xboole_0
% 7.45/1.49      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 7.45/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_10496,c_8583]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_16244,plain,
% 7.45/1.49      ( sK5 = k1_xboole_0
% 7.45/1.49      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_15838,c_11741]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_18356,plain,
% 7.45/1.49      ( sK5 = k1_xboole_0
% 7.45/1.49      | v1_funct_2(sK5,k1_relat_1(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_10496,c_16244]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_18512,plain,
% 7.45/1.49      ( sK5 = k1_xboole_0 ),
% 7.45/1.49      inference(global_propositional_subsumption,
% 7.45/1.49                [status(thm)],
% 7.45/1.49                [c_15832,c_15839,c_18356]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_18556,plain,
% 7.45/1.49      ( v1_funct_2(k1_xboole_0,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 7.45/1.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top ),
% 7.45/1.49      inference(demodulation,[status(thm)],[c_18512,c_8583]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_5996,plain,
% 7.45/1.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 7.45/1.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 7.45/1.49      | v1_funct_1(sK5) != iProver_top
% 7.45/1.49      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_3118,c_3107]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_6173,plain,
% 7.45/1.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 7.45/1.49      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
% 7.45/1.49      inference(global_propositional_subsumption,
% 7.45/1.49                [status(thm)],
% 7.45/1.49                [c_5996,c_66,c_67]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_6150,plain,
% 7.45/1.49      ( u1_struct_0(sK3) = X0
% 7.45/1.49      | u1_struct_0(sK2) = k1_relat_1(sK5)
% 7.45/1.49      | v1_xboole_0(X0) != iProver_top ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_6146,c_3143]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_6185,plain,
% 7.45/1.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = u1_struct_0(sK3)
% 7.45/1.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 7.45/1.49      | u1_struct_0(sK2) = k1_relat_1(sK5) ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_6173,c_6150]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_6221,plain,
% 7.45/1.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 7.45/1.49      | u1_struct_0(sK2) = k1_relat_1(sK5)
% 7.45/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) = iProver_top ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_6185,c_3118]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_3122,plain,
% 7.45/1.49      ( v5_pre_topc(X0,X1,X2) = iProver_top
% 7.45/1.49      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) != iProver_top
% 7.45/1.49      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 7.45/1.49      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 7.45/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 7.45/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 7.45/1.49      | v2_pre_topc(X1) != iProver_top
% 7.45/1.49      | v2_pre_topc(X2) != iProver_top
% 7.45/1.49      | l1_pre_topc(X1) != iProver_top
% 7.45/1.49      | l1_pre_topc(X2) != iProver_top
% 7.45/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_7880,plain,
% 7.45/1.49      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 7.45/1.49      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) = iProver_top
% 7.45/1.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 7.45/1.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 7.45/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
% 7.45/1.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 7.45/1.49      | v2_pre_topc(sK3) != iProver_top
% 7.45/1.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 7.45/1.49      | l1_pre_topc(sK3) != iProver_top
% 7.45/1.49      | v1_funct_1(sK5) != iProver_top ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_3118,c_3122]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_3318,plain,
% 7.45/1.49      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 7.45/1.49      | ~ v2_pre_topc(sK2)
% 7.45/1.49      | ~ l1_pre_topc(sK2) ),
% 7.45/1.49      inference(instantiation,[status(thm)],[c_41]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_3319,plain,
% 7.45/1.49      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 7.45/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.45/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_3318]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_3749,plain,
% 7.45/1.49      ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 7.45/1.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
% 7.45/1.49      inference(instantiation,[status(thm)],[c_39]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_3750,plain,
% 7.45/1.49      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
% 7.45/1.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_3749]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_4199,plain,
% 7.45/1.49      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 7.45/1.49      | ~ l1_pre_topc(sK2) ),
% 7.45/1.49      inference(instantiation,[status(thm)],[c_40]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_4200,plain,
% 7.45/1.49      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
% 7.45/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_4199]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_5343,plain,
% 7.45/1.49      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3)
% 7.45/1.49      | ~ v5_pre_topc(sK5,sK2,sK3)
% 7.45/1.49      | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))
% 7.45/1.49      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.45/1.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))))
% 7.45/1.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.45/1.49      | ~ v2_pre_topc(sK3)
% 7.45/1.49      | ~ v2_pre_topc(sK2)
% 7.45/1.49      | ~ l1_pre_topc(sK3)
% 7.45/1.49      | ~ l1_pre_topc(sK2)
% 7.45/1.49      | ~ v1_funct_1(sK5) ),
% 7.45/1.49      inference(instantiation,[status(thm)],[c_43]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_5344,plain,
% 7.45/1.49      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) = iProver_top
% 7.45/1.49      | v5_pre_topc(sK5,sK2,sK3) != iProver_top
% 7.45/1.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 7.45/1.49      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.45/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
% 7.45/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.45/1.49      | v2_pre_topc(sK3) != iProver_top
% 7.45/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.45/1.49      | l1_pre_topc(sK3) != iProver_top
% 7.45/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.45/1.49      | v1_funct_1(sK5) != iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_5343]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_3121,plain,
% 7.45/1.49      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 7.45/1.49      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) = iProver_top
% 7.45/1.49      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 7.45/1.49      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 7.45/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 7.45/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 7.45/1.49      | v2_pre_topc(X1) != iProver_top
% 7.45/1.49      | v2_pre_topc(X2) != iProver_top
% 7.45/1.49      | l1_pre_topc(X1) != iProver_top
% 7.45/1.49      | l1_pre_topc(X2) != iProver_top
% 7.45/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_6660,plain,
% 7.45/1.49      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 7.45/1.49      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) != iProver_top
% 7.45/1.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 7.45/1.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 7.45/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
% 7.45/1.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 7.45/1.49      | v2_pre_topc(sK3) != iProver_top
% 7.45/1.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 7.45/1.49      | l1_pre_topc(sK3) != iProver_top
% 7.45/1.49      | v1_funct_1(sK5) != iProver_top ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_3118,c_3121]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_5129,plain,
% 7.45/1.49      ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3)
% 7.45/1.49      | v5_pre_topc(sK5,sK2,sK3)
% 7.45/1.49      | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))
% 7.45/1.49      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.45/1.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))))
% 7.45/1.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.45/1.49      | ~ v2_pre_topc(sK3)
% 7.45/1.49      | ~ v2_pre_topc(sK2)
% 7.45/1.49      | ~ l1_pre_topc(sK3)
% 7.45/1.49      | ~ l1_pre_topc(sK2)
% 7.45/1.49      | ~ v1_funct_1(sK5) ),
% 7.45/1.49      inference(instantiation,[status(thm)],[c_4056]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_5130,plain,
% 7.45/1.49      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) != iProver_top
% 7.45/1.49      | v5_pre_topc(sK5,sK2,sK3) = iProver_top
% 7.45/1.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 7.45/1.49      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.45/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
% 7.45/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.45/1.49      | v2_pre_topc(sK3) != iProver_top
% 7.45/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.45/1.49      | l1_pre_topc(sK3) != iProver_top
% 7.45/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.45/1.49      | v1_funct_1(sK5) != iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_5129]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_6803,plain,
% 7.45/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
% 7.45/1.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 7.45/1.49      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) != iProver_top ),
% 7.45/1.49      inference(global_propositional_subsumption,
% 7.45/1.49                [status(thm)],
% 7.45/1.49                [c_6660,c_59,c_60,c_61,c_62,c_66,c_67,c_3151,c_3150,c_3154,
% 7.45/1.49                 c_3319,c_3750,c_4200,c_5130]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_6804,plain,
% 7.45/1.49      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) != iProver_top
% 7.45/1.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 7.45/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top ),
% 7.45/1.49      inference(renaming,[status(thm)],[c_6803]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_8091,plain,
% 7.45/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
% 7.45/1.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top ),
% 7.45/1.49      inference(global_propositional_subsumption,
% 7.45/1.49                [status(thm)],
% 7.45/1.49                [c_7880,c_59,c_60,c_61,c_62,c_66,c_67,c_3151,c_3150,c_3153,
% 7.45/1.49                 c_3319,c_3750,c_4200,c_5344,c_6804]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_8092,plain,
% 7.45/1.49      ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 7.45/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top ),
% 7.45/1.49      inference(renaming,[status(thm)],[c_8091]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_8096,plain,
% 7.45/1.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 7.45/1.49      | u1_struct_0(sK2) = k1_relat_1(sK5)
% 7.45/1.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_6221,c_8092]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_6222,plain,
% 7.45/1.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 7.45/1.49      | u1_struct_0(sK2) = k1_relat_1(sK5)
% 7.45/1.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) = iProver_top ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_6185,c_3117]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_9826,plain,
% 7.45/1.49      ( u1_struct_0(sK2) = k1_relat_1(sK5)
% 7.45/1.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5) ),
% 7.45/1.49      inference(global_propositional_subsumption,[status(thm)],[c_8096,c_6222]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_9827,plain,
% 7.45/1.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 7.45/1.49      | u1_struct_0(sK2) = k1_relat_1(sK5) ),
% 7.45/1.49      inference(renaming,[status(thm)],[c_9826]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_9,plain,
% 7.45/1.49      ( m1_subset_1(X0,X1) | ~ v1_xboole_0(X1) | ~ v1_xboole_0(X0) ),
% 7.45/1.49      inference(cnf_transformation,[],[f96]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_3142,plain,
% 7.45/1.49      ( m1_subset_1(X0,X1) = iProver_top
% 7.45/1.49      | v1_xboole_0(X1) != iProver_top
% 7.45/1.49      | v1_xboole_0(X0) != iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_8095,plain,
% 7.45/1.49      ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 7.45/1.49      | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
% 7.45/1.49      | v1_xboole_0(sK5) != iProver_top ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_3142,c_8092]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_9839,plain,
% 7.45/1.49      ( u1_struct_0(sK2) = k1_relat_1(sK5)
% 7.45/1.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 7.45/1.49      | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.45/1.49      | v1_xboole_0(sK5) != iProver_top ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_9827,c_8095]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_11447,plain,
% 7.45/1.49      ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.45/1.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 7.45/1.49      | u1_struct_0(sK2) = k1_relat_1(sK5) ),
% 7.45/1.49      inference(global_propositional_subsumption,[status(thm)],[c_9839,c_8054]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_11448,plain,
% 7.45/1.49      ( u1_struct_0(sK2) = k1_relat_1(sK5)
% 7.45/1.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 7.45/1.49      | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),u1_struct_0(sK3)))) != iProver_top ),
% 7.45/1.49      inference(renaming,[status(thm)],[c_11447]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_11451,plain,
% 7.45/1.49      ( u1_struct_0(sK2) = k1_relat_1(sK5)
% 7.45/1.49      | v1_funct_2(sK5,k1_relat_1(sK5),u1_struct_0(sK3)) != iProver_top
% 7.45/1.49      | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),u1_struct_0(sK3)))) != iProver_top ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_9827,c_11448]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_18524,plain,
% 7.45/1.49      ( u1_struct_0(sK2) = k1_relat_1(k1_xboole_0)
% 7.45/1.49      | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK3)) != iProver_top
% 7.45/1.49      | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(sK3)))) != iProver_top ),
% 7.45/1.49      inference(demodulation,[status(thm)],[c_18512,c_11451]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_18626,plain,
% 7.45/1.49      ( u1_struct_0(sK2) = k1_xboole_0
% 7.45/1.49      | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK3)) != iProver_top
% 7.45/1.49      | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK3)))) != iProver_top ),
% 7.45/1.49      inference(light_normalisation,[status(thm)],[c_18524,c_10497]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_18627,plain,
% 7.45/1.49      ( u1_struct_0(sK2) = k1_xboole_0
% 7.45/1.49      | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK3)) != iProver_top
% 7.45/1.49      | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.45/1.49      inference(demodulation,[status(thm)],[c_18626,c_7]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_9842,plain,
% 7.45/1.49      ( u1_struct_0(sK2) = k1_relat_1(sK5)
% 7.45/1.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 7.45/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),u1_struct_0(sK3)))) != iProver_top ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_9827,c_8092]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_10225,plain,
% 7.45/1.49      ( u1_struct_0(sK2) = k1_relat_1(sK5)
% 7.45/1.49      | v1_funct_2(sK5,k1_relat_1(sK5),u1_struct_0(sK3)) != iProver_top
% 7.45/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),u1_struct_0(sK3)))) != iProver_top ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_9827,c_9842]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_18527,plain,
% 7.45/1.49      ( u1_struct_0(sK2) = k1_relat_1(k1_xboole_0)
% 7.45/1.49      | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK3)) != iProver_top
% 7.45/1.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(sK3)))) != iProver_top ),
% 7.45/1.49      inference(demodulation,[status(thm)],[c_18512,c_10225]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_18621,plain,
% 7.45/1.49      ( u1_struct_0(sK2) = k1_xboole_0
% 7.45/1.49      | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK3)) != iProver_top
% 7.45/1.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK3)))) != iProver_top ),
% 7.45/1.49      inference(light_normalisation,[status(thm)],[c_18527,c_10497]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_18622,plain,
% 7.45/1.49      ( u1_struct_0(sK2) = k1_xboole_0
% 7.45/1.49      | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK3)) != iProver_top
% 7.45/1.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.45/1.49      inference(demodulation,[status(thm)],[c_18621,c_7]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_20098,plain,
% 7.45/1.49      ( v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK3)) != iProver_top
% 7.45/1.49      | u1_struct_0(sK2) = k1_xboole_0 ),
% 7.45/1.49      inference(global_propositional_subsumption,
% 7.45/1.49                [status(thm)],
% 7.45/1.49                [c_18627,c_153,c_18622]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_20099,plain,
% 7.45/1.49      ( u1_struct_0(sK2) = k1_xboole_0
% 7.45/1.49      | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK3)) != iProver_top ),
% 7.45/1.49      inference(renaming,[status(thm)],[c_20098]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_20102,plain,
% 7.45/1.49      ( u1_struct_0(sK2) = k1_xboole_0 ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_17857,c_20099]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_20164,plain,
% 7.45/1.49      ( v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 7.45/1.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top ),
% 7.45/1.49      inference(light_normalisation,[status(thm)],[c_18556,c_20102]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_20165,plain,
% 7.45/1.49      ( v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 7.45/1.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.45/1.49      inference(demodulation,[status(thm)],[c_20164,c_7]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_20167,plain,
% 7.45/1.49      ( v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top ),
% 7.45/1.49      inference(global_propositional_subsumption,[status(thm)],[c_20165,c_153]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_20171,plain,
% 7.45/1.49      ( $false ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_17857,c_20167]) ).
% 7.45/1.49  
% 7.45/1.49  
% 7.45/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.45/1.49  
% 7.45/1.49  ------                               Statistics
% 7.45/1.49  
% 7.45/1.49  ------ General
% 7.45/1.49  
% 7.45/1.49  abstr_ref_over_cycles:                  0
% 7.45/1.49  abstr_ref_under_cycles:                 0
% 7.45/1.49  gc_basic_clause_elim:                   0
% 7.45/1.49  forced_gc_time:                         0
% 7.45/1.49  parsing_time:                           0.008
% 7.45/1.49  unif_index_cands_time:                  0.
% 7.45/1.49  unif_index_add_time:                    0.
% 7.45/1.49  orderings_time:                         0.
% 7.45/1.49  out_proof_time:                         0.022
% 7.45/1.49  total_time:                             0.559
% 7.45/1.49  num_of_symbols:                         58
% 7.45/1.49  num_of_terms:                           15106
% 7.45/1.49  
% 7.45/1.49  ------ Preprocessing
% 7.45/1.49  
% 7.45/1.49  num_of_splits:                          0
% 7.45/1.49  num_of_split_atoms:                     0
% 7.45/1.49  num_of_reused_defs:                     0
% 7.45/1.49  num_eq_ax_congr_red:                    29
% 7.45/1.49  num_of_sem_filtered_clauses:            1
% 7.45/1.49  num_of_subtypes:                        0
% 7.45/1.49  monotx_restored_types:                  0
% 7.45/1.49  sat_num_of_epr_types:                   0
% 7.45/1.49  sat_num_of_non_cyclic_types:            0
% 7.45/1.49  sat_guarded_non_collapsed_types:        0
% 7.45/1.49  num_pure_diseq_elim:                    0
% 7.45/1.49  simp_replaced_by:                       0
% 7.45/1.49  res_preprocessed:                       237
% 7.45/1.49  prep_upred:                             0
% 7.45/1.49  prep_unflattend:                        34
% 7.45/1.49  smt_new_axioms:                         0
% 7.45/1.49  pred_elim_cands:                        8
% 7.45/1.49  pred_elim:                              4
% 7.45/1.49  pred_elim_cl:                           6
% 7.45/1.49  pred_elim_cycles:                       7
% 7.45/1.49  merged_defs:                            10
% 7.45/1.49  merged_defs_ncl:                        0
% 7.45/1.49  bin_hyper_res:                          10
% 7.45/1.49  prep_cycles:                            4
% 7.45/1.49  pred_elim_time:                         0.017
% 7.45/1.49  splitting_time:                         0.
% 7.45/1.49  sem_filter_time:                        0.
% 7.45/1.49  monotx_time:                            0.
% 7.45/1.49  subtype_inf_time:                       0.
% 7.45/1.49  
% 7.45/1.49  ------ Problem properties
% 7.45/1.49  
% 7.45/1.49  clauses:                                50
% 7.45/1.49  conjectures:                            13
% 7.45/1.49  epr:                                    14
% 7.45/1.49  horn:                                   39
% 7.45/1.49  ground:                                 13
% 7.45/1.49  unary:                                  17
% 7.45/1.49  binary:                                 11
% 7.45/1.49  lits:                                   145
% 7.45/1.49  lits_eq:                                21
% 7.45/1.49  fd_pure:                                0
% 7.45/1.49  fd_pseudo:                              0
% 7.45/1.49  fd_cond:                                4
% 7.45/1.49  fd_pseudo_cond:                         4
% 7.45/1.49  ac_symbols:                             0
% 7.45/1.49  
% 7.45/1.49  ------ Propositional Solver
% 7.45/1.49  
% 7.45/1.49  prop_solver_calls:                      34
% 7.45/1.49  prop_fast_solver_calls:                 2302
% 7.45/1.49  smt_solver_calls:                       0
% 7.45/1.49  smt_fast_solver_calls:                  0
% 7.45/1.49  prop_num_of_clauses:                    7239
% 7.45/1.49  prop_preprocess_simplified:             16941
% 7.45/1.49  prop_fo_subsumed:                       84
% 7.45/1.49  prop_solver_time:                       0.
% 7.45/1.49  smt_solver_time:                        0.
% 7.45/1.49  smt_fast_solver_time:                   0.
% 7.45/1.49  prop_fast_solver_time:                  0.
% 7.45/1.49  prop_unsat_core_time:                   0.
% 7.45/1.49  
% 7.45/1.49  ------ QBF
% 7.45/1.49  
% 7.45/1.49  qbf_q_res:                              0
% 7.45/1.49  qbf_num_tautologies:                    0
% 7.45/1.49  qbf_prep_cycles:                        0
% 7.45/1.49  
% 7.45/1.49  ------ BMC1
% 7.45/1.49  
% 7.45/1.49  bmc1_current_bound:                     -1
% 7.45/1.49  bmc1_last_solved_bound:                 -1
% 7.45/1.49  bmc1_unsat_core_size:                   -1
% 7.45/1.49  bmc1_unsat_core_parents_size:           -1
% 7.45/1.49  bmc1_merge_next_fun:                    0
% 7.45/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.45/1.49  
% 7.45/1.49  ------ Instantiation
% 7.45/1.49  
% 7.45/1.49  inst_num_of_clauses:                    2139
% 7.45/1.49  inst_num_in_passive:                    1516
% 7.45/1.49  inst_num_in_active:                     600
% 7.45/1.49  inst_num_in_unprocessed:                23
% 7.45/1.49  inst_num_of_loops:                      1020
% 7.45/1.49  inst_num_of_learning_restarts:          0
% 7.45/1.49  inst_num_moves_active_passive:          415
% 7.45/1.49  inst_lit_activity:                      0
% 7.45/1.49  inst_lit_activity_moves:                1
% 7.45/1.49  inst_num_tautologies:                   0
% 7.45/1.49  inst_num_prop_implied:                  0
% 7.45/1.49  inst_num_existing_simplified:           0
% 7.45/1.49  inst_num_eq_res_simplified:             0
% 7.45/1.49  inst_num_child_elim:                    0
% 7.45/1.49  inst_num_of_dismatching_blockings:      601
% 7.45/1.49  inst_num_of_non_proper_insts:           2236
% 7.45/1.49  inst_num_of_duplicates:                 0
% 7.45/1.49  inst_inst_num_from_inst_to_res:         0
% 7.45/1.49  inst_dismatching_checking_time:         0.
% 7.45/1.49  
% 7.45/1.49  ------ Resolution
% 7.45/1.49  
% 7.45/1.49  res_num_of_clauses:                     0
% 7.45/1.49  res_num_in_passive:                     0
% 7.45/1.49  res_num_in_active:                      0
% 7.45/1.49  res_num_of_loops:                       241
% 7.45/1.49  res_forward_subset_subsumed:            115
% 7.45/1.49  res_backward_subset_subsumed:           0
% 7.45/1.49  res_forward_subsumed:                   0
% 7.45/1.49  res_backward_subsumed:                  0
% 7.45/1.49  res_forward_subsumption_resolution:     0
% 7.45/1.49  res_backward_subsumption_resolution:    0
% 7.45/1.49  res_clause_to_clause_subsumption:       1372
% 7.45/1.49  res_orphan_elimination:                 0
% 7.45/1.49  res_tautology_del:                      193
% 7.45/1.49  res_num_eq_res_simplified:              0
% 7.45/1.49  res_num_sel_changes:                    0
% 7.45/1.49  res_moves_from_active_to_pass:          0
% 7.45/1.49  
% 7.45/1.49  ------ Superposition
% 7.45/1.49  
% 7.45/1.49  sup_time_total:                         0.
% 7.45/1.49  sup_time_generating:                    0.
% 7.45/1.49  sup_time_sim_full:                      0.
% 7.45/1.49  sup_time_sim_immed:                     0.
% 7.45/1.49  
% 7.45/1.49  sup_num_of_clauses:                     332
% 7.45/1.49  sup_num_in_active:                      89
% 7.45/1.49  sup_num_in_passive:                     243
% 7.45/1.49  sup_num_of_loops:                       203
% 7.45/1.49  sup_fw_superposition:                   314
% 7.45/1.49  sup_bw_superposition:                   395
% 7.45/1.49  sup_immediate_simplified:               185
% 7.45/1.49  sup_given_eliminated:                   0
% 7.45/1.49  comparisons_done:                       0
% 7.45/1.49  comparisons_avoided:                    39
% 7.45/1.49  
% 7.45/1.49  ------ Simplifications
% 7.45/1.49  
% 7.45/1.49  
% 7.45/1.49  sim_fw_subset_subsumed:                 97
% 7.45/1.49  sim_bw_subset_subsumed:                 110
% 7.45/1.49  sim_fw_subsumed:                        46
% 7.45/1.49  sim_bw_subsumed:                        9
% 7.45/1.49  sim_fw_subsumption_res:                 0
% 7.45/1.49  sim_bw_subsumption_res:                 0
% 7.45/1.49  sim_tautology_del:                      21
% 7.45/1.49  sim_eq_tautology_del:                   41
% 7.45/1.49  sim_eq_res_simp:                        1
% 7.45/1.49  sim_fw_demodulated:                     25
% 7.45/1.49  sim_bw_demodulated:                     80
% 7.45/1.49  sim_light_normalised:                   66
% 7.45/1.49  sim_joinable_taut:                      0
% 7.45/1.49  sim_joinable_simp:                      0
% 7.45/1.49  sim_ac_normalised:                      0
% 7.45/1.49  sim_smt_subsumption:                    0
% 7.45/1.49  
%------------------------------------------------------------------------------
