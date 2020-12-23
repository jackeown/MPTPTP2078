%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:16:54 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :  154 (2041 expanded)
%              Number of clauses        :   95 ( 663 expanded)
%              Number of leaves         :   17 ( 551 expanded)
%              Depth                    :   27
%              Number of atoms          :  458 (11441 expanded)
%              Number of equality atoms :  188 (4563 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f25])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f13,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( k1_xboole_0 = k2_struct_0(X1)
                 => k1_xboole_0 = k2_struct_0(X0) )
               => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) = k2_struct_0(X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( k1_xboole_0 = k2_struct_0(X1)
                   => k1_xboole_0 = k2_struct_0(X0) )
                 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) = k2_struct_0(X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0)
              & ( k1_xboole_0 = k2_struct_0(X0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0)
              & ( k1_xboole_0 = k2_struct_0(X0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0)
          & ( k1_xboole_0 = k2_struct_0(X0)
            | k1_xboole_0 != k2_struct_0(X1) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,k2_struct_0(X1)) != k2_struct_0(X0)
        & ( k1_xboole_0 = k2_struct_0(X0)
          | k1_xboole_0 != k2_struct_0(X1) )
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0)
              & ( k1_xboole_0 = k2_struct_0(X0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
     => ( ? [X2] :
            ( k8_relset_1(u1_struct_0(X0),u1_struct_0(sK2),X2,k2_struct_0(sK2)) != k2_struct_0(X0)
            & ( k1_xboole_0 = k2_struct_0(X0)
              | k1_xboole_0 != k2_struct_0(sK2) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK2))
            & v1_funct_1(X2) )
        & l1_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0)
                & ( k1_xboole_0 = k2_struct_0(X0)
                  | k1_xboole_0 != k2_struct_0(X1) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(sK1)
              & ( k1_xboole_0 = k2_struct_0(sK1)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_struct_0(sK2)) != k2_struct_0(sK1)
    & ( k1_xboole_0 = k2_struct_0(sK1)
      | k1_xboole_0 != k2_struct_0(sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    & v1_funct_1(sK3)
    & l1_struct_0(sK2)
    & l1_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f31,f39,f38,f37])).

fof(f61,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f40])).

fof(f60,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f62,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f40])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f57,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f58,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f59,plain,(
    l1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f64,plain,(
    k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_struct_0(sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f63,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | k1_xboole_0 != k2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f9,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5,X6] :
                  ( ( r2_hidden(X6,X1)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X3,X4)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f34])).

fof(f52,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_7,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_15,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_20,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_326,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | u1_struct_0(sK2) != X2
    | u1_struct_0(sK1) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_20])).

cnf(c_327,plain,
    ( v1_partfun1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_326])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_329,plain,
    ( v1_partfun1(sK3,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_327,c_21,c_19])).

cnf(c_343,plain,
    ( v1_partfun1(sK3,u1_struct_0(sK1))
    | u1_struct_0(sK2) != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_329])).

cnf(c_344,plain,
    ( v1_partfun1(sK3,u1_struct_0(sK1))
    | k1_xboole_0 = u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_343])).

cnf(c_508,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK1) != X1
    | k1_relat_1(X0) = X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_344])).

cnf(c_509,plain,
    ( ~ v4_relat_1(sK3,u1_struct_0(sK1))
    | ~ v1_relat_1(sK3)
    | u1_struct_0(sK2) = k1_xboole_0
    | k1_relat_1(sK3) = u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_508])).

cnf(c_668,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(sK3)
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK1) != X1
    | u1_struct_0(sK1) = k1_relat_1(sK3)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_509])).

cnf(c_669,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0)))
    | ~ v1_relat_1(sK3)
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK1) = k1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_668])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_681,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0)))
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK1) = k1_relat_1(sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_669,c_6])).

cnf(c_855,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0_52)))
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK1) = k1_relat_1(sK3) ),
    inference(subtyping,[status(esa)],[c_681])).

cnf(c_866,plain,
    ( sP0_iProver_split
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK1) = k1_relat_1(sK3) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_855])).

cnf(c_1102,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK1) = k1_relat_1(sK3)
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_866])).

cnf(c_16,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_23,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_302,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_23])).

cnf(c_303,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_302])).

cnf(c_857,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_303])).

cnf(c_22,negated_conjecture,
    ( l1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_297,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_22])).

cnf(c_298,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_297])).

cnf(c_858,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_298])).

cnf(c_1133,plain,
    ( k2_struct_0(sK2) = k1_xboole_0
    | k2_struct_0(sK1) = k1_relat_1(sK3)
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_1102,c_857,c_858])).

cnf(c_28,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_865,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0_52)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_855])).

cnf(c_1220,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ sP0_iProver_split ),
    inference(instantiation,[status(thm)],[c_865])).

cnf(c_1221,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1220])).

cnf(c_859,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1100,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_859])).

cnf(c_1120,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1100,c_857,c_858])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_863,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
    | k8_relset_1(X1_52,X2_52,X0_52,X2_52) = k1_relset_1(X1_52,X2_52,X0_52) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1098,plain,
    ( k8_relset_1(X0_52,X1_52,X2_52,X1_52) = k1_relset_1(X0_52,X1_52,X2_52)
    | m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_863])).

cnf(c_1403,plain,
    ( k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,k2_struct_0(sK2)) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) ),
    inference(superposition,[status(thm)],[c_1120,c_1098])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_864,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
    | k1_relset_1(X1_52,X2_52,X0_52) = k1_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1097,plain,
    ( k1_relset_1(X0_52,X1_52,X2_52) = k1_relat_1(X2_52)
    | m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_864])).

cnf(c_1399,plain,
    ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1120,c_1097])).

cnf(c_1529,plain,
    ( k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,k2_struct_0(sK2)) = k1_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_1403,c_1399])).

cnf(c_17,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_struct_0(sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_861,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_struct_0(sK2)) != k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1123,plain,
    ( k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,k2_struct_0(sK2)) != k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_861,c_857,c_858])).

cnf(c_1531,plain,
    ( k2_struct_0(sK1) != k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_1529,c_1123])).

cnf(c_1562,plain,
    ( k2_struct_0(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1133,c_28,c_1221,c_1531])).

cnf(c_1568,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1562,c_1120])).

cnf(c_18,negated_conjecture,
    ( k1_xboole_0 != k2_struct_0(sK2)
    | k1_xboole_0 = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_860,negated_conjecture,
    ( k1_xboole_0 != k2_struct_0(sK2)
    | k1_xboole_0 = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1570,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1562,c_860])).

cnf(c_1571,plain,
    ( k2_struct_0(sK1) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_1570])).

cnf(c_1576,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1568,c_1571])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_176,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_5,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_392,plain,
    ( ~ v4_relat_1(X0,X1)
    | m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_relat_1(X0)
    | X1 != X3
    | k1_relat_1(X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_176,c_5])).

cnf(c_393,plain,
    ( ~ v4_relat_1(X0,X1)
    | m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(X1))
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_392])).

cnf(c_614,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(X1))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_7,c_393])).

cnf(c_618,plain,
    ( m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_614,c_6])).

cnf(c_619,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(X1)) ),
    inference(renaming,[status(thm)],[c_618])).

cnf(c_856,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
    | m1_subset_1(k1_relat_1(X0_52),k1_zfmisc_1(X1_52)) ),
    inference(subtyping,[status(esa)],[c_619])).

cnf(c_1101,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52))) != iProver_top
    | m1_subset_1(k1_relat_1(X0_52),k1_zfmisc_1(X1_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_856])).

cnf(c_1920,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1576,c_1101])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_11,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_309,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | X2 != X0
    | sK0(X2) != X3
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_11])).

cnf(c_310,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_309])).

cnf(c_353,plain,
    ( v1_partfun1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | u1_struct_0(sK2) != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_310,c_329])).

cnf(c_354,plain,
    ( v1_partfun1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_353])).

cnf(c_487,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_relat_1(X0)
    | u1_struct_0(sK1) != X1
    | k1_relat_1(X0) = X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_354])).

cnf(c_488,plain,
    ( ~ v4_relat_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) = u1_struct_0(sK1)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_487])).

cnf(c_688,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_relat_1(sK3)
    | u1_struct_0(sK1) != X1
    | u1_struct_0(sK1) = k1_relat_1(sK3)
    | sK3 != X0
    | k1_xboole_0 = X3 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_488])).

cnf(c_689,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X1)))
    | ~ v1_relat_1(sK3)
    | u1_struct_0(sK1) = k1_relat_1(sK3)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_688])).

cnf(c_703,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X1)))
    | u1_struct_0(sK1) = k1_relat_1(sK3)
    | k1_xboole_0 = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_689,c_6])).

cnf(c_854,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X1_52)))
    | u1_struct_0(sK1) = k1_relat_1(sK3)
    | k1_xboole_0 = X0_52 ),
    inference(subtyping,[status(esa)],[c_703])).

cnf(c_867,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_xboole_0 = X0_52
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_854])).

cnf(c_1105,plain,
    ( k1_xboole_0 = X0_52
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_867])).

cnf(c_1158,plain,
    ( k1_xboole_0 = X0_52
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1105,c_858])).

cnf(c_1567,plain,
    ( k1_xboole_0 = X0_52
    | m1_subset_1(X0_52,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_1562,c_1158])).

cnf(c_868,plain,
    ( sP1_iProver_split
    | sP0_iProver_split
    | u1_struct_0(sK1) = k1_relat_1(sK3) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_854])).

cnf(c_1104,plain,
    ( u1_struct_0(sK1) = k1_relat_1(sK3)
    | sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_868])).

cnf(c_1126,plain,
    ( k2_struct_0(sK1) = k1_relat_1(sK3)
    | sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_1104,c_857])).

cnf(c_1361,plain,
    ( sP1_iProver_split = iProver_top
    | k2_struct_0(sK1) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1126,c_28,c_1221])).

cnf(c_1362,plain,
    ( k2_struct_0(sK1) = k1_relat_1(sK3)
    | sP1_iProver_split = iProver_top ),
    inference(renaming,[status(thm)],[c_1361])).

cnf(c_2037,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | k1_xboole_0 = X0_52 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1567,c_1362,c_1531])).

cnf(c_2038,plain,
    ( k1_xboole_0 = X0_52
    | m1_subset_1(X0_52,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2037])).

cnf(c_2098,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1920,c_2038])).

cnf(c_1621,plain,
    ( k1_relat_1(sK3) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1571,c_1531])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2098,c_1621])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:25:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.80/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.02  
% 1.80/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.80/1.02  
% 1.80/1.02  ------  iProver source info
% 1.80/1.02  
% 1.80/1.02  git: date: 2020-06-30 10:37:57 +0100
% 1.80/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.80/1.02  git: non_committed_changes: false
% 1.80/1.02  git: last_make_outside_of_git: false
% 1.80/1.02  
% 1.80/1.02  ------ 
% 1.80/1.02  
% 1.80/1.02  ------ Input Options
% 1.80/1.02  
% 1.80/1.02  --out_options                           all
% 1.80/1.02  --tptp_safe_out                         true
% 1.80/1.02  --problem_path                          ""
% 1.80/1.02  --include_path                          ""
% 1.80/1.02  --clausifier                            res/vclausify_rel
% 1.80/1.02  --clausifier_options                    --mode clausify
% 1.80/1.02  --stdin                                 false
% 1.80/1.02  --stats_out                             all
% 1.80/1.02  
% 1.80/1.02  ------ General Options
% 1.80/1.02  
% 1.80/1.02  --fof                                   false
% 1.80/1.02  --time_out_real                         305.
% 1.80/1.02  --time_out_virtual                      -1.
% 1.80/1.02  --symbol_type_check                     false
% 1.80/1.02  --clausify_out                          false
% 1.80/1.02  --sig_cnt_out                           false
% 1.80/1.02  --trig_cnt_out                          false
% 1.80/1.02  --trig_cnt_out_tolerance                1.
% 1.80/1.02  --trig_cnt_out_sk_spl                   false
% 1.80/1.02  --abstr_cl_out                          false
% 1.80/1.02  
% 1.80/1.02  ------ Global Options
% 1.80/1.02  
% 1.80/1.02  --schedule                              default
% 1.80/1.02  --add_important_lit                     false
% 1.80/1.02  --prop_solver_per_cl                    1000
% 1.80/1.02  --min_unsat_core                        false
% 1.80/1.02  --soft_assumptions                      false
% 1.80/1.02  --soft_lemma_size                       3
% 1.80/1.02  --prop_impl_unit_size                   0
% 1.80/1.02  --prop_impl_unit                        []
% 1.80/1.02  --share_sel_clauses                     true
% 1.80/1.02  --reset_solvers                         false
% 1.80/1.02  --bc_imp_inh                            [conj_cone]
% 1.80/1.02  --conj_cone_tolerance                   3.
% 1.80/1.02  --extra_neg_conj                        none
% 1.80/1.02  --large_theory_mode                     true
% 1.80/1.02  --prolific_symb_bound                   200
% 1.80/1.02  --lt_threshold                          2000
% 1.80/1.02  --clause_weak_htbl                      true
% 1.80/1.02  --gc_record_bc_elim                     false
% 1.80/1.02  
% 1.80/1.02  ------ Preprocessing Options
% 1.80/1.02  
% 1.80/1.02  --preprocessing_flag                    true
% 1.80/1.02  --time_out_prep_mult                    0.1
% 1.80/1.02  --splitting_mode                        input
% 1.80/1.02  --splitting_grd                         true
% 1.80/1.02  --splitting_cvd                         false
% 1.80/1.02  --splitting_cvd_svl                     false
% 1.80/1.02  --splitting_nvd                         32
% 1.80/1.02  --sub_typing                            true
% 1.80/1.02  --prep_gs_sim                           true
% 1.80/1.02  --prep_unflatten                        true
% 1.80/1.02  --prep_res_sim                          true
% 1.80/1.02  --prep_upred                            true
% 1.80/1.02  --prep_sem_filter                       exhaustive
% 1.80/1.02  --prep_sem_filter_out                   false
% 1.80/1.02  --pred_elim                             true
% 1.80/1.02  --res_sim_input                         true
% 1.80/1.02  --eq_ax_congr_red                       true
% 1.80/1.02  --pure_diseq_elim                       true
% 1.80/1.02  --brand_transform                       false
% 1.80/1.02  --non_eq_to_eq                          false
% 1.80/1.02  --prep_def_merge                        true
% 1.80/1.02  --prep_def_merge_prop_impl              false
% 1.80/1.02  --prep_def_merge_mbd                    true
% 1.80/1.02  --prep_def_merge_tr_red                 false
% 1.80/1.02  --prep_def_merge_tr_cl                  false
% 1.80/1.02  --smt_preprocessing                     true
% 1.80/1.02  --smt_ac_axioms                         fast
% 1.80/1.02  --preprocessed_out                      false
% 1.80/1.02  --preprocessed_stats                    false
% 1.80/1.02  
% 1.80/1.02  ------ Abstraction refinement Options
% 1.80/1.02  
% 1.80/1.02  --abstr_ref                             []
% 1.80/1.02  --abstr_ref_prep                        false
% 1.80/1.02  --abstr_ref_until_sat                   false
% 1.80/1.02  --abstr_ref_sig_restrict                funpre
% 1.80/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.80/1.02  --abstr_ref_under                       []
% 1.80/1.02  
% 1.80/1.02  ------ SAT Options
% 1.80/1.02  
% 1.80/1.02  --sat_mode                              false
% 1.80/1.02  --sat_fm_restart_options                ""
% 1.80/1.02  --sat_gr_def                            false
% 1.80/1.02  --sat_epr_types                         true
% 1.80/1.02  --sat_non_cyclic_types                  false
% 1.80/1.02  --sat_finite_models                     false
% 1.80/1.02  --sat_fm_lemmas                         false
% 1.80/1.02  --sat_fm_prep                           false
% 1.80/1.02  --sat_fm_uc_incr                        true
% 1.80/1.02  --sat_out_model                         small
% 1.80/1.02  --sat_out_clauses                       false
% 1.80/1.02  
% 1.80/1.02  ------ QBF Options
% 1.80/1.02  
% 1.80/1.02  --qbf_mode                              false
% 1.80/1.02  --qbf_elim_univ                         false
% 1.80/1.02  --qbf_dom_inst                          none
% 1.80/1.02  --qbf_dom_pre_inst                      false
% 1.80/1.02  --qbf_sk_in                             false
% 1.80/1.02  --qbf_pred_elim                         true
% 1.80/1.02  --qbf_split                             512
% 1.80/1.02  
% 1.80/1.02  ------ BMC1 Options
% 1.80/1.02  
% 1.80/1.02  --bmc1_incremental                      false
% 1.80/1.02  --bmc1_axioms                           reachable_all
% 1.80/1.02  --bmc1_min_bound                        0
% 1.80/1.02  --bmc1_max_bound                        -1
% 1.80/1.02  --bmc1_max_bound_default                -1
% 1.80/1.02  --bmc1_symbol_reachability              true
% 1.80/1.02  --bmc1_property_lemmas                  false
% 1.80/1.02  --bmc1_k_induction                      false
% 1.80/1.02  --bmc1_non_equiv_states                 false
% 1.80/1.02  --bmc1_deadlock                         false
% 1.80/1.02  --bmc1_ucm                              false
% 1.80/1.02  --bmc1_add_unsat_core                   none
% 1.80/1.02  --bmc1_unsat_core_children              false
% 1.80/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.80/1.02  --bmc1_out_stat                         full
% 1.80/1.02  --bmc1_ground_init                      false
% 1.80/1.02  --bmc1_pre_inst_next_state              false
% 1.80/1.02  --bmc1_pre_inst_state                   false
% 1.80/1.02  --bmc1_pre_inst_reach_state             false
% 1.80/1.02  --bmc1_out_unsat_core                   false
% 1.80/1.02  --bmc1_aig_witness_out                  false
% 1.80/1.02  --bmc1_verbose                          false
% 1.80/1.02  --bmc1_dump_clauses_tptp                false
% 1.80/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.80/1.02  --bmc1_dump_file                        -
% 1.80/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.80/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.80/1.02  --bmc1_ucm_extend_mode                  1
% 1.80/1.02  --bmc1_ucm_init_mode                    2
% 1.80/1.02  --bmc1_ucm_cone_mode                    none
% 1.80/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.80/1.02  --bmc1_ucm_relax_model                  4
% 1.80/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.80/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.80/1.02  --bmc1_ucm_layered_model                none
% 1.80/1.02  --bmc1_ucm_max_lemma_size               10
% 1.80/1.02  
% 1.80/1.02  ------ AIG Options
% 1.80/1.02  
% 1.80/1.02  --aig_mode                              false
% 1.80/1.02  
% 1.80/1.02  ------ Instantiation Options
% 1.80/1.02  
% 1.80/1.02  --instantiation_flag                    true
% 1.80/1.02  --inst_sos_flag                         false
% 1.80/1.02  --inst_sos_phase                        true
% 1.80/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.80/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.80/1.02  --inst_lit_sel_side                     num_symb
% 1.80/1.02  --inst_solver_per_active                1400
% 1.80/1.02  --inst_solver_calls_frac                1.
% 1.80/1.02  --inst_passive_queue_type               priority_queues
% 1.80/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.80/1.02  --inst_passive_queues_freq              [25;2]
% 1.80/1.02  --inst_dismatching                      true
% 1.80/1.02  --inst_eager_unprocessed_to_passive     true
% 1.80/1.02  --inst_prop_sim_given                   true
% 1.80/1.02  --inst_prop_sim_new                     false
% 1.80/1.02  --inst_subs_new                         false
% 1.80/1.02  --inst_eq_res_simp                      false
% 1.80/1.02  --inst_subs_given                       false
% 1.80/1.02  --inst_orphan_elimination               true
% 1.80/1.02  --inst_learning_loop_flag               true
% 1.80/1.02  --inst_learning_start                   3000
% 1.80/1.02  --inst_learning_factor                  2
% 1.80/1.02  --inst_start_prop_sim_after_learn       3
% 1.80/1.02  --inst_sel_renew                        solver
% 1.80/1.02  --inst_lit_activity_flag                true
% 1.80/1.02  --inst_restr_to_given                   false
% 1.80/1.02  --inst_activity_threshold               500
% 1.80/1.02  --inst_out_proof                        true
% 1.80/1.02  
% 1.80/1.02  ------ Resolution Options
% 1.80/1.02  
% 1.80/1.02  --resolution_flag                       true
% 1.80/1.02  --res_lit_sel                           adaptive
% 1.80/1.02  --res_lit_sel_side                      none
% 1.80/1.02  --res_ordering                          kbo
% 1.80/1.02  --res_to_prop_solver                    active
% 1.80/1.02  --res_prop_simpl_new                    false
% 1.80/1.02  --res_prop_simpl_given                  true
% 1.80/1.02  --res_passive_queue_type                priority_queues
% 1.80/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.80/1.02  --res_passive_queues_freq               [15;5]
% 1.80/1.02  --res_forward_subs                      full
% 1.80/1.02  --res_backward_subs                     full
% 1.80/1.02  --res_forward_subs_resolution           true
% 1.80/1.02  --res_backward_subs_resolution          true
% 1.80/1.02  --res_orphan_elimination                true
% 1.80/1.02  --res_time_limit                        2.
% 1.80/1.02  --res_out_proof                         true
% 1.80/1.02  
% 1.80/1.02  ------ Superposition Options
% 1.80/1.02  
% 1.80/1.02  --superposition_flag                    true
% 1.80/1.02  --sup_passive_queue_type                priority_queues
% 1.80/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.80/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.80/1.02  --demod_completeness_check              fast
% 1.80/1.02  --demod_use_ground                      true
% 1.80/1.02  --sup_to_prop_solver                    passive
% 1.80/1.02  --sup_prop_simpl_new                    true
% 1.80/1.02  --sup_prop_simpl_given                  true
% 1.80/1.02  --sup_fun_splitting                     false
% 1.80/1.02  --sup_smt_interval                      50000
% 1.80/1.02  
% 1.80/1.02  ------ Superposition Simplification Setup
% 1.80/1.02  
% 1.80/1.02  --sup_indices_passive                   []
% 1.80/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.80/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.80/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.80/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.80/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.80/1.02  --sup_full_bw                           [BwDemod]
% 1.80/1.02  --sup_immed_triv                        [TrivRules]
% 1.80/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.80/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.80/1.02  --sup_immed_bw_main                     []
% 1.80/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.80/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.80/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.80/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.80/1.02  
% 1.80/1.02  ------ Combination Options
% 1.80/1.02  
% 1.80/1.02  --comb_res_mult                         3
% 1.80/1.02  --comb_sup_mult                         2
% 1.80/1.02  --comb_inst_mult                        10
% 1.80/1.02  
% 1.80/1.02  ------ Debug Options
% 1.80/1.02  
% 1.80/1.02  --dbg_backtrace                         false
% 1.80/1.02  --dbg_dump_prop_clauses                 false
% 1.80/1.02  --dbg_dump_prop_clauses_file            -
% 1.80/1.02  --dbg_out_stat                          false
% 1.80/1.02  ------ Parsing...
% 1.80/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.80/1.02  
% 1.80/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 1.80/1.02  
% 1.80/1.02  ------ Preprocessing... gs_s  sp: 6 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.80/1.02  
% 1.80/1.02  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.80/1.02  ------ Proving...
% 1.80/1.02  ------ Problem Properties 
% 1.80/1.02  
% 1.80/1.02  
% 1.80/1.02  clauses                                 19
% 1.80/1.02  conjectures                             3
% 1.80/1.02  EPR                                     0
% 1.80/1.02  Horn                                    15
% 1.80/1.02  unary                                   4
% 1.80/1.02  binary                                  9
% 1.80/1.02  lits                                    42
% 1.80/1.02  lits eq                                 16
% 1.80/1.02  fd_pure                                 0
% 1.80/1.02  fd_pseudo                               0
% 1.80/1.02  fd_cond                                 2
% 1.80/1.02  fd_pseudo_cond                          0
% 1.80/1.02  AC symbols                              0
% 1.80/1.02  
% 1.80/1.02  ------ Schedule dynamic 5 is on 
% 1.80/1.02  
% 1.80/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.80/1.02  
% 1.80/1.02  
% 1.80/1.02  ------ 
% 1.80/1.02  Current options:
% 1.80/1.02  ------ 
% 1.80/1.02  
% 1.80/1.02  ------ Input Options
% 1.80/1.02  
% 1.80/1.02  --out_options                           all
% 1.80/1.02  --tptp_safe_out                         true
% 1.80/1.02  --problem_path                          ""
% 1.80/1.02  --include_path                          ""
% 1.80/1.02  --clausifier                            res/vclausify_rel
% 1.80/1.02  --clausifier_options                    --mode clausify
% 1.80/1.02  --stdin                                 false
% 1.80/1.02  --stats_out                             all
% 1.80/1.02  
% 1.80/1.02  ------ General Options
% 1.80/1.02  
% 1.80/1.02  --fof                                   false
% 1.80/1.02  --time_out_real                         305.
% 1.80/1.02  --time_out_virtual                      -1.
% 1.80/1.02  --symbol_type_check                     false
% 1.80/1.02  --clausify_out                          false
% 1.80/1.02  --sig_cnt_out                           false
% 1.80/1.02  --trig_cnt_out                          false
% 1.80/1.02  --trig_cnt_out_tolerance                1.
% 1.80/1.02  --trig_cnt_out_sk_spl                   false
% 1.80/1.02  --abstr_cl_out                          false
% 1.80/1.02  
% 1.80/1.02  ------ Global Options
% 1.80/1.02  
% 1.80/1.02  --schedule                              default
% 1.80/1.02  --add_important_lit                     false
% 1.80/1.02  --prop_solver_per_cl                    1000
% 1.80/1.02  --min_unsat_core                        false
% 1.80/1.02  --soft_assumptions                      false
% 1.80/1.02  --soft_lemma_size                       3
% 1.80/1.02  --prop_impl_unit_size                   0
% 1.80/1.02  --prop_impl_unit                        []
% 1.80/1.02  --share_sel_clauses                     true
% 1.80/1.02  --reset_solvers                         false
% 1.80/1.02  --bc_imp_inh                            [conj_cone]
% 1.80/1.02  --conj_cone_tolerance                   3.
% 1.80/1.02  --extra_neg_conj                        none
% 1.80/1.02  --large_theory_mode                     true
% 1.80/1.02  --prolific_symb_bound                   200
% 1.80/1.02  --lt_threshold                          2000
% 1.80/1.02  --clause_weak_htbl                      true
% 1.80/1.02  --gc_record_bc_elim                     false
% 1.80/1.02  
% 1.80/1.02  ------ Preprocessing Options
% 1.80/1.02  
% 1.80/1.02  --preprocessing_flag                    true
% 1.80/1.02  --time_out_prep_mult                    0.1
% 1.80/1.02  --splitting_mode                        input
% 1.80/1.02  --splitting_grd                         true
% 1.80/1.02  --splitting_cvd                         false
% 1.80/1.02  --splitting_cvd_svl                     false
% 1.80/1.02  --splitting_nvd                         32
% 1.80/1.02  --sub_typing                            true
% 1.80/1.02  --prep_gs_sim                           true
% 1.80/1.02  --prep_unflatten                        true
% 1.80/1.02  --prep_res_sim                          true
% 1.80/1.02  --prep_upred                            true
% 1.80/1.02  --prep_sem_filter                       exhaustive
% 1.80/1.02  --prep_sem_filter_out                   false
% 1.80/1.02  --pred_elim                             true
% 1.80/1.02  --res_sim_input                         true
% 1.80/1.02  --eq_ax_congr_red                       true
% 1.80/1.02  --pure_diseq_elim                       true
% 1.80/1.02  --brand_transform                       false
% 1.80/1.02  --non_eq_to_eq                          false
% 1.80/1.02  --prep_def_merge                        true
% 1.80/1.02  --prep_def_merge_prop_impl              false
% 1.80/1.02  --prep_def_merge_mbd                    true
% 1.80/1.02  --prep_def_merge_tr_red                 false
% 1.80/1.02  --prep_def_merge_tr_cl                  false
% 1.80/1.02  --smt_preprocessing                     true
% 1.80/1.02  --smt_ac_axioms                         fast
% 1.80/1.02  --preprocessed_out                      false
% 1.80/1.02  --preprocessed_stats                    false
% 1.80/1.02  
% 1.80/1.02  ------ Abstraction refinement Options
% 1.80/1.02  
% 1.80/1.02  --abstr_ref                             []
% 1.80/1.02  --abstr_ref_prep                        false
% 1.80/1.02  --abstr_ref_until_sat                   false
% 1.80/1.02  --abstr_ref_sig_restrict                funpre
% 1.80/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.80/1.02  --abstr_ref_under                       []
% 1.80/1.02  
% 1.80/1.02  ------ SAT Options
% 1.80/1.02  
% 1.80/1.02  --sat_mode                              false
% 1.80/1.02  --sat_fm_restart_options                ""
% 1.80/1.02  --sat_gr_def                            false
% 1.80/1.02  --sat_epr_types                         true
% 1.80/1.02  --sat_non_cyclic_types                  false
% 1.80/1.02  --sat_finite_models                     false
% 1.80/1.02  --sat_fm_lemmas                         false
% 1.80/1.02  --sat_fm_prep                           false
% 1.80/1.02  --sat_fm_uc_incr                        true
% 1.80/1.02  --sat_out_model                         small
% 1.80/1.02  --sat_out_clauses                       false
% 1.80/1.02  
% 1.80/1.02  ------ QBF Options
% 1.80/1.02  
% 1.80/1.02  --qbf_mode                              false
% 1.80/1.02  --qbf_elim_univ                         false
% 1.80/1.02  --qbf_dom_inst                          none
% 1.80/1.02  --qbf_dom_pre_inst                      false
% 1.80/1.02  --qbf_sk_in                             false
% 1.80/1.02  --qbf_pred_elim                         true
% 1.80/1.02  --qbf_split                             512
% 1.80/1.02  
% 1.80/1.02  ------ BMC1 Options
% 1.80/1.02  
% 1.80/1.02  --bmc1_incremental                      false
% 1.80/1.02  --bmc1_axioms                           reachable_all
% 1.80/1.02  --bmc1_min_bound                        0
% 1.80/1.02  --bmc1_max_bound                        -1
% 1.80/1.02  --bmc1_max_bound_default                -1
% 1.80/1.02  --bmc1_symbol_reachability              true
% 1.80/1.02  --bmc1_property_lemmas                  false
% 1.80/1.02  --bmc1_k_induction                      false
% 1.80/1.02  --bmc1_non_equiv_states                 false
% 1.80/1.02  --bmc1_deadlock                         false
% 1.80/1.02  --bmc1_ucm                              false
% 1.80/1.02  --bmc1_add_unsat_core                   none
% 1.80/1.02  --bmc1_unsat_core_children              false
% 1.80/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.80/1.02  --bmc1_out_stat                         full
% 1.80/1.02  --bmc1_ground_init                      false
% 1.80/1.02  --bmc1_pre_inst_next_state              false
% 1.80/1.02  --bmc1_pre_inst_state                   false
% 1.80/1.02  --bmc1_pre_inst_reach_state             false
% 1.80/1.02  --bmc1_out_unsat_core                   false
% 1.80/1.02  --bmc1_aig_witness_out                  false
% 1.80/1.02  --bmc1_verbose                          false
% 1.80/1.02  --bmc1_dump_clauses_tptp                false
% 1.80/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.80/1.02  --bmc1_dump_file                        -
% 1.80/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.80/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.80/1.02  --bmc1_ucm_extend_mode                  1
% 1.80/1.02  --bmc1_ucm_init_mode                    2
% 1.80/1.02  --bmc1_ucm_cone_mode                    none
% 1.80/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.80/1.02  --bmc1_ucm_relax_model                  4
% 1.80/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.80/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.80/1.02  --bmc1_ucm_layered_model                none
% 1.80/1.02  --bmc1_ucm_max_lemma_size               10
% 1.80/1.02  
% 1.80/1.02  ------ AIG Options
% 1.80/1.02  
% 1.80/1.02  --aig_mode                              false
% 1.80/1.02  
% 1.80/1.02  ------ Instantiation Options
% 1.80/1.02  
% 1.80/1.02  --instantiation_flag                    true
% 1.80/1.02  --inst_sos_flag                         false
% 1.80/1.02  --inst_sos_phase                        true
% 1.80/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.80/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.80/1.02  --inst_lit_sel_side                     none
% 1.80/1.02  --inst_solver_per_active                1400
% 1.80/1.02  --inst_solver_calls_frac                1.
% 1.80/1.02  --inst_passive_queue_type               priority_queues
% 1.80/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.80/1.02  --inst_passive_queues_freq              [25;2]
% 1.80/1.02  --inst_dismatching                      true
% 1.80/1.02  --inst_eager_unprocessed_to_passive     true
% 1.80/1.02  --inst_prop_sim_given                   true
% 1.80/1.02  --inst_prop_sim_new                     false
% 1.80/1.02  --inst_subs_new                         false
% 1.80/1.02  --inst_eq_res_simp                      false
% 1.80/1.02  --inst_subs_given                       false
% 1.80/1.02  --inst_orphan_elimination               true
% 1.80/1.02  --inst_learning_loop_flag               true
% 1.80/1.02  --inst_learning_start                   3000
% 1.80/1.02  --inst_learning_factor                  2
% 1.80/1.02  --inst_start_prop_sim_after_learn       3
% 1.80/1.02  --inst_sel_renew                        solver
% 1.80/1.02  --inst_lit_activity_flag                true
% 1.80/1.02  --inst_restr_to_given                   false
% 1.80/1.02  --inst_activity_threshold               500
% 1.80/1.02  --inst_out_proof                        true
% 1.80/1.02  
% 1.80/1.02  ------ Resolution Options
% 1.80/1.02  
% 1.80/1.02  --resolution_flag                       false
% 1.80/1.02  --res_lit_sel                           adaptive
% 1.80/1.02  --res_lit_sel_side                      none
% 1.80/1.02  --res_ordering                          kbo
% 1.80/1.02  --res_to_prop_solver                    active
% 1.80/1.02  --res_prop_simpl_new                    false
% 1.80/1.02  --res_prop_simpl_given                  true
% 1.80/1.02  --res_passive_queue_type                priority_queues
% 1.80/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.80/1.02  --res_passive_queues_freq               [15;5]
% 1.80/1.02  --res_forward_subs                      full
% 1.80/1.02  --res_backward_subs                     full
% 1.80/1.02  --res_forward_subs_resolution           true
% 1.80/1.02  --res_backward_subs_resolution          true
% 1.80/1.02  --res_orphan_elimination                true
% 1.80/1.02  --res_time_limit                        2.
% 1.80/1.02  --res_out_proof                         true
% 1.80/1.02  
% 1.80/1.02  ------ Superposition Options
% 1.80/1.02  
% 1.80/1.02  --superposition_flag                    true
% 1.80/1.02  --sup_passive_queue_type                priority_queues
% 1.80/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.80/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.80/1.02  --demod_completeness_check              fast
% 1.80/1.02  --demod_use_ground                      true
% 1.80/1.02  --sup_to_prop_solver                    passive
% 1.80/1.02  --sup_prop_simpl_new                    true
% 1.80/1.02  --sup_prop_simpl_given                  true
% 1.80/1.02  --sup_fun_splitting                     false
% 1.80/1.02  --sup_smt_interval                      50000
% 1.80/1.02  
% 1.80/1.02  ------ Superposition Simplification Setup
% 1.80/1.02  
% 1.80/1.02  --sup_indices_passive                   []
% 1.80/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.80/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.80/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.80/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.80/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.80/1.02  --sup_full_bw                           [BwDemod]
% 1.80/1.02  --sup_immed_triv                        [TrivRules]
% 1.80/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.80/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.80/1.02  --sup_immed_bw_main                     []
% 1.80/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.80/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.80/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.80/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.80/1.02  
% 1.80/1.02  ------ Combination Options
% 1.80/1.02  
% 1.80/1.02  --comb_res_mult                         3
% 1.80/1.02  --comb_sup_mult                         2
% 1.80/1.02  --comb_inst_mult                        10
% 1.80/1.02  
% 1.80/1.02  ------ Debug Options
% 1.80/1.02  
% 1.80/1.02  --dbg_backtrace                         false
% 1.80/1.02  --dbg_dump_prop_clauses                 false
% 1.80/1.02  --dbg_dump_prop_clauses_file            -
% 1.80/1.02  --dbg_out_stat                          false
% 1.80/1.02  
% 1.80/1.02  
% 1.80/1.02  
% 1.80/1.02  
% 1.80/1.02  ------ Proving...
% 1.80/1.02  
% 1.80/1.02  
% 1.80/1.02  % SZS status Theorem for theBenchmark.p
% 1.80/1.02  
% 1.80/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 1.80/1.02  
% 1.80/1.02  fof(f6,axiom,(
% 1.80/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.80/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.80/1.02  
% 1.80/1.02  fof(f16,plain,(
% 1.80/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.80/1.02    inference(pure_predicate_removal,[],[f6])).
% 1.80/1.02  
% 1.80/1.02  fof(f21,plain,(
% 1.80/1.02    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.80/1.02    inference(ennf_transformation,[],[f16])).
% 1.80/1.02  
% 1.80/1.02  fof(f48,plain,(
% 1.80/1.02    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.80/1.02    inference(cnf_transformation,[],[f21])).
% 1.80/1.02  
% 1.80/1.02  fof(f11,axiom,(
% 1.80/1.02    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 1.80/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.80/1.02  
% 1.80/1.02  fof(f27,plain,(
% 1.80/1.02    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.80/1.02    inference(ennf_transformation,[],[f11])).
% 1.80/1.02  
% 1.80/1.02  fof(f28,plain,(
% 1.80/1.02    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.80/1.02    inference(flattening,[],[f27])).
% 1.80/1.02  
% 1.80/1.02  fof(f36,plain,(
% 1.80/1.02    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.80/1.02    inference(nnf_transformation,[],[f28])).
% 1.80/1.02  
% 1.80/1.02  fof(f55,plain,(
% 1.80/1.02    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.80/1.02    inference(cnf_transformation,[],[f36])).
% 1.80/1.02  
% 1.80/1.02  fof(f1,axiom,(
% 1.80/1.02    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.80/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.80/1.02  
% 1.80/1.02  fof(f17,plain,(
% 1.80/1.02    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.80/1.02    inference(ennf_transformation,[],[f1])).
% 1.80/1.02  
% 1.80/1.02  fof(f41,plain,(
% 1.80/1.02    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.80/1.02    inference(cnf_transformation,[],[f17])).
% 1.80/1.02  
% 1.80/1.02  fof(f10,axiom,(
% 1.80/1.02    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 1.80/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.80/1.02  
% 1.80/1.02  fof(f25,plain,(
% 1.80/1.02    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.80/1.02    inference(ennf_transformation,[],[f10])).
% 1.80/1.02  
% 1.80/1.02  fof(f26,plain,(
% 1.80/1.02    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.80/1.02    inference(flattening,[],[f25])).
% 1.80/1.02  
% 1.80/1.02  fof(f54,plain,(
% 1.80/1.02    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 1.80/1.02    inference(cnf_transformation,[],[f26])).
% 1.80/1.02  
% 1.80/1.02  fof(f13,conjecture,(
% 1.80/1.02    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) = k2_struct_0(X0)))))),
% 1.80/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.80/1.02  
% 1.80/1.02  fof(f14,negated_conjecture,(
% 1.80/1.02    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) = k2_struct_0(X0)))))),
% 1.80/1.02    inference(negated_conjecture,[],[f13])).
% 1.80/1.02  
% 1.80/1.02  fof(f30,plain,(
% 1.80/1.02    ? [X0] : (? [X1] : (? [X2] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 1.80/1.02    inference(ennf_transformation,[],[f14])).
% 1.80/1.02  
% 1.80/1.02  fof(f31,plain,(
% 1.80/1.02    ? [X0] : (? [X1] : (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 1.80/1.02    inference(flattening,[],[f30])).
% 1.80/1.02  
% 1.80/1.02  fof(f39,plain,(
% 1.80/1.02    ( ! [X0,X1] : (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK3))) )),
% 1.80/1.02    introduced(choice_axiom,[])).
% 1.80/1.02  
% 1.80/1.02  fof(f38,plain,(
% 1.80/1.02    ( ! [X0] : (? [X1] : (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(sK2),X2,k2_struct_0(sK2)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(sK2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK2)) & v1_funct_1(X2)) & l1_struct_0(sK2))) )),
% 1.80/1.02    introduced(choice_axiom,[])).
% 1.80/1.02  
% 1.80/1.02  fof(f37,plain,(
% 1.80/1.02    ? [X0] : (? [X1] : (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (k8_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(sK1) & (k1_xboole_0 = k2_struct_0(sK1) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK1))),
% 1.80/1.02    introduced(choice_axiom,[])).
% 1.80/1.02  
% 1.80/1.02  fof(f40,plain,(
% 1.80/1.02    ((k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_struct_0(sK2)) != k2_struct_0(sK1) & (k1_xboole_0 = k2_struct_0(sK1) | k1_xboole_0 != k2_struct_0(sK2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK3)) & l1_struct_0(sK2)) & l1_struct_0(sK1)),
% 1.80/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f31,f39,f38,f37])).
% 1.80/1.02  
% 1.80/1.02  fof(f61,plain,(
% 1.80/1.02    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))),
% 1.80/1.02    inference(cnf_transformation,[],[f40])).
% 1.80/1.02  
% 1.80/1.02  fof(f60,plain,(
% 1.80/1.02    v1_funct_1(sK3)),
% 1.80/1.02    inference(cnf_transformation,[],[f40])).
% 1.80/1.02  
% 1.80/1.02  fof(f62,plain,(
% 1.80/1.02    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))),
% 1.80/1.02    inference(cnf_transformation,[],[f40])).
% 1.80/1.02  
% 1.80/1.02  fof(f5,axiom,(
% 1.80/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.80/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.80/1.02  
% 1.80/1.02  fof(f20,plain,(
% 1.80/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.80/1.02    inference(ennf_transformation,[],[f5])).
% 1.80/1.02  
% 1.80/1.02  fof(f47,plain,(
% 1.80/1.02    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.80/1.02    inference(cnf_transformation,[],[f20])).
% 1.80/1.02  
% 1.80/1.02  fof(f12,axiom,(
% 1.80/1.02    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.80/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.80/1.02  
% 1.80/1.02  fof(f29,plain,(
% 1.80/1.02    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.80/1.02    inference(ennf_transformation,[],[f12])).
% 1.80/1.02  
% 1.80/1.02  fof(f57,plain,(
% 1.80/1.02    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.80/1.02    inference(cnf_transformation,[],[f29])).
% 1.80/1.02  
% 1.80/1.02  fof(f58,plain,(
% 1.80/1.02    l1_struct_0(sK1)),
% 1.80/1.02    inference(cnf_transformation,[],[f40])).
% 1.80/1.02  
% 1.80/1.02  fof(f59,plain,(
% 1.80/1.02    l1_struct_0(sK2)),
% 1.80/1.02    inference(cnf_transformation,[],[f40])).
% 1.80/1.02  
% 1.80/1.02  fof(f8,axiom,(
% 1.80/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 1.80/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.80/1.02  
% 1.80/1.02  fof(f23,plain,(
% 1.80/1.02    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.80/1.02    inference(ennf_transformation,[],[f8])).
% 1.80/1.02  
% 1.80/1.02  fof(f51,plain,(
% 1.80/1.02    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.80/1.02    inference(cnf_transformation,[],[f23])).
% 1.80/1.02  
% 1.80/1.02  fof(f7,axiom,(
% 1.80/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.80/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.80/1.02  
% 1.80/1.02  fof(f22,plain,(
% 1.80/1.02    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.80/1.02    inference(ennf_transformation,[],[f7])).
% 1.80/1.02  
% 1.80/1.02  fof(f49,plain,(
% 1.80/1.02    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.80/1.02    inference(cnf_transformation,[],[f22])).
% 1.80/1.02  
% 1.80/1.02  fof(f64,plain,(
% 1.80/1.02    k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_struct_0(sK2)) != k2_struct_0(sK1)),
% 1.80/1.02    inference(cnf_transformation,[],[f40])).
% 1.80/1.02  
% 1.80/1.02  fof(f63,plain,(
% 1.80/1.02    k1_xboole_0 = k2_struct_0(sK1) | k1_xboole_0 != k2_struct_0(sK2)),
% 1.80/1.02    inference(cnf_transformation,[],[f40])).
% 1.80/1.02  
% 1.80/1.02  fof(f2,axiom,(
% 1.80/1.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.80/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.80/1.02  
% 1.80/1.02  fof(f32,plain,(
% 1.80/1.02    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.80/1.02    inference(nnf_transformation,[],[f2])).
% 1.80/1.02  
% 1.80/1.02  fof(f43,plain,(
% 1.80/1.02    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.80/1.02    inference(cnf_transformation,[],[f32])).
% 1.80/1.02  
% 1.80/1.02  fof(f4,axiom,(
% 1.80/1.02    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.80/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.80/1.02  
% 1.80/1.02  fof(f19,plain,(
% 1.80/1.02    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.80/1.02    inference(ennf_transformation,[],[f4])).
% 1.80/1.02  
% 1.80/1.02  fof(f33,plain,(
% 1.80/1.02    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.80/1.02    inference(nnf_transformation,[],[f19])).
% 1.80/1.02  
% 1.80/1.02  fof(f45,plain,(
% 1.80/1.02    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.80/1.02    inference(cnf_transformation,[],[f33])).
% 1.80/1.02  
% 1.80/1.02  fof(f3,axiom,(
% 1.80/1.02    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.80/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.80/1.02  
% 1.80/1.02  fof(f18,plain,(
% 1.80/1.02    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.80/1.02    inference(ennf_transformation,[],[f3])).
% 1.80/1.02  
% 1.80/1.02  fof(f44,plain,(
% 1.80/1.02    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.80/1.02    inference(cnf_transformation,[],[f18])).
% 1.80/1.02  
% 1.80/1.02  fof(f9,axiom,(
% 1.80/1.02    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.80/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.80/1.02  
% 1.80/1.02  fof(f15,plain,(
% 1.80/1.02    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.80/1.02    inference(pure_predicate_removal,[],[f9])).
% 1.80/1.02  
% 1.80/1.02  fof(f24,plain,(
% 1.80/1.02    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.80/1.02    inference(ennf_transformation,[],[f15])).
% 1.80/1.02  
% 1.80/1.02  fof(f34,plain,(
% 1.80/1.02    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 1.80/1.02    introduced(choice_axiom,[])).
% 1.80/1.02  
% 1.80/1.02  fof(f35,plain,(
% 1.80/1.02    ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0)),
% 1.80/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f34])).
% 1.80/1.02  
% 1.80/1.02  fof(f52,plain,(
% 1.80/1.02    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 1.80/1.02    inference(cnf_transformation,[],[f35])).
% 1.80/1.02  
% 1.80/1.02  cnf(c_7,plain,
% 1.80/1.02      ( v4_relat_1(X0,X1)
% 1.80/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 1.80/1.02      inference(cnf_transformation,[],[f48]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_15,plain,
% 1.80/1.02      ( ~ v1_partfun1(X0,X1)
% 1.80/1.02      | ~ v4_relat_1(X0,X1)
% 1.80/1.02      | ~ v1_relat_1(X0)
% 1.80/1.02      | k1_relat_1(X0) = X1 ),
% 1.80/1.02      inference(cnf_transformation,[],[f55]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_0,plain,
% 1.80/1.02      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 1.80/1.02      inference(cnf_transformation,[],[f41]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_12,plain,
% 1.80/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 1.80/1.02      | v1_partfun1(X0,X1)
% 1.80/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.80/1.02      | ~ v1_funct_1(X0)
% 1.80/1.02      | v1_xboole_0(X2) ),
% 1.80/1.02      inference(cnf_transformation,[],[f54]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_20,negated_conjecture,
% 1.80/1.02      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 1.80/1.02      inference(cnf_transformation,[],[f61]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_326,plain,
% 1.80/1.02      ( v1_partfun1(X0,X1)
% 1.80/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.80/1.02      | ~ v1_funct_1(X0)
% 1.80/1.02      | v1_xboole_0(X2)
% 1.80/1.02      | u1_struct_0(sK2) != X2
% 1.80/1.02      | u1_struct_0(sK1) != X1
% 1.80/1.02      | sK3 != X0 ),
% 1.80/1.02      inference(resolution_lifted,[status(thm)],[c_12,c_20]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_327,plain,
% 1.80/1.02      ( v1_partfun1(sK3,u1_struct_0(sK1))
% 1.80/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 1.80/1.02      | ~ v1_funct_1(sK3)
% 1.80/1.02      | v1_xboole_0(u1_struct_0(sK2)) ),
% 1.80/1.02      inference(unflattening,[status(thm)],[c_326]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_21,negated_conjecture,
% 1.80/1.02      ( v1_funct_1(sK3) ),
% 1.80/1.02      inference(cnf_transformation,[],[f60]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_19,negated_conjecture,
% 1.80/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
% 1.80/1.02      inference(cnf_transformation,[],[f62]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_329,plain,
% 1.80/1.02      ( v1_partfun1(sK3,u1_struct_0(sK1))
% 1.80/1.02      | v1_xboole_0(u1_struct_0(sK2)) ),
% 1.80/1.02      inference(global_propositional_subsumption,
% 1.80/1.02                [status(thm)],
% 1.80/1.02                [c_327,c_21,c_19]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_343,plain,
% 1.80/1.02      ( v1_partfun1(sK3,u1_struct_0(sK1))
% 1.80/1.02      | u1_struct_0(sK2) != X0
% 1.80/1.02      | k1_xboole_0 = X0 ),
% 1.80/1.02      inference(resolution_lifted,[status(thm)],[c_0,c_329]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_344,plain,
% 1.80/1.02      ( v1_partfun1(sK3,u1_struct_0(sK1))
% 1.80/1.02      | k1_xboole_0 = u1_struct_0(sK2) ),
% 1.80/1.02      inference(unflattening,[status(thm)],[c_343]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_508,plain,
% 1.80/1.02      ( ~ v4_relat_1(X0,X1)
% 1.80/1.02      | ~ v1_relat_1(X0)
% 1.80/1.02      | u1_struct_0(sK2) = k1_xboole_0
% 1.80/1.02      | u1_struct_0(sK1) != X1
% 1.80/1.02      | k1_relat_1(X0) = X1
% 1.80/1.02      | sK3 != X0 ),
% 1.80/1.02      inference(resolution_lifted,[status(thm)],[c_15,c_344]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_509,plain,
% 1.80/1.02      ( ~ v4_relat_1(sK3,u1_struct_0(sK1))
% 1.80/1.02      | ~ v1_relat_1(sK3)
% 1.80/1.02      | u1_struct_0(sK2) = k1_xboole_0
% 1.80/1.02      | k1_relat_1(sK3) = u1_struct_0(sK1) ),
% 1.80/1.02      inference(unflattening,[status(thm)],[c_508]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_668,plain,
% 1.80/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.80/1.02      | ~ v1_relat_1(sK3)
% 1.80/1.02      | u1_struct_0(sK2) = k1_xboole_0
% 1.80/1.02      | u1_struct_0(sK1) != X1
% 1.80/1.02      | u1_struct_0(sK1) = k1_relat_1(sK3)
% 1.80/1.02      | sK3 != X0 ),
% 1.80/1.02      inference(resolution_lifted,[status(thm)],[c_7,c_509]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_669,plain,
% 1.80/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0)))
% 1.80/1.02      | ~ v1_relat_1(sK3)
% 1.80/1.02      | u1_struct_0(sK2) = k1_xboole_0
% 1.80/1.02      | u1_struct_0(sK1) = k1_relat_1(sK3) ),
% 1.80/1.02      inference(unflattening,[status(thm)],[c_668]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_6,plain,
% 1.80/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.80/1.02      | v1_relat_1(X0) ),
% 1.80/1.02      inference(cnf_transformation,[],[f47]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_681,plain,
% 1.80/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0)))
% 1.80/1.02      | u1_struct_0(sK2) = k1_xboole_0
% 1.80/1.02      | u1_struct_0(sK1) = k1_relat_1(sK3) ),
% 1.80/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_669,c_6]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_855,plain,
% 1.80/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0_52)))
% 1.80/1.02      | u1_struct_0(sK2) = k1_xboole_0
% 1.80/1.02      | u1_struct_0(sK1) = k1_relat_1(sK3) ),
% 1.80/1.02      inference(subtyping,[status(esa)],[c_681]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_866,plain,
% 1.80/1.02      ( sP0_iProver_split
% 1.80/1.02      | u1_struct_0(sK2) = k1_xboole_0
% 1.80/1.02      | u1_struct_0(sK1) = k1_relat_1(sK3) ),
% 1.80/1.02      inference(splitting,
% 1.80/1.02                [splitting(split),new_symbols(definition,[])],
% 1.80/1.02                [c_855]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_1102,plain,
% 1.80/1.02      ( u1_struct_0(sK2) = k1_xboole_0
% 1.80/1.02      | u1_struct_0(sK1) = k1_relat_1(sK3)
% 1.80/1.02      | sP0_iProver_split = iProver_top ),
% 1.80/1.02      inference(predicate_to_equality,[status(thm)],[c_866]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_16,plain,
% 1.80/1.02      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 1.80/1.02      inference(cnf_transformation,[],[f57]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_23,negated_conjecture,
% 1.80/1.02      ( l1_struct_0(sK1) ),
% 1.80/1.02      inference(cnf_transformation,[],[f58]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_302,plain,
% 1.80/1.02      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 1.80/1.02      inference(resolution_lifted,[status(thm)],[c_16,c_23]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_303,plain,
% 1.80/1.02      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 1.80/1.02      inference(unflattening,[status(thm)],[c_302]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_857,plain,
% 1.80/1.02      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 1.80/1.02      inference(subtyping,[status(esa)],[c_303]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_22,negated_conjecture,
% 1.80/1.02      ( l1_struct_0(sK2) ),
% 1.80/1.02      inference(cnf_transformation,[],[f59]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_297,plain,
% 1.80/1.02      ( u1_struct_0(X0) = k2_struct_0(X0) | sK2 != X0 ),
% 1.80/1.02      inference(resolution_lifted,[status(thm)],[c_16,c_22]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_298,plain,
% 1.80/1.02      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 1.80/1.02      inference(unflattening,[status(thm)],[c_297]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_858,plain,
% 1.80/1.02      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 1.80/1.02      inference(subtyping,[status(esa)],[c_298]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_1133,plain,
% 1.80/1.02      ( k2_struct_0(sK2) = k1_xboole_0
% 1.80/1.02      | k2_struct_0(sK1) = k1_relat_1(sK3)
% 1.80/1.02      | sP0_iProver_split = iProver_top ),
% 1.80/1.02      inference(demodulation,[status(thm)],[c_1102,c_857,c_858]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_28,plain,
% 1.80/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
% 1.80/1.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_865,plain,
% 1.80/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0_52)))
% 1.80/1.02      | ~ sP0_iProver_split ),
% 1.80/1.02      inference(splitting,
% 1.80/1.02                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.80/1.02                [c_855]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_1220,plain,
% 1.80/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 1.80/1.02      | ~ sP0_iProver_split ),
% 1.80/1.02      inference(instantiation,[status(thm)],[c_865]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_1221,plain,
% 1.80/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
% 1.80/1.02      | sP0_iProver_split != iProver_top ),
% 1.80/1.02      inference(predicate_to_equality,[status(thm)],[c_1220]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_859,negated_conjecture,
% 1.80/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
% 1.80/1.02      inference(subtyping,[status(esa)],[c_19]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_1100,plain,
% 1.80/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
% 1.80/1.02      inference(predicate_to_equality,[status(thm)],[c_859]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_1120,plain,
% 1.80/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) = iProver_top ),
% 1.80/1.02      inference(light_normalisation,[status(thm)],[c_1100,c_857,c_858]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_9,plain,
% 1.80/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.80/1.02      | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
% 1.80/1.02      inference(cnf_transformation,[],[f51]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_863,plain,
% 1.80/1.02      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
% 1.80/1.02      | k8_relset_1(X1_52,X2_52,X0_52,X2_52) = k1_relset_1(X1_52,X2_52,X0_52) ),
% 1.80/1.02      inference(subtyping,[status(esa)],[c_9]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_1098,plain,
% 1.80/1.02      ( k8_relset_1(X0_52,X1_52,X2_52,X1_52) = k1_relset_1(X0_52,X1_52,X2_52)
% 1.80/1.02      | m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
% 1.80/1.02      inference(predicate_to_equality,[status(thm)],[c_863]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_1403,plain,
% 1.80/1.02      ( k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,k2_struct_0(sK2)) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) ),
% 1.80/1.02      inference(superposition,[status(thm)],[c_1120,c_1098]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_8,plain,
% 1.80/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.80/1.02      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.80/1.02      inference(cnf_transformation,[],[f49]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_864,plain,
% 1.80/1.02      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
% 1.80/1.02      | k1_relset_1(X1_52,X2_52,X0_52) = k1_relat_1(X0_52) ),
% 1.80/1.02      inference(subtyping,[status(esa)],[c_8]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_1097,plain,
% 1.80/1.02      ( k1_relset_1(X0_52,X1_52,X2_52) = k1_relat_1(X2_52)
% 1.80/1.02      | m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
% 1.80/1.02      inference(predicate_to_equality,[status(thm)],[c_864]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_1399,plain,
% 1.80/1.02      ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) = k1_relat_1(sK3) ),
% 1.80/1.02      inference(superposition,[status(thm)],[c_1120,c_1097]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_1529,plain,
% 1.80/1.02      ( k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,k2_struct_0(sK2)) = k1_relat_1(sK3) ),
% 1.80/1.02      inference(light_normalisation,[status(thm)],[c_1403,c_1399]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_17,negated_conjecture,
% 1.80/1.02      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_struct_0(sK2)) != k2_struct_0(sK1) ),
% 1.80/1.02      inference(cnf_transformation,[],[f64]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_861,negated_conjecture,
% 1.80/1.02      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_struct_0(sK2)) != k2_struct_0(sK1) ),
% 1.80/1.02      inference(subtyping,[status(esa)],[c_17]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_1123,plain,
% 1.80/1.02      ( k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,k2_struct_0(sK2)) != k2_struct_0(sK1) ),
% 1.80/1.02      inference(light_normalisation,[status(thm)],[c_861,c_857,c_858]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_1531,plain,
% 1.80/1.02      ( k2_struct_0(sK1) != k1_relat_1(sK3) ),
% 1.80/1.02      inference(demodulation,[status(thm)],[c_1529,c_1123]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_1562,plain,
% 1.80/1.02      ( k2_struct_0(sK2) = k1_xboole_0 ),
% 1.80/1.02      inference(global_propositional_subsumption,
% 1.80/1.02                [status(thm)],
% 1.80/1.02                [c_1133,c_28,c_1221,c_1531]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_1568,plain,
% 1.80/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0))) = iProver_top ),
% 1.80/1.02      inference(demodulation,[status(thm)],[c_1562,c_1120]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_18,negated_conjecture,
% 1.80/1.02      ( k1_xboole_0 != k2_struct_0(sK2)
% 1.80/1.02      | k1_xboole_0 = k2_struct_0(sK1) ),
% 1.80/1.02      inference(cnf_transformation,[],[f63]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_860,negated_conjecture,
% 1.80/1.02      ( k1_xboole_0 != k2_struct_0(sK2)
% 1.80/1.02      | k1_xboole_0 = k2_struct_0(sK1) ),
% 1.80/1.02      inference(subtyping,[status(esa)],[c_18]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_1570,plain,
% 1.80/1.02      ( k2_struct_0(sK1) = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 1.80/1.02      inference(demodulation,[status(thm)],[c_1562,c_860]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_1571,plain,
% 1.80/1.02      ( k2_struct_0(sK1) = k1_xboole_0 ),
% 1.80/1.02      inference(equality_resolution_simp,[status(thm)],[c_1570]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_1576,plain,
% 1.80/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 1.80/1.02      inference(light_normalisation,[status(thm)],[c_1568,c_1571]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_1,plain,
% 1.80/1.02      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 1.80/1.02      inference(cnf_transformation,[],[f43]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_176,plain,
% 1.80/1.02      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 1.80/1.02      inference(prop_impl,[status(thm)],[c_1]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_5,plain,
% 1.80/1.02      ( ~ v4_relat_1(X0,X1)
% 1.80/1.02      | r1_tarski(k1_relat_1(X0),X1)
% 1.80/1.02      | ~ v1_relat_1(X0) ),
% 1.80/1.02      inference(cnf_transformation,[],[f45]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_392,plain,
% 1.80/1.02      ( ~ v4_relat_1(X0,X1)
% 1.80/1.02      | m1_subset_1(X2,k1_zfmisc_1(X3))
% 1.80/1.02      | ~ v1_relat_1(X0)
% 1.80/1.02      | X1 != X3
% 1.80/1.02      | k1_relat_1(X0) != X2 ),
% 1.80/1.02      inference(resolution_lifted,[status(thm)],[c_176,c_5]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_393,plain,
% 1.80/1.02      ( ~ v4_relat_1(X0,X1)
% 1.80/1.02      | m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(X1))
% 1.80/1.02      | ~ v1_relat_1(X0) ),
% 1.80/1.02      inference(unflattening,[status(thm)],[c_392]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_614,plain,
% 1.80/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.80/1.02      | m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(X1))
% 1.80/1.02      | ~ v1_relat_1(X0) ),
% 1.80/1.02      inference(resolution,[status(thm)],[c_7,c_393]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_618,plain,
% 1.80/1.02      ( m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(X1))
% 1.80/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 1.80/1.02      inference(global_propositional_subsumption,
% 1.80/1.02                [status(thm)],
% 1.80/1.02                [c_614,c_6]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_619,plain,
% 1.80/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.80/1.02      | m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(X1)) ),
% 1.80/1.02      inference(renaming,[status(thm)],[c_618]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_856,plain,
% 1.80/1.02      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
% 1.80/1.02      | m1_subset_1(k1_relat_1(X0_52),k1_zfmisc_1(X1_52)) ),
% 1.80/1.02      inference(subtyping,[status(esa)],[c_619]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_1101,plain,
% 1.80/1.02      ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52))) != iProver_top
% 1.80/1.02      | m1_subset_1(k1_relat_1(X0_52),k1_zfmisc_1(X1_52)) = iProver_top ),
% 1.80/1.02      inference(predicate_to_equality,[status(thm)],[c_856]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_1920,plain,
% 1.80/1.02      ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 1.80/1.02      inference(superposition,[status(thm)],[c_1576,c_1101]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_3,plain,
% 1.80/1.02      ( ~ r2_hidden(X0,X1)
% 1.80/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 1.80/1.02      | ~ v1_xboole_0(X2) ),
% 1.80/1.02      inference(cnf_transformation,[],[f44]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_11,plain,
% 1.80/1.02      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 1.80/1.02      inference(cnf_transformation,[],[f52]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_309,plain,
% 1.80/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.80/1.02      | ~ v1_xboole_0(X1)
% 1.80/1.02      | X2 != X0
% 1.80/1.02      | sK0(X2) != X3
% 1.80/1.02      | k1_xboole_0 = X2 ),
% 1.80/1.02      inference(resolution_lifted,[status(thm)],[c_3,c_11]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_310,plain,
% 1.80/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.80/1.02      | ~ v1_xboole_0(X1)
% 1.80/1.02      | k1_xboole_0 = X0 ),
% 1.80/1.02      inference(unflattening,[status(thm)],[c_309]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_353,plain,
% 1.80/1.02      ( v1_partfun1(sK3,u1_struct_0(sK1))
% 1.80/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.80/1.02      | u1_struct_0(sK2) != X1
% 1.80/1.02      | k1_xboole_0 = X0 ),
% 1.80/1.02      inference(resolution_lifted,[status(thm)],[c_310,c_329]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_354,plain,
% 1.80/1.02      ( v1_partfun1(sK3,u1_struct_0(sK1))
% 1.80/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.80/1.02      | k1_xboole_0 = X0 ),
% 1.80/1.02      inference(unflattening,[status(thm)],[c_353]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_487,plain,
% 1.80/1.02      ( ~ v4_relat_1(X0,X1)
% 1.80/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.80/1.02      | ~ v1_relat_1(X0)
% 1.80/1.02      | u1_struct_0(sK1) != X1
% 1.80/1.02      | k1_relat_1(X0) = X1
% 1.80/1.02      | sK3 != X0
% 1.80/1.02      | k1_xboole_0 = X2 ),
% 1.80/1.02      inference(resolution_lifted,[status(thm)],[c_15,c_354]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_488,plain,
% 1.80/1.02      ( ~ v4_relat_1(sK3,u1_struct_0(sK1))
% 1.80/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.80/1.02      | ~ v1_relat_1(sK3)
% 1.80/1.02      | k1_relat_1(sK3) = u1_struct_0(sK1)
% 1.80/1.02      | k1_xboole_0 = X0 ),
% 1.80/1.02      inference(unflattening,[status(thm)],[c_487]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_688,plain,
% 1.80/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.80/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.80/1.02      | ~ v1_relat_1(sK3)
% 1.80/1.02      | u1_struct_0(sK1) != X1
% 1.80/1.02      | u1_struct_0(sK1) = k1_relat_1(sK3)
% 1.80/1.02      | sK3 != X0
% 1.80/1.02      | k1_xboole_0 = X3 ),
% 1.80/1.02      inference(resolution_lifted,[status(thm)],[c_7,c_488]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_689,plain,
% 1.80/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.80/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X1)))
% 1.80/1.02      | ~ v1_relat_1(sK3)
% 1.80/1.02      | u1_struct_0(sK1) = k1_relat_1(sK3)
% 1.80/1.02      | k1_xboole_0 = X0 ),
% 1.80/1.02      inference(unflattening,[status(thm)],[c_688]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_703,plain,
% 1.80/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.80/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X1)))
% 1.80/1.02      | u1_struct_0(sK1) = k1_relat_1(sK3)
% 1.80/1.02      | k1_xboole_0 = X0 ),
% 1.80/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_689,c_6]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_854,plain,
% 1.80/1.02      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.80/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X1_52)))
% 1.80/1.02      | u1_struct_0(sK1) = k1_relat_1(sK3)
% 1.80/1.02      | k1_xboole_0 = X0_52 ),
% 1.80/1.02      inference(subtyping,[status(esa)],[c_703]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_867,plain,
% 1.80/1.02      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.80/1.02      | k1_xboole_0 = X0_52
% 1.80/1.02      | ~ sP1_iProver_split ),
% 1.80/1.02      inference(splitting,
% 1.80/1.02                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 1.80/1.02                [c_854]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_1105,plain,
% 1.80/1.02      ( k1_xboole_0 = X0_52
% 1.80/1.02      | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.80/1.02      | sP1_iProver_split != iProver_top ),
% 1.80/1.02      inference(predicate_to_equality,[status(thm)],[c_867]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_1158,plain,
% 1.80/1.02      ( k1_xboole_0 = X0_52
% 1.80/1.02      | m1_subset_1(X0_52,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 1.80/1.02      | sP1_iProver_split != iProver_top ),
% 1.80/1.02      inference(light_normalisation,[status(thm)],[c_1105,c_858]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_1567,plain,
% 1.80/1.02      ( k1_xboole_0 = X0_52
% 1.80/1.02      | m1_subset_1(X0_52,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 1.80/1.02      | sP1_iProver_split != iProver_top ),
% 1.80/1.02      inference(demodulation,[status(thm)],[c_1562,c_1158]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_868,plain,
% 1.80/1.02      ( sP1_iProver_split
% 1.80/1.02      | sP0_iProver_split
% 1.80/1.02      | u1_struct_0(sK1) = k1_relat_1(sK3) ),
% 1.80/1.02      inference(splitting,
% 1.80/1.02                [splitting(split),new_symbols(definition,[])],
% 1.80/1.02                [c_854]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_1104,plain,
% 1.80/1.02      ( u1_struct_0(sK1) = k1_relat_1(sK3)
% 1.80/1.02      | sP1_iProver_split = iProver_top
% 1.80/1.02      | sP0_iProver_split = iProver_top ),
% 1.80/1.02      inference(predicate_to_equality,[status(thm)],[c_868]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_1126,plain,
% 1.80/1.02      ( k2_struct_0(sK1) = k1_relat_1(sK3)
% 1.80/1.02      | sP1_iProver_split = iProver_top
% 1.80/1.02      | sP0_iProver_split = iProver_top ),
% 1.80/1.02      inference(demodulation,[status(thm)],[c_1104,c_857]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_1361,plain,
% 1.80/1.02      ( sP1_iProver_split = iProver_top
% 1.80/1.02      | k2_struct_0(sK1) = k1_relat_1(sK3) ),
% 1.80/1.02      inference(global_propositional_subsumption,
% 1.80/1.02                [status(thm)],
% 1.80/1.02                [c_1126,c_28,c_1221]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_1362,plain,
% 1.80/1.02      ( k2_struct_0(sK1) = k1_relat_1(sK3)
% 1.80/1.02      | sP1_iProver_split = iProver_top ),
% 1.80/1.02      inference(renaming,[status(thm)],[c_1361]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_2037,plain,
% 1.80/1.02      ( m1_subset_1(X0_52,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 1.80/1.02      | k1_xboole_0 = X0_52 ),
% 1.80/1.02      inference(global_propositional_subsumption,
% 1.80/1.02                [status(thm)],
% 1.80/1.02                [c_1567,c_1362,c_1531]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_2038,plain,
% 1.80/1.02      ( k1_xboole_0 = X0_52
% 1.80/1.02      | m1_subset_1(X0_52,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.80/1.02      inference(renaming,[status(thm)],[c_2037]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_2098,plain,
% 1.80/1.02      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 1.80/1.02      inference(superposition,[status(thm)],[c_1920,c_2038]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(c_1621,plain,
% 1.80/1.02      ( k1_relat_1(sK3) != k1_xboole_0 ),
% 1.80/1.02      inference(demodulation,[status(thm)],[c_1571,c_1531]) ).
% 1.80/1.02  
% 1.80/1.02  cnf(contradiction,plain,
% 1.80/1.02      ( $false ),
% 1.80/1.02      inference(minisat,[status(thm)],[c_2098,c_1621]) ).
% 1.80/1.02  
% 1.80/1.02  
% 1.80/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 1.80/1.02  
% 1.80/1.02  ------                               Statistics
% 1.80/1.02  
% 1.80/1.02  ------ General
% 1.80/1.02  
% 1.80/1.02  abstr_ref_over_cycles:                  0
% 1.80/1.02  abstr_ref_under_cycles:                 0
% 1.80/1.02  gc_basic_clause_elim:                   0
% 1.80/1.02  forced_gc_time:                         0
% 1.80/1.02  parsing_time:                           0.008
% 1.80/1.02  unif_index_cands_time:                  0.
% 1.80/1.02  unif_index_add_time:                    0.
% 1.80/1.02  orderings_time:                         0.
% 1.80/1.02  out_proof_time:                         0.013
% 1.80/1.02  total_time:                             0.102
% 1.80/1.02  num_of_symbols:                         62
% 1.80/1.02  num_of_terms:                           1523
% 1.80/1.02  
% 1.80/1.02  ------ Preprocessing
% 1.80/1.02  
% 1.80/1.02  num_of_splits:                          6
% 1.80/1.02  num_of_split_atoms:                     3
% 1.80/1.02  num_of_reused_defs:                     3
% 1.80/1.02  num_eq_ax_congr_red:                    40
% 1.80/1.02  num_of_sem_filtered_clauses:            4
% 1.80/1.02  num_of_subtypes:                        4
% 1.80/1.02  monotx_restored_types:                  0
% 1.80/1.02  sat_num_of_epr_types:                   0
% 1.80/1.02  sat_num_of_non_cyclic_types:            0
% 1.80/1.02  sat_guarded_non_collapsed_types:        1
% 1.80/1.02  num_pure_diseq_elim:                    0
% 1.80/1.02  simp_replaced_by:                       0
% 1.80/1.02  res_preprocessed:                       86
% 1.80/1.02  prep_upred:                             0
% 1.80/1.02  prep_unflattend:                        31
% 1.80/1.02  smt_new_axioms:                         0
% 1.80/1.02  pred_elim_cands:                        1
% 1.80/1.02  pred_elim:                              9
% 1.80/1.02  pred_elim_cl:                           10
% 1.80/1.02  pred_elim_cycles:                       13
% 1.80/1.02  merged_defs:                            2
% 1.80/1.02  merged_defs_ncl:                        0
% 1.80/1.02  bin_hyper_res:                          2
% 1.80/1.02  prep_cycles:                            4
% 1.80/1.02  pred_elim_time:                         0.013
% 1.80/1.02  splitting_time:                         0.
% 1.80/1.02  sem_filter_time:                        0.
% 1.80/1.02  monotx_time:                            0.
% 1.80/1.02  subtype_inf_time:                       0.
% 1.80/1.02  
% 1.80/1.02  ------ Problem properties
% 1.80/1.02  
% 1.80/1.02  clauses:                                19
% 1.80/1.02  conjectures:                            3
% 1.80/1.02  epr:                                    0
% 1.80/1.02  horn:                                   15
% 1.80/1.02  ground:                                 9
% 1.80/1.02  unary:                                  4
% 1.80/1.02  binary:                                 9
% 1.80/1.02  lits:                                   42
% 1.80/1.02  lits_eq:                                16
% 1.80/1.02  fd_pure:                                0
% 1.80/1.02  fd_pseudo:                              0
% 1.80/1.02  fd_cond:                                2
% 1.80/1.02  fd_pseudo_cond:                         0
% 1.80/1.02  ac_symbols:                             0
% 1.80/1.02  
% 1.80/1.02  ------ Propositional Solver
% 1.80/1.02  
% 1.80/1.02  prop_solver_calls:                      28
% 1.80/1.02  prop_fast_solver_calls:                 540
% 1.80/1.02  smt_solver_calls:                       0
% 1.80/1.02  smt_fast_solver_calls:                  0
% 1.80/1.02  prop_num_of_clauses:                    670
% 1.80/1.02  prop_preprocess_simplified:             2737
% 1.80/1.02  prop_fo_subsumed:                       11
% 1.80/1.02  prop_solver_time:                       0.
% 1.80/1.02  smt_solver_time:                        0.
% 1.80/1.02  smt_fast_solver_time:                   0.
% 1.80/1.02  prop_fast_solver_time:                  0.
% 1.80/1.02  prop_unsat_core_time:                   0.
% 1.80/1.02  
% 1.80/1.02  ------ QBF
% 1.80/1.02  
% 1.80/1.02  qbf_q_res:                              0
% 1.80/1.02  qbf_num_tautologies:                    0
% 1.80/1.02  qbf_prep_cycles:                        0
% 1.80/1.02  
% 1.80/1.02  ------ BMC1
% 1.80/1.02  
% 1.80/1.02  bmc1_current_bound:                     -1
% 1.80/1.02  bmc1_last_solved_bound:                 -1
% 1.80/1.02  bmc1_unsat_core_size:                   -1
% 1.80/1.02  bmc1_unsat_core_parents_size:           -1
% 1.80/1.02  bmc1_merge_next_fun:                    0
% 1.80/1.02  bmc1_unsat_core_clauses_time:           0.
% 1.80/1.02  
% 1.80/1.02  ------ Instantiation
% 1.80/1.02  
% 1.80/1.02  inst_num_of_clauses:                    223
% 1.80/1.02  inst_num_in_passive:                    95
% 1.80/1.02  inst_num_in_active:                     111
% 1.80/1.02  inst_num_in_unprocessed:                17
% 1.80/1.02  inst_num_of_loops:                      140
% 1.80/1.02  inst_num_of_learning_restarts:          0
% 1.80/1.02  inst_num_moves_active_passive:          25
% 1.80/1.02  inst_lit_activity:                      0
% 1.80/1.02  inst_lit_activity_moves:                0
% 1.80/1.02  inst_num_tautologies:                   0
% 1.80/1.02  inst_num_prop_implied:                  0
% 1.80/1.02  inst_num_existing_simplified:           0
% 1.80/1.02  inst_num_eq_res_simplified:             0
% 1.80/1.02  inst_num_child_elim:                    0
% 1.80/1.02  inst_num_of_dismatching_blockings:      19
% 1.80/1.02  inst_num_of_non_proper_insts:           127
% 1.80/1.02  inst_num_of_duplicates:                 0
% 1.80/1.02  inst_inst_num_from_inst_to_res:         0
% 1.80/1.02  inst_dismatching_checking_time:         0.
% 1.80/1.02  
% 1.80/1.02  ------ Resolution
% 1.80/1.02  
% 1.80/1.02  res_num_of_clauses:                     0
% 1.80/1.02  res_num_in_passive:                     0
% 1.80/1.02  res_num_in_active:                      0
% 1.80/1.02  res_num_of_loops:                       90
% 1.80/1.02  res_forward_subset_subsumed:            27
% 1.80/1.02  res_backward_subset_subsumed:           0
% 1.80/1.02  res_forward_subsumed:                   0
% 1.80/1.02  res_backward_subsumed:                  0
% 1.80/1.02  res_forward_subsumption_resolution:     2
% 1.80/1.02  res_backward_subsumption_resolution:    0
% 1.80/1.02  res_clause_to_clause_subsumption:       51
% 1.80/1.02  res_orphan_elimination:                 0
% 1.80/1.02  res_tautology_del:                      33
% 1.80/1.02  res_num_eq_res_simplified:              0
% 1.80/1.02  res_num_sel_changes:                    0
% 1.80/1.02  res_moves_from_active_to_pass:          0
% 1.80/1.02  
% 1.80/1.02  ------ Superposition
% 1.80/1.02  
% 1.80/1.02  sup_time_total:                         0.
% 1.80/1.02  sup_time_generating:                    0.
% 1.80/1.02  sup_time_sim_full:                      0.
% 1.80/1.02  sup_time_sim_immed:                     0.
% 1.80/1.02  
% 1.80/1.02  sup_num_of_clauses:                     19
% 1.80/1.02  sup_num_in_active:                      17
% 1.80/1.02  sup_num_in_passive:                     2
% 1.80/1.02  sup_num_of_loops:                       26
% 1.80/1.02  sup_fw_superposition:                   3
% 1.80/1.02  sup_bw_superposition:                   5
% 1.80/1.02  sup_immediate_simplified:               5
% 1.80/1.02  sup_given_eliminated:                   0
% 1.80/1.02  comparisons_done:                       0
% 1.80/1.02  comparisons_avoided:                    0
% 1.80/1.02  
% 1.80/1.02  ------ Simplifications
% 1.80/1.02  
% 1.80/1.02  
% 1.80/1.02  sim_fw_subset_subsumed:                 0
% 1.80/1.02  sim_bw_subset_subsumed:                 1
% 1.80/1.02  sim_fw_subsumed:                        0
% 1.80/1.02  sim_bw_subsumed:                        0
% 1.80/1.02  sim_fw_subsumption_res:                 0
% 1.80/1.02  sim_bw_subsumption_res:                 1
% 1.80/1.02  sim_tautology_del:                      0
% 1.80/1.02  sim_eq_tautology_del:                   0
% 1.80/1.02  sim_eq_res_simp:                        1
% 1.80/1.02  sim_fw_demodulated:                     4
% 1.80/1.02  sim_bw_demodulated:                     10
% 1.80/1.02  sim_light_normalised:                   14
% 1.80/1.02  sim_joinable_taut:                      0
% 1.80/1.02  sim_joinable_simp:                      0
% 1.80/1.02  sim_ac_normalised:                      0
% 1.80/1.02  sim_smt_subsumption:                    0
% 1.80/1.02  
%------------------------------------------------------------------------------
