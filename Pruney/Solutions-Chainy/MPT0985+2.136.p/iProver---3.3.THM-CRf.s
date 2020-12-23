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
% DateTime   : Thu Dec  3 12:02:48 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 565 expanded)
%              Number of clauses        :   81 ( 192 expanded)
%              Number of leaves         :   13 ( 106 expanded)
%              Depth                    :   18
%              Number of atoms          :  410 (2966 expanded)
%              Number of equality atoms :  132 ( 533 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
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

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f31,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
        | ~ v1_funct_1(k2_funct_1(sK3)) )
      & k2_relset_1(sK1,sK2,sK3) = sK2
      & v2_funct_1(sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
      | ~ v1_funct_1(k2_funct_1(sK3)) )
    & k2_relset_1(sK1,sK2,sK3) = sK2
    & v2_funct_1(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f26,f31])).

fof(f52,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f54,plain,(
    k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f41,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f53,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f50,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f42,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f39,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f40,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f55,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f32])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK0(X0,X1),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( r1_tarski(sK0(X0,X1),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK0(X0,X1),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r1_tarski(sK0(X0,X1),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f57,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f33])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_925,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1269,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_925])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_928,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | k2_relset_1(X1_47,X2_47,X0_47) = k2_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1267,plain,
    ( k2_relset_1(X0_47,X1_47,X2_47) = k2_relat_1(X2_47)
    | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_928])).

cnf(c_1640,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1269,c_1267])).

cnf(c_18,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_926,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1641,plain,
    ( k2_relat_1(sK3) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_1640,c_926])).

cnf(c_9,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_19,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_306,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_19])).

cnf(c_307,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_306])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_309,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_307,c_22])).

cnf(c_923,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(subtyping,[status(esa)],[c_309])).

cnf(c_1271,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_923])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_931,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | v1_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1402,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_931])).

cnf(c_1413,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1271,c_20,c_923,c_1402])).

cnf(c_1644,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
    inference(demodulation,[status(thm)],[c_1641,c_1413])).

cnf(c_14,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_927,plain,
    ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_47),X1_47)))
    | ~ r1_tarski(k2_relat_1(X0_47),X1_47)
    | ~ v1_relat_1(X0_47)
    | ~ v1_funct_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1268,plain,
    ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_47),X1_47))) = iProver_top
    | r1_tarski(k2_relat_1(X0_47),X1_47) != iProver_top
    | v1_relat_1(X0_47) != iProver_top
    | v1_funct_1(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_927])).

cnf(c_2085,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0_47))) = iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK3)),X0_47) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1644,c_1268])).

cnf(c_8,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_320,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_19])).

cnf(c_321,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_320])).

cnf(c_51,plain,
    ( ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_323,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_321,c_22,c_19,c_51])).

cnf(c_922,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(subtyping,[status(esa)],[c_323])).

cnf(c_1272,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_922])).

cnf(c_1431,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1272,c_20,c_922,c_1402])).

cnf(c_2118,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0_47))) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0_47) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2085,c_1431])).

cnf(c_23,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_25,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_53,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_55,plain,
    ( v1_relat_1(k2_funct_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_53])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_56,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_58,plain,
    ( v1_relat_1(sK3) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_56])).

cnf(c_1403,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1402])).

cnf(c_2449,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0_47))) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0_47) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2118,c_23,c_25,c_55,c_58,c_1403])).

cnf(c_15,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_17,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_340,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relat_1(X0) != sK2
    | k2_funct_1(sK3) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_17])).

cnf(c_341,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1)
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
    inference(unflattening,[status(thm)],[c_340])).

cnf(c_353,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_341,c_10])).

cnf(c_921,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
    inference(subtyping,[status(esa)],[c_353])).

cnf(c_1273,plain,
    ( k1_relat_1(k2_funct_1(sK3)) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_921])).

cnf(c_979,plain,
    ( k1_relat_1(k2_funct_1(sK3)) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_921])).

cnf(c_1456,plain,
    ( r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1273,c_23,c_25,c_58,c_979,c_1403])).

cnf(c_1457,plain,
    ( k1_relat_1(k2_funct_1(sK3)) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_1456])).

cnf(c_1460,plain,
    ( k2_relat_1(sK3) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1457,c_1413,c_1431])).

cnf(c_1643,plain,
    ( sK2 != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1641,c_1460])).

cnf(c_1647,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1643])).

cnf(c_2457,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2449,c_1647])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_929,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | k1_relset_1(X1_47,X2_47,X0_47) = k1_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1266,plain,
    ( k1_relset_1(X0_47,X1_47,X2_47) = k1_relat_1(X2_47)
    | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_929])).

cnf(c_1600,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1269,c_1266])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_930,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | m1_subset_1(k1_relset_1(X1_47,X2_47,X0_47),k1_zfmisc_1(X1_47)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1265,plain,
    ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47))) != iProver_top
    | m1_subset_1(k1_relset_1(X1_47,X2_47,X0_47),k1_zfmisc_1(X1_47)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_930])).

cnf(c_1932,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1600,c_1265])).

cnf(c_2073,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1932,c_25])).

cnf(c_4,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_291,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | k1_zfmisc_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_5])).

cnf(c_292,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(unflattening,[status(thm)],[c_291])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_656,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_657,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_656])).

cnf(c_695,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(bin_hyper_res,[status(thm)],[c_292,c_657])).

cnf(c_919,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(X1_47))
    | r1_tarski(X0_47,X1_47) ),
    inference(subtyping,[status(esa)],[c_695])).

cnf(c_1275,plain,
    ( m1_subset_1(X0_47,k1_zfmisc_1(X1_47)) != iProver_top
    | r1_tarski(X0_47,X1_47) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_919])).

cnf(c_2078,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2073,c_1275])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2457,c_2078])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:19:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.87/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/0.98  
% 1.87/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.87/0.98  
% 1.87/0.98  ------  iProver source info
% 1.87/0.98  
% 1.87/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.87/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.87/0.98  git: non_committed_changes: false
% 1.87/0.98  git: last_make_outside_of_git: false
% 1.87/0.98  
% 1.87/0.98  ------ 
% 1.87/0.98  
% 1.87/0.98  ------ Input Options
% 1.87/0.98  
% 1.87/0.98  --out_options                           all
% 1.87/0.98  --tptp_safe_out                         true
% 1.87/0.98  --problem_path                          ""
% 1.87/0.98  --include_path                          ""
% 1.87/0.98  --clausifier                            res/vclausify_rel
% 1.87/0.98  --clausifier_options                    --mode clausify
% 1.87/0.98  --stdin                                 false
% 1.87/0.98  --stats_out                             all
% 1.87/0.98  
% 1.87/0.98  ------ General Options
% 1.87/0.98  
% 1.87/0.98  --fof                                   false
% 1.87/0.98  --time_out_real                         305.
% 1.87/0.98  --time_out_virtual                      -1.
% 1.87/0.98  --symbol_type_check                     false
% 1.87/0.98  --clausify_out                          false
% 1.87/0.98  --sig_cnt_out                           false
% 1.87/0.98  --trig_cnt_out                          false
% 1.87/0.98  --trig_cnt_out_tolerance                1.
% 1.87/0.98  --trig_cnt_out_sk_spl                   false
% 1.87/0.98  --abstr_cl_out                          false
% 1.87/0.98  
% 1.87/0.98  ------ Global Options
% 1.87/0.98  
% 1.87/0.98  --schedule                              default
% 1.87/0.98  --add_important_lit                     false
% 1.87/0.98  --prop_solver_per_cl                    1000
% 1.87/0.98  --min_unsat_core                        false
% 1.87/0.98  --soft_assumptions                      false
% 1.87/0.98  --soft_lemma_size                       3
% 1.87/0.98  --prop_impl_unit_size                   0
% 1.87/0.98  --prop_impl_unit                        []
% 1.87/0.98  --share_sel_clauses                     true
% 1.87/0.98  --reset_solvers                         false
% 1.87/0.98  --bc_imp_inh                            [conj_cone]
% 1.87/0.98  --conj_cone_tolerance                   3.
% 1.87/0.98  --extra_neg_conj                        none
% 1.87/0.98  --large_theory_mode                     true
% 1.87/0.98  --prolific_symb_bound                   200
% 1.87/0.98  --lt_threshold                          2000
% 1.87/0.98  --clause_weak_htbl                      true
% 1.87/0.98  --gc_record_bc_elim                     false
% 1.87/0.98  
% 1.87/0.98  ------ Preprocessing Options
% 1.87/0.98  
% 1.87/0.98  --preprocessing_flag                    true
% 1.87/0.98  --time_out_prep_mult                    0.1
% 1.87/0.98  --splitting_mode                        input
% 1.87/0.98  --splitting_grd                         true
% 1.87/0.98  --splitting_cvd                         false
% 1.87/0.98  --splitting_cvd_svl                     false
% 1.87/0.98  --splitting_nvd                         32
% 1.87/0.98  --sub_typing                            true
% 1.87/0.98  --prep_gs_sim                           true
% 1.87/0.98  --prep_unflatten                        true
% 1.87/0.98  --prep_res_sim                          true
% 1.87/0.98  --prep_upred                            true
% 1.87/0.98  --prep_sem_filter                       exhaustive
% 1.87/0.98  --prep_sem_filter_out                   false
% 1.87/0.98  --pred_elim                             true
% 1.87/0.98  --res_sim_input                         true
% 1.87/0.98  --eq_ax_congr_red                       true
% 1.87/0.98  --pure_diseq_elim                       true
% 1.87/0.98  --brand_transform                       false
% 1.87/0.98  --non_eq_to_eq                          false
% 1.87/0.98  --prep_def_merge                        true
% 1.87/0.98  --prep_def_merge_prop_impl              false
% 1.87/0.98  --prep_def_merge_mbd                    true
% 1.87/0.98  --prep_def_merge_tr_red                 false
% 1.87/0.98  --prep_def_merge_tr_cl                  false
% 1.87/0.98  --smt_preprocessing                     true
% 1.87/0.98  --smt_ac_axioms                         fast
% 1.87/0.98  --preprocessed_out                      false
% 1.87/0.98  --preprocessed_stats                    false
% 1.87/0.98  
% 1.87/0.98  ------ Abstraction refinement Options
% 1.87/0.98  
% 1.87/0.98  --abstr_ref                             []
% 1.87/0.98  --abstr_ref_prep                        false
% 1.87/0.98  --abstr_ref_until_sat                   false
% 1.87/0.98  --abstr_ref_sig_restrict                funpre
% 1.87/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.87/0.98  --abstr_ref_under                       []
% 1.87/0.98  
% 1.87/0.98  ------ SAT Options
% 1.87/0.98  
% 1.87/0.98  --sat_mode                              false
% 1.87/0.98  --sat_fm_restart_options                ""
% 1.87/0.98  --sat_gr_def                            false
% 1.87/0.98  --sat_epr_types                         true
% 1.87/0.98  --sat_non_cyclic_types                  false
% 1.87/0.98  --sat_finite_models                     false
% 1.87/0.98  --sat_fm_lemmas                         false
% 1.87/0.98  --sat_fm_prep                           false
% 1.87/0.98  --sat_fm_uc_incr                        true
% 1.87/0.98  --sat_out_model                         small
% 1.87/0.98  --sat_out_clauses                       false
% 1.87/0.98  
% 1.87/0.98  ------ QBF Options
% 1.87/0.98  
% 1.87/0.98  --qbf_mode                              false
% 1.87/0.98  --qbf_elim_univ                         false
% 1.87/0.98  --qbf_dom_inst                          none
% 1.87/0.98  --qbf_dom_pre_inst                      false
% 1.87/0.98  --qbf_sk_in                             false
% 1.87/0.98  --qbf_pred_elim                         true
% 1.87/0.98  --qbf_split                             512
% 1.87/0.98  
% 1.87/0.98  ------ BMC1 Options
% 1.87/0.98  
% 1.87/0.98  --bmc1_incremental                      false
% 1.87/0.98  --bmc1_axioms                           reachable_all
% 1.87/0.98  --bmc1_min_bound                        0
% 1.87/0.98  --bmc1_max_bound                        -1
% 1.87/0.98  --bmc1_max_bound_default                -1
% 1.87/0.98  --bmc1_symbol_reachability              true
% 1.87/0.98  --bmc1_property_lemmas                  false
% 1.87/0.98  --bmc1_k_induction                      false
% 1.87/0.98  --bmc1_non_equiv_states                 false
% 1.87/0.98  --bmc1_deadlock                         false
% 1.87/0.98  --bmc1_ucm                              false
% 1.87/0.98  --bmc1_add_unsat_core                   none
% 1.87/0.98  --bmc1_unsat_core_children              false
% 1.87/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.87/0.98  --bmc1_out_stat                         full
% 1.87/0.98  --bmc1_ground_init                      false
% 1.87/0.98  --bmc1_pre_inst_next_state              false
% 1.87/0.98  --bmc1_pre_inst_state                   false
% 1.87/0.98  --bmc1_pre_inst_reach_state             false
% 1.87/0.98  --bmc1_out_unsat_core                   false
% 1.87/0.98  --bmc1_aig_witness_out                  false
% 1.87/0.98  --bmc1_verbose                          false
% 1.87/0.98  --bmc1_dump_clauses_tptp                false
% 1.87/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.87/0.98  --bmc1_dump_file                        -
% 1.87/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.87/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.87/0.98  --bmc1_ucm_extend_mode                  1
% 1.87/0.98  --bmc1_ucm_init_mode                    2
% 1.87/0.98  --bmc1_ucm_cone_mode                    none
% 1.87/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.87/0.98  --bmc1_ucm_relax_model                  4
% 1.87/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.87/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.87/0.98  --bmc1_ucm_layered_model                none
% 1.87/0.98  --bmc1_ucm_max_lemma_size               10
% 1.87/0.98  
% 1.87/0.98  ------ AIG Options
% 1.87/0.98  
% 1.87/0.98  --aig_mode                              false
% 1.87/0.98  
% 1.87/0.98  ------ Instantiation Options
% 1.87/0.98  
% 1.87/0.98  --instantiation_flag                    true
% 1.87/0.98  --inst_sos_flag                         false
% 1.87/0.98  --inst_sos_phase                        true
% 1.87/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.87/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.87/0.98  --inst_lit_sel_side                     num_symb
% 1.87/0.98  --inst_solver_per_active                1400
% 1.87/0.98  --inst_solver_calls_frac                1.
% 1.87/0.98  --inst_passive_queue_type               priority_queues
% 1.87/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.87/0.98  --inst_passive_queues_freq              [25;2]
% 1.87/0.98  --inst_dismatching                      true
% 1.87/0.98  --inst_eager_unprocessed_to_passive     true
% 1.87/0.98  --inst_prop_sim_given                   true
% 1.87/0.98  --inst_prop_sim_new                     false
% 1.87/0.98  --inst_subs_new                         false
% 1.87/0.98  --inst_eq_res_simp                      false
% 1.87/0.98  --inst_subs_given                       false
% 1.87/0.98  --inst_orphan_elimination               true
% 1.87/0.98  --inst_learning_loop_flag               true
% 1.87/0.98  --inst_learning_start                   3000
% 1.87/0.98  --inst_learning_factor                  2
% 1.87/0.98  --inst_start_prop_sim_after_learn       3
% 1.87/0.98  --inst_sel_renew                        solver
% 1.87/0.98  --inst_lit_activity_flag                true
% 1.87/0.98  --inst_restr_to_given                   false
% 1.87/0.98  --inst_activity_threshold               500
% 1.87/0.98  --inst_out_proof                        true
% 1.87/0.98  
% 1.87/0.98  ------ Resolution Options
% 1.87/0.98  
% 1.87/0.98  --resolution_flag                       true
% 1.87/0.98  --res_lit_sel                           adaptive
% 1.87/0.98  --res_lit_sel_side                      none
% 1.87/0.98  --res_ordering                          kbo
% 1.87/0.98  --res_to_prop_solver                    active
% 1.87/0.98  --res_prop_simpl_new                    false
% 1.87/0.98  --res_prop_simpl_given                  true
% 1.87/0.98  --res_passive_queue_type                priority_queues
% 1.87/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.87/0.98  --res_passive_queues_freq               [15;5]
% 1.87/0.98  --res_forward_subs                      full
% 1.87/0.98  --res_backward_subs                     full
% 1.87/0.98  --res_forward_subs_resolution           true
% 1.87/0.98  --res_backward_subs_resolution          true
% 1.87/0.98  --res_orphan_elimination                true
% 1.87/0.98  --res_time_limit                        2.
% 1.87/0.98  --res_out_proof                         true
% 1.87/0.98  
% 1.87/0.98  ------ Superposition Options
% 1.87/0.98  
% 1.87/0.98  --superposition_flag                    true
% 1.87/0.98  --sup_passive_queue_type                priority_queues
% 1.87/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.87/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.87/0.98  --demod_completeness_check              fast
% 1.87/0.98  --demod_use_ground                      true
% 1.87/0.98  --sup_to_prop_solver                    passive
% 1.87/0.98  --sup_prop_simpl_new                    true
% 1.87/0.98  --sup_prop_simpl_given                  true
% 1.87/0.98  --sup_fun_splitting                     false
% 1.87/0.98  --sup_smt_interval                      50000
% 1.87/0.98  
% 1.87/0.98  ------ Superposition Simplification Setup
% 1.87/0.98  
% 1.87/0.98  --sup_indices_passive                   []
% 1.87/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.87/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/0.98  --sup_full_bw                           [BwDemod]
% 1.87/0.98  --sup_immed_triv                        [TrivRules]
% 1.87/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.87/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/0.98  --sup_immed_bw_main                     []
% 1.87/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.87/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.87/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.87/0.98  
% 1.87/0.98  ------ Combination Options
% 1.87/0.98  
% 1.87/0.98  --comb_res_mult                         3
% 1.87/0.98  --comb_sup_mult                         2
% 1.87/0.98  --comb_inst_mult                        10
% 1.87/0.98  
% 1.87/0.98  ------ Debug Options
% 1.87/0.98  
% 1.87/0.98  --dbg_backtrace                         false
% 1.87/0.98  --dbg_dump_prop_clauses                 false
% 1.87/0.98  --dbg_dump_prop_clauses_file            -
% 1.87/0.98  --dbg_out_stat                          false
% 1.87/0.98  ------ Parsing...
% 1.87/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.87/0.98  
% 1.87/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 1.87/0.98  
% 1.87/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.87/0.98  
% 1.87/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.87/0.98  ------ Proving...
% 1.87/0.98  ------ Problem Properties 
% 1.87/0.98  
% 1.87/0.98  
% 1.87/0.98  clauses                                 17
% 1.87/0.98  conjectures                             3
% 1.87/0.98  EPR                                     1
% 1.87/0.98  Horn                                    16
% 1.87/0.98  unary                                   3
% 1.87/0.98  binary                                  7
% 1.87/0.98  lits                                    41
% 1.87/0.98  lits eq                                 10
% 1.87/0.98  fd_pure                                 0
% 1.87/0.98  fd_pseudo                               0
% 1.87/0.98  fd_cond                                 0
% 1.87/0.98  fd_pseudo_cond                          0
% 1.87/0.98  AC symbols                              0
% 1.87/0.98  
% 1.87/0.98  ------ Schedule dynamic 5 is on 
% 1.87/0.98  
% 1.87/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.87/0.98  
% 1.87/0.98  
% 1.87/0.98  ------ 
% 1.87/0.98  Current options:
% 1.87/0.98  ------ 
% 1.87/0.98  
% 1.87/0.98  ------ Input Options
% 1.87/0.98  
% 1.87/0.98  --out_options                           all
% 1.87/0.98  --tptp_safe_out                         true
% 1.87/0.98  --problem_path                          ""
% 1.87/0.98  --include_path                          ""
% 1.87/0.98  --clausifier                            res/vclausify_rel
% 1.87/0.98  --clausifier_options                    --mode clausify
% 1.87/0.98  --stdin                                 false
% 1.87/0.98  --stats_out                             all
% 1.87/0.98  
% 1.87/0.98  ------ General Options
% 1.87/0.98  
% 1.87/0.98  --fof                                   false
% 1.87/0.98  --time_out_real                         305.
% 1.87/0.98  --time_out_virtual                      -1.
% 1.87/0.98  --symbol_type_check                     false
% 1.87/0.98  --clausify_out                          false
% 1.87/0.98  --sig_cnt_out                           false
% 1.87/0.98  --trig_cnt_out                          false
% 1.87/0.98  --trig_cnt_out_tolerance                1.
% 1.87/0.98  --trig_cnt_out_sk_spl                   false
% 1.87/0.98  --abstr_cl_out                          false
% 1.87/0.98  
% 1.87/0.98  ------ Global Options
% 1.87/0.98  
% 1.87/0.98  --schedule                              default
% 1.87/0.98  --add_important_lit                     false
% 1.87/0.98  --prop_solver_per_cl                    1000
% 1.87/0.98  --min_unsat_core                        false
% 1.87/0.98  --soft_assumptions                      false
% 1.87/0.98  --soft_lemma_size                       3
% 1.87/0.98  --prop_impl_unit_size                   0
% 1.87/0.98  --prop_impl_unit                        []
% 1.87/0.98  --share_sel_clauses                     true
% 1.87/0.98  --reset_solvers                         false
% 1.87/0.98  --bc_imp_inh                            [conj_cone]
% 1.87/0.98  --conj_cone_tolerance                   3.
% 1.87/0.98  --extra_neg_conj                        none
% 1.87/0.98  --large_theory_mode                     true
% 1.87/0.98  --prolific_symb_bound                   200
% 1.87/0.98  --lt_threshold                          2000
% 1.87/0.98  --clause_weak_htbl                      true
% 1.87/0.98  --gc_record_bc_elim                     false
% 1.87/0.98  
% 1.87/0.98  ------ Preprocessing Options
% 1.87/0.98  
% 1.87/0.98  --preprocessing_flag                    true
% 1.87/0.98  --time_out_prep_mult                    0.1
% 1.87/0.98  --splitting_mode                        input
% 1.87/0.98  --splitting_grd                         true
% 1.87/0.98  --splitting_cvd                         false
% 1.87/0.98  --splitting_cvd_svl                     false
% 1.87/0.98  --splitting_nvd                         32
% 1.87/0.98  --sub_typing                            true
% 1.87/0.98  --prep_gs_sim                           true
% 1.87/0.98  --prep_unflatten                        true
% 1.87/0.98  --prep_res_sim                          true
% 1.87/0.98  --prep_upred                            true
% 1.87/0.98  --prep_sem_filter                       exhaustive
% 1.87/0.98  --prep_sem_filter_out                   false
% 1.87/0.98  --pred_elim                             true
% 1.87/0.98  --res_sim_input                         true
% 1.87/0.98  --eq_ax_congr_red                       true
% 1.87/0.98  --pure_diseq_elim                       true
% 1.87/0.98  --brand_transform                       false
% 1.87/0.98  --non_eq_to_eq                          false
% 1.87/0.98  --prep_def_merge                        true
% 1.87/0.98  --prep_def_merge_prop_impl              false
% 1.87/0.98  --prep_def_merge_mbd                    true
% 1.87/0.98  --prep_def_merge_tr_red                 false
% 1.87/0.98  --prep_def_merge_tr_cl                  false
% 1.87/0.98  --smt_preprocessing                     true
% 1.87/0.98  --smt_ac_axioms                         fast
% 1.87/0.98  --preprocessed_out                      false
% 1.87/0.98  --preprocessed_stats                    false
% 1.87/0.98  
% 1.87/0.98  ------ Abstraction refinement Options
% 1.87/0.98  
% 1.87/0.98  --abstr_ref                             []
% 1.87/0.98  --abstr_ref_prep                        false
% 1.87/0.98  --abstr_ref_until_sat                   false
% 1.87/0.98  --abstr_ref_sig_restrict                funpre
% 1.87/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.87/0.98  --abstr_ref_under                       []
% 1.87/0.98  
% 1.87/0.98  ------ SAT Options
% 1.87/0.98  
% 1.87/0.98  --sat_mode                              false
% 1.87/0.98  --sat_fm_restart_options                ""
% 1.87/0.98  --sat_gr_def                            false
% 1.87/0.98  --sat_epr_types                         true
% 1.87/0.98  --sat_non_cyclic_types                  false
% 1.87/0.98  --sat_finite_models                     false
% 1.87/0.98  --sat_fm_lemmas                         false
% 1.87/0.98  --sat_fm_prep                           false
% 1.87/0.98  --sat_fm_uc_incr                        true
% 1.87/0.98  --sat_out_model                         small
% 1.87/0.98  --sat_out_clauses                       false
% 1.87/0.98  
% 1.87/0.98  ------ QBF Options
% 1.87/0.98  
% 1.87/0.98  --qbf_mode                              false
% 1.87/0.98  --qbf_elim_univ                         false
% 1.87/0.98  --qbf_dom_inst                          none
% 1.87/0.98  --qbf_dom_pre_inst                      false
% 1.87/0.98  --qbf_sk_in                             false
% 1.87/0.98  --qbf_pred_elim                         true
% 1.87/0.98  --qbf_split                             512
% 1.87/0.98  
% 1.87/0.98  ------ BMC1 Options
% 1.87/0.98  
% 1.87/0.98  --bmc1_incremental                      false
% 1.87/0.98  --bmc1_axioms                           reachable_all
% 1.87/0.98  --bmc1_min_bound                        0
% 1.87/0.98  --bmc1_max_bound                        -1
% 1.87/0.98  --bmc1_max_bound_default                -1
% 1.87/0.98  --bmc1_symbol_reachability              true
% 1.87/0.98  --bmc1_property_lemmas                  false
% 1.87/0.98  --bmc1_k_induction                      false
% 1.87/0.98  --bmc1_non_equiv_states                 false
% 1.87/0.98  --bmc1_deadlock                         false
% 1.87/0.98  --bmc1_ucm                              false
% 1.87/0.98  --bmc1_add_unsat_core                   none
% 1.87/0.98  --bmc1_unsat_core_children              false
% 1.87/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.87/0.98  --bmc1_out_stat                         full
% 1.87/0.98  --bmc1_ground_init                      false
% 1.87/0.98  --bmc1_pre_inst_next_state              false
% 1.87/0.98  --bmc1_pre_inst_state                   false
% 1.87/0.98  --bmc1_pre_inst_reach_state             false
% 1.87/0.98  --bmc1_out_unsat_core                   false
% 1.87/0.98  --bmc1_aig_witness_out                  false
% 1.87/0.98  --bmc1_verbose                          false
% 1.87/0.98  --bmc1_dump_clauses_tptp                false
% 1.87/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.87/0.98  --bmc1_dump_file                        -
% 1.87/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.87/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.87/0.98  --bmc1_ucm_extend_mode                  1
% 1.87/0.98  --bmc1_ucm_init_mode                    2
% 1.87/0.98  --bmc1_ucm_cone_mode                    none
% 1.87/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.87/0.98  --bmc1_ucm_relax_model                  4
% 1.87/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.87/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.87/0.98  --bmc1_ucm_layered_model                none
% 1.87/0.98  --bmc1_ucm_max_lemma_size               10
% 1.87/0.98  
% 1.87/0.98  ------ AIG Options
% 1.87/0.98  
% 1.87/0.98  --aig_mode                              false
% 1.87/0.98  
% 1.87/0.98  ------ Instantiation Options
% 1.87/0.98  
% 1.87/0.98  --instantiation_flag                    true
% 1.87/0.98  --inst_sos_flag                         false
% 1.87/0.98  --inst_sos_phase                        true
% 1.87/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.87/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.87/0.98  --inst_lit_sel_side                     none
% 1.87/0.98  --inst_solver_per_active                1400
% 1.87/0.98  --inst_solver_calls_frac                1.
% 1.87/0.98  --inst_passive_queue_type               priority_queues
% 1.87/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.87/0.98  --inst_passive_queues_freq              [25;2]
% 1.87/0.98  --inst_dismatching                      true
% 1.87/0.98  --inst_eager_unprocessed_to_passive     true
% 1.87/0.98  --inst_prop_sim_given                   true
% 1.87/0.98  --inst_prop_sim_new                     false
% 1.87/0.98  --inst_subs_new                         false
% 1.87/0.98  --inst_eq_res_simp                      false
% 1.87/0.98  --inst_subs_given                       false
% 1.87/0.98  --inst_orphan_elimination               true
% 1.87/0.98  --inst_learning_loop_flag               true
% 1.87/0.98  --inst_learning_start                   3000
% 1.87/0.98  --inst_learning_factor                  2
% 1.87/0.98  --inst_start_prop_sim_after_learn       3
% 1.87/0.98  --inst_sel_renew                        solver
% 1.87/0.98  --inst_lit_activity_flag                true
% 1.87/0.98  --inst_restr_to_given                   false
% 1.87/0.98  --inst_activity_threshold               500
% 1.87/0.98  --inst_out_proof                        true
% 1.87/0.98  
% 1.87/0.98  ------ Resolution Options
% 1.87/0.98  
% 1.87/0.98  --resolution_flag                       false
% 1.87/0.98  --res_lit_sel                           adaptive
% 1.87/0.98  --res_lit_sel_side                      none
% 1.87/0.98  --res_ordering                          kbo
% 1.87/0.98  --res_to_prop_solver                    active
% 1.87/0.98  --res_prop_simpl_new                    false
% 1.87/0.98  --res_prop_simpl_given                  true
% 1.87/0.98  --res_passive_queue_type                priority_queues
% 1.87/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.87/0.98  --res_passive_queues_freq               [15;5]
% 1.87/0.98  --res_forward_subs                      full
% 1.87/0.98  --res_backward_subs                     full
% 1.87/0.98  --res_forward_subs_resolution           true
% 1.87/0.98  --res_backward_subs_resolution          true
% 1.87/0.98  --res_orphan_elimination                true
% 1.87/0.98  --res_time_limit                        2.
% 1.87/0.98  --res_out_proof                         true
% 1.87/0.98  
% 1.87/0.98  ------ Superposition Options
% 1.87/0.98  
% 1.87/0.98  --superposition_flag                    true
% 1.87/0.98  --sup_passive_queue_type                priority_queues
% 1.87/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.87/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.87/0.99  --demod_completeness_check              fast
% 1.87/0.99  --demod_use_ground                      true
% 1.87/0.99  --sup_to_prop_solver                    passive
% 1.87/0.99  --sup_prop_simpl_new                    true
% 1.87/0.99  --sup_prop_simpl_given                  true
% 1.87/0.99  --sup_fun_splitting                     false
% 1.87/0.99  --sup_smt_interval                      50000
% 1.87/0.99  
% 1.87/0.99  ------ Superposition Simplification Setup
% 1.87/0.99  
% 1.87/0.99  --sup_indices_passive                   []
% 1.87/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.87/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/0.99  --sup_full_bw                           [BwDemod]
% 1.87/0.99  --sup_immed_triv                        [TrivRules]
% 1.87/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.87/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/0.99  --sup_immed_bw_main                     []
% 1.87/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.87/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.87/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.87/0.99  
% 1.87/0.99  ------ Combination Options
% 1.87/0.99  
% 1.87/0.99  --comb_res_mult                         3
% 1.87/0.99  --comb_sup_mult                         2
% 1.87/0.99  --comb_inst_mult                        10
% 1.87/0.99  
% 1.87/0.99  ------ Debug Options
% 1.87/0.99  
% 1.87/0.99  --dbg_backtrace                         false
% 1.87/0.99  --dbg_dump_prop_clauses                 false
% 1.87/0.99  --dbg_dump_prop_clauses_file            -
% 1.87/0.99  --dbg_out_stat                          false
% 1.87/0.99  
% 1.87/0.99  
% 1.87/0.99  
% 1.87/0.99  
% 1.87/0.99  ------ Proving...
% 1.87/0.99  
% 1.87/0.99  
% 1.87/0.99  % SZS status Theorem for theBenchmark.p
% 1.87/0.99  
% 1.87/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.87/0.99  
% 1.87/0.99  fof(f11,conjecture,(
% 1.87/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.87/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.87/0.99  
% 1.87/0.99  fof(f12,negated_conjecture,(
% 1.87/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.87/0.99    inference(negated_conjecture,[],[f11])).
% 1.87/0.99  
% 1.87/0.99  fof(f25,plain,(
% 1.87/0.99    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.87/0.99    inference(ennf_transformation,[],[f12])).
% 1.87/0.99  
% 1.87/0.99  fof(f26,plain,(
% 1.87/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.87/0.99    inference(flattening,[],[f25])).
% 1.87/0.99  
% 1.87/0.99  fof(f31,plain,(
% 1.87/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 1.87/0.99    introduced(choice_axiom,[])).
% 1.87/0.99  
% 1.87/0.99  fof(f32,plain,(
% 1.87/0.99    (~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 1.87/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f26,f31])).
% 1.87/0.99  
% 1.87/0.99  fof(f52,plain,(
% 1.87/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.87/0.99    inference(cnf_transformation,[],[f32])).
% 1.87/0.99  
% 1.87/0.99  fof(f9,axiom,(
% 1.87/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 1.87/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.87/0.99  
% 1.87/0.99  fof(f22,plain,(
% 1.87/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.87/0.99    inference(ennf_transformation,[],[f9])).
% 1.87/0.99  
% 1.87/0.99  fof(f46,plain,(
% 1.87/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.87/0.99    inference(cnf_transformation,[],[f22])).
% 1.87/0.99  
% 1.87/0.99  fof(f54,plain,(
% 1.87/0.99    k2_relset_1(sK1,sK2,sK3) = sK2),
% 1.87/0.99    inference(cnf_transformation,[],[f32])).
% 1.87/0.99  
% 1.87/0.99  fof(f5,axiom,(
% 1.87/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.87/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.87/0.99  
% 1.87/0.99  fof(f17,plain,(
% 1.87/0.99    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.87/0.99    inference(ennf_transformation,[],[f5])).
% 1.87/0.99  
% 1.87/0.99  fof(f18,plain,(
% 1.87/0.99    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.87/0.99    inference(flattening,[],[f17])).
% 1.87/0.99  
% 1.87/0.99  fof(f41,plain,(
% 1.87/0.99    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.87/0.99    inference(cnf_transformation,[],[f18])).
% 1.87/0.99  
% 1.87/0.99  fof(f53,plain,(
% 1.87/0.99    v2_funct_1(sK3)),
% 1.87/0.99    inference(cnf_transformation,[],[f32])).
% 1.87/0.99  
% 1.87/0.99  fof(f50,plain,(
% 1.87/0.99    v1_funct_1(sK3)),
% 1.87/0.99    inference(cnf_transformation,[],[f32])).
% 1.87/0.99  
% 1.87/0.99  fof(f6,axiom,(
% 1.87/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.87/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.87/0.99  
% 1.87/0.99  fof(f19,plain,(
% 1.87/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.87/0.99    inference(ennf_transformation,[],[f6])).
% 1.87/0.99  
% 1.87/0.99  fof(f43,plain,(
% 1.87/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.87/0.99    inference(cnf_transformation,[],[f19])).
% 1.87/0.99  
% 1.87/0.99  fof(f10,axiom,(
% 1.87/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.87/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.87/0.99  
% 1.87/0.99  fof(f23,plain,(
% 1.87/0.99    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.87/0.99    inference(ennf_transformation,[],[f10])).
% 1.87/0.99  
% 1.87/0.99  fof(f24,plain,(
% 1.87/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.87/0.99    inference(flattening,[],[f23])).
% 1.87/0.99  
% 1.87/0.99  fof(f49,plain,(
% 1.87/0.99    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.87/0.99    inference(cnf_transformation,[],[f24])).
% 1.87/0.99  
% 1.87/0.99  fof(f42,plain,(
% 1.87/0.99    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.87/0.99    inference(cnf_transformation,[],[f18])).
% 1.87/0.99  
% 1.87/0.99  fof(f4,axiom,(
% 1.87/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.87/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.87/0.99  
% 1.87/0.99  fof(f15,plain,(
% 1.87/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.87/0.99    inference(ennf_transformation,[],[f4])).
% 1.87/0.99  
% 1.87/0.99  fof(f16,plain,(
% 1.87/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.87/0.99    inference(flattening,[],[f15])).
% 1.87/0.99  
% 1.87/0.99  fof(f39,plain,(
% 1.87/0.99    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.87/0.99    inference(cnf_transformation,[],[f16])).
% 1.87/0.99  
% 1.87/0.99  fof(f40,plain,(
% 1.87/0.99    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.87/0.99    inference(cnf_transformation,[],[f16])).
% 1.87/0.99  
% 1.87/0.99  fof(f48,plain,(
% 1.87/0.99    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.87/0.99    inference(cnf_transformation,[],[f24])).
% 1.87/0.99  
% 1.87/0.99  fof(f55,plain,(
% 1.87/0.99    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 1.87/0.99    inference(cnf_transformation,[],[f32])).
% 1.87/0.99  
% 1.87/0.99  fof(f8,axiom,(
% 1.87/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.87/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.87/0.99  
% 1.87/0.99  fof(f21,plain,(
% 1.87/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.87/0.99    inference(ennf_transformation,[],[f8])).
% 1.87/0.99  
% 1.87/0.99  fof(f45,plain,(
% 1.87/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.87/0.99    inference(cnf_transformation,[],[f21])).
% 1.87/0.99  
% 1.87/0.99  fof(f7,axiom,(
% 1.87/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.87/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.87/0.99  
% 1.87/0.99  fof(f20,plain,(
% 1.87/0.99    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.87/0.99    inference(ennf_transformation,[],[f7])).
% 1.87/0.99  
% 1.87/0.99  fof(f44,plain,(
% 1.87/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.87/0.99    inference(cnf_transformation,[],[f20])).
% 1.87/0.99  
% 1.87/0.99  fof(f2,axiom,(
% 1.87/0.99    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.87/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.87/0.99  
% 1.87/0.99  fof(f37,plain,(
% 1.87/0.99    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.87/0.99    inference(cnf_transformation,[],[f2])).
% 1.87/0.99  
% 1.87/0.99  fof(f3,axiom,(
% 1.87/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.87/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.87/0.99  
% 1.87/0.99  fof(f13,plain,(
% 1.87/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.87/0.99    inference(ennf_transformation,[],[f3])).
% 1.87/0.99  
% 1.87/0.99  fof(f14,plain,(
% 1.87/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.87/0.99    inference(flattening,[],[f13])).
% 1.87/0.99  
% 1.87/0.99  fof(f38,plain,(
% 1.87/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.87/0.99    inference(cnf_transformation,[],[f14])).
% 1.87/0.99  
% 1.87/0.99  fof(f1,axiom,(
% 1.87/0.99    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.87/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.87/0.99  
% 1.87/0.99  fof(f27,plain,(
% 1.87/0.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.87/0.99    inference(nnf_transformation,[],[f1])).
% 1.87/0.99  
% 1.87/0.99  fof(f28,plain,(
% 1.87/0.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.87/0.99    inference(rectify,[],[f27])).
% 1.87/0.99  
% 1.87/0.99  fof(f29,plain,(
% 1.87/0.99    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 1.87/0.99    introduced(choice_axiom,[])).
% 1.87/0.99  
% 1.87/0.99  fof(f30,plain,(
% 1.87/0.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.87/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 1.87/0.99  
% 1.87/0.99  fof(f33,plain,(
% 1.87/0.99    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.87/0.99    inference(cnf_transformation,[],[f30])).
% 1.87/0.99  
% 1.87/0.99  fof(f57,plain,(
% 1.87/0.99    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 1.87/0.99    inference(equality_resolution,[],[f33])).
% 1.87/0.99  
% 1.87/0.99  cnf(c_20,negated_conjecture,
% 1.87/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 1.87/0.99      inference(cnf_transformation,[],[f52]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_925,negated_conjecture,
% 1.87/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 1.87/0.99      inference(subtyping,[status(esa)],[c_20]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1269,plain,
% 1.87/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_925]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_13,plain,
% 1.87/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.87/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 1.87/0.99      inference(cnf_transformation,[],[f46]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_928,plain,
% 1.87/0.99      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
% 1.87/0.99      | k2_relset_1(X1_47,X2_47,X0_47) = k2_relat_1(X0_47) ),
% 1.87/0.99      inference(subtyping,[status(esa)],[c_13]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1267,plain,
% 1.87/0.99      ( k2_relset_1(X0_47,X1_47,X2_47) = k2_relat_1(X2_47)
% 1.87/0.99      | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_928]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1640,plain,
% 1.87/0.99      ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 1.87/0.99      inference(superposition,[status(thm)],[c_1269,c_1267]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_18,negated_conjecture,
% 1.87/0.99      ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
% 1.87/0.99      inference(cnf_transformation,[],[f54]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_926,negated_conjecture,
% 1.87/0.99      ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
% 1.87/0.99      inference(subtyping,[status(esa)],[c_18]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1641,plain,
% 1.87/0.99      ( k2_relat_1(sK3) = sK2 ),
% 1.87/0.99      inference(light_normalisation,[status(thm)],[c_1640,c_926]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_9,plain,
% 1.87/0.99      ( ~ v2_funct_1(X0)
% 1.87/0.99      | ~ v1_relat_1(X0)
% 1.87/0.99      | ~ v1_funct_1(X0)
% 1.87/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 1.87/0.99      inference(cnf_transformation,[],[f41]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_19,negated_conjecture,
% 1.87/0.99      ( v2_funct_1(sK3) ),
% 1.87/0.99      inference(cnf_transformation,[],[f53]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_306,plain,
% 1.87/0.99      ( ~ v1_relat_1(X0)
% 1.87/0.99      | ~ v1_funct_1(X0)
% 1.87/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 1.87/0.99      | sK3 != X0 ),
% 1.87/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_19]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_307,plain,
% 1.87/0.99      ( ~ v1_relat_1(sK3)
% 1.87/0.99      | ~ v1_funct_1(sK3)
% 1.87/0.99      | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 1.87/0.99      inference(unflattening,[status(thm)],[c_306]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_22,negated_conjecture,
% 1.87/0.99      ( v1_funct_1(sK3) ),
% 1.87/0.99      inference(cnf_transformation,[],[f50]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_309,plain,
% 1.87/0.99      ( ~ v1_relat_1(sK3)
% 1.87/0.99      | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 1.87/0.99      inference(global_propositional_subsumption,
% 1.87/0.99                [status(thm)],
% 1.87/0.99                [c_307,c_22]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_923,plain,
% 1.87/0.99      ( ~ v1_relat_1(sK3)
% 1.87/0.99      | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 1.87/0.99      inference(subtyping,[status(esa)],[c_309]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1271,plain,
% 1.87/0.99      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
% 1.87/0.99      | v1_relat_1(sK3) != iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_923]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_10,plain,
% 1.87/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.87/0.99      | v1_relat_1(X0) ),
% 1.87/0.99      inference(cnf_transformation,[],[f43]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_931,plain,
% 1.87/0.99      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
% 1.87/0.99      | v1_relat_1(X0_47) ),
% 1.87/0.99      inference(subtyping,[status(esa)],[c_10]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1402,plain,
% 1.87/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 1.87/0.99      | v1_relat_1(sK3) ),
% 1.87/0.99      inference(instantiation,[status(thm)],[c_931]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1413,plain,
% 1.87/0.99      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 1.87/0.99      inference(global_propositional_subsumption,
% 1.87/0.99                [status(thm)],
% 1.87/0.99                [c_1271,c_20,c_923,c_1402]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1644,plain,
% 1.87/0.99      ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
% 1.87/0.99      inference(demodulation,[status(thm)],[c_1641,c_1413]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_14,plain,
% 1.87/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 1.87/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 1.87/0.99      | ~ v1_relat_1(X0)
% 1.87/0.99      | ~ v1_funct_1(X0) ),
% 1.87/0.99      inference(cnf_transformation,[],[f49]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_927,plain,
% 1.87/0.99      ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_47),X1_47)))
% 1.87/0.99      | ~ r1_tarski(k2_relat_1(X0_47),X1_47)
% 1.87/0.99      | ~ v1_relat_1(X0_47)
% 1.87/0.99      | ~ v1_funct_1(X0_47) ),
% 1.87/0.99      inference(subtyping,[status(esa)],[c_14]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1268,plain,
% 1.87/0.99      ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_47),X1_47))) = iProver_top
% 1.87/0.99      | r1_tarski(k2_relat_1(X0_47),X1_47) != iProver_top
% 1.87/0.99      | v1_relat_1(X0_47) != iProver_top
% 1.87/0.99      | v1_funct_1(X0_47) != iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_927]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2085,plain,
% 1.87/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0_47))) = iProver_top
% 1.87/0.99      | r1_tarski(k2_relat_1(k2_funct_1(sK3)),X0_47) != iProver_top
% 1.87/0.99      | v1_relat_1(k2_funct_1(sK3)) != iProver_top
% 1.87/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 1.87/0.99      inference(superposition,[status(thm)],[c_1644,c_1268]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_8,plain,
% 1.87/0.99      ( ~ v2_funct_1(X0)
% 1.87/0.99      | ~ v1_relat_1(X0)
% 1.87/0.99      | ~ v1_funct_1(X0)
% 1.87/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 1.87/0.99      inference(cnf_transformation,[],[f42]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_320,plain,
% 1.87/0.99      ( ~ v1_relat_1(X0)
% 1.87/0.99      | ~ v1_funct_1(X0)
% 1.87/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 1.87/0.99      | sK3 != X0 ),
% 1.87/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_19]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_321,plain,
% 1.87/0.99      ( ~ v1_relat_1(sK3)
% 1.87/0.99      | ~ v1_funct_1(sK3)
% 1.87/0.99      | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 1.87/0.99      inference(unflattening,[status(thm)],[c_320]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_51,plain,
% 1.87/0.99      ( ~ v2_funct_1(sK3)
% 1.87/0.99      | ~ v1_relat_1(sK3)
% 1.87/0.99      | ~ v1_funct_1(sK3)
% 1.87/0.99      | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 1.87/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_323,plain,
% 1.87/0.99      ( ~ v1_relat_1(sK3)
% 1.87/0.99      | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 1.87/0.99      inference(global_propositional_subsumption,
% 1.87/0.99                [status(thm)],
% 1.87/0.99                [c_321,c_22,c_19,c_51]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_922,plain,
% 1.87/0.99      ( ~ v1_relat_1(sK3)
% 1.87/0.99      | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 1.87/0.99      inference(subtyping,[status(esa)],[c_323]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1272,plain,
% 1.87/0.99      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
% 1.87/0.99      | v1_relat_1(sK3) != iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_922]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1431,plain,
% 1.87/0.99      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 1.87/0.99      inference(global_propositional_subsumption,
% 1.87/0.99                [status(thm)],
% 1.87/0.99                [c_1272,c_20,c_922,c_1402]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2118,plain,
% 1.87/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0_47))) = iProver_top
% 1.87/0.99      | r1_tarski(k1_relat_1(sK3),X0_47) != iProver_top
% 1.87/0.99      | v1_relat_1(k2_funct_1(sK3)) != iProver_top
% 1.87/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 1.87/0.99      inference(light_normalisation,[status(thm)],[c_2085,c_1431]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_23,plain,
% 1.87/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_25,plain,
% 1.87/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_7,plain,
% 1.87/0.99      ( ~ v1_relat_1(X0)
% 1.87/0.99      | v1_relat_1(k2_funct_1(X0))
% 1.87/0.99      | ~ v1_funct_1(X0) ),
% 1.87/0.99      inference(cnf_transformation,[],[f39]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_53,plain,
% 1.87/0.99      ( v1_relat_1(X0) != iProver_top
% 1.87/0.99      | v1_relat_1(k2_funct_1(X0)) = iProver_top
% 1.87/0.99      | v1_funct_1(X0) != iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_55,plain,
% 1.87/0.99      ( v1_relat_1(k2_funct_1(sK3)) = iProver_top
% 1.87/0.99      | v1_relat_1(sK3) != iProver_top
% 1.87/0.99      | v1_funct_1(sK3) != iProver_top ),
% 1.87/0.99      inference(instantiation,[status(thm)],[c_53]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_6,plain,
% 1.87/0.99      ( ~ v1_relat_1(X0)
% 1.87/0.99      | ~ v1_funct_1(X0)
% 1.87/0.99      | v1_funct_1(k2_funct_1(X0)) ),
% 1.87/0.99      inference(cnf_transformation,[],[f40]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_56,plain,
% 1.87/0.99      ( v1_relat_1(X0) != iProver_top
% 1.87/0.99      | v1_funct_1(X0) != iProver_top
% 1.87/0.99      | v1_funct_1(k2_funct_1(X0)) = iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_58,plain,
% 1.87/0.99      ( v1_relat_1(sK3) != iProver_top
% 1.87/0.99      | v1_funct_1(k2_funct_1(sK3)) = iProver_top
% 1.87/0.99      | v1_funct_1(sK3) != iProver_top ),
% 1.87/0.99      inference(instantiation,[status(thm)],[c_56]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1403,plain,
% 1.87/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 1.87/0.99      | v1_relat_1(sK3) = iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_1402]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2449,plain,
% 1.87/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0_47))) = iProver_top
% 1.87/0.99      | r1_tarski(k1_relat_1(sK3),X0_47) != iProver_top ),
% 1.87/0.99      inference(global_propositional_subsumption,
% 1.87/0.99                [status(thm)],
% 1.87/0.99                [c_2118,c_23,c_25,c_55,c_58,c_1403]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_15,plain,
% 1.87/0.99      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 1.87/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 1.87/0.99      | ~ v1_relat_1(X0)
% 1.87/0.99      | ~ v1_funct_1(X0) ),
% 1.87/0.99      inference(cnf_transformation,[],[f48]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_17,negated_conjecture,
% 1.87/0.99      ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
% 1.87/0.99      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 1.87/0.99      | ~ v1_funct_1(k2_funct_1(sK3)) ),
% 1.87/0.99      inference(cnf_transformation,[],[f55]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_340,plain,
% 1.87/0.99      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 1.87/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 1.87/0.99      | ~ v1_relat_1(X0)
% 1.87/0.99      | ~ v1_funct_1(X0)
% 1.87/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 1.87/0.99      | k1_relat_1(X0) != sK2
% 1.87/0.99      | k2_funct_1(sK3) != X0
% 1.87/0.99      | sK1 != X1 ),
% 1.87/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_17]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_341,plain,
% 1.87/0.99      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 1.87/0.99      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1)
% 1.87/0.99      | ~ v1_relat_1(k2_funct_1(sK3))
% 1.87/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 1.87/0.99      | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
% 1.87/0.99      inference(unflattening,[status(thm)],[c_340]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_353,plain,
% 1.87/0.99      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 1.87/0.99      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1)
% 1.87/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 1.87/0.99      | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
% 1.87/0.99      inference(forward_subsumption_resolution,
% 1.87/0.99                [status(thm)],
% 1.87/0.99                [c_341,c_10]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_921,plain,
% 1.87/0.99      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 1.87/0.99      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1)
% 1.87/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 1.87/0.99      | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
% 1.87/0.99      inference(subtyping,[status(esa)],[c_353]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1273,plain,
% 1.87/0.99      ( k1_relat_1(k2_funct_1(sK3)) != sK2
% 1.87/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 1.87/0.99      | r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1) != iProver_top
% 1.87/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_921]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_979,plain,
% 1.87/0.99      ( k1_relat_1(k2_funct_1(sK3)) != sK2
% 1.87/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 1.87/0.99      | r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1) != iProver_top
% 1.87/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_921]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1456,plain,
% 1.87/0.99      ( r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1) != iProver_top
% 1.87/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 1.87/0.99      | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
% 1.87/0.99      inference(global_propositional_subsumption,
% 1.87/0.99                [status(thm)],
% 1.87/0.99                [c_1273,c_23,c_25,c_58,c_979,c_1403]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1457,plain,
% 1.87/0.99      ( k1_relat_1(k2_funct_1(sK3)) != sK2
% 1.87/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 1.87/0.99      | r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1) != iProver_top ),
% 1.87/0.99      inference(renaming,[status(thm)],[c_1456]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1460,plain,
% 1.87/0.99      ( k2_relat_1(sK3) != sK2
% 1.87/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 1.87/0.99      | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
% 1.87/0.99      inference(light_normalisation,[status(thm)],[c_1457,c_1413,c_1431]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1643,plain,
% 1.87/0.99      ( sK2 != sK2
% 1.87/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 1.87/0.99      | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
% 1.87/0.99      inference(demodulation,[status(thm)],[c_1641,c_1460]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1647,plain,
% 1.87/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 1.87/0.99      | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
% 1.87/0.99      inference(equality_resolution_simp,[status(thm)],[c_1643]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2457,plain,
% 1.87/0.99      ( r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
% 1.87/0.99      inference(superposition,[status(thm)],[c_2449,c_1647]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_12,plain,
% 1.87/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.87/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.87/0.99      inference(cnf_transformation,[],[f45]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_929,plain,
% 1.87/0.99      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
% 1.87/0.99      | k1_relset_1(X1_47,X2_47,X0_47) = k1_relat_1(X0_47) ),
% 1.87/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1266,plain,
% 1.87/0.99      ( k1_relset_1(X0_47,X1_47,X2_47) = k1_relat_1(X2_47)
% 1.87/0.99      | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_929]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1600,plain,
% 1.87/0.99      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 1.87/0.99      inference(superposition,[status(thm)],[c_1269,c_1266]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_11,plain,
% 1.87/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.87/0.99      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 1.87/0.99      inference(cnf_transformation,[],[f44]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_930,plain,
% 1.87/0.99      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
% 1.87/0.99      | m1_subset_1(k1_relset_1(X1_47,X2_47,X0_47),k1_zfmisc_1(X1_47)) ),
% 1.87/0.99      inference(subtyping,[status(esa)],[c_11]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1265,plain,
% 1.87/0.99      ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47))) != iProver_top
% 1.87/0.99      | m1_subset_1(k1_relset_1(X1_47,X2_47,X0_47),k1_zfmisc_1(X1_47)) = iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_930]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1932,plain,
% 1.87/0.99      ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1)) = iProver_top
% 1.87/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 1.87/0.99      inference(superposition,[status(thm)],[c_1600,c_1265]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2073,plain,
% 1.87/0.99      ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1)) = iProver_top ),
% 1.87/0.99      inference(global_propositional_subsumption,
% 1.87/0.99                [status(thm)],
% 1.87/0.99                [c_1932,c_25]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_4,plain,
% 1.87/0.99      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 1.87/0.99      inference(cnf_transformation,[],[f37]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_5,plain,
% 1.87/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 1.87/0.99      inference(cnf_transformation,[],[f38]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_291,plain,
% 1.87/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | k1_zfmisc_1(X2) != X1 ),
% 1.87/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_5]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_292,plain,
% 1.87/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.87/0.99      | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 1.87/0.99      inference(unflattening,[status(thm)],[c_291]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3,plain,
% 1.87/0.99      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 1.87/0.99      inference(cnf_transformation,[],[f57]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_656,plain,
% 1.87/0.99      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 1.87/0.99      inference(prop_impl,[status(thm)],[c_3]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_657,plain,
% 1.87/0.99      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 1.87/0.99      inference(renaming,[status(thm)],[c_656]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_695,plain,
% 1.87/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 1.87/0.99      inference(bin_hyper_res,[status(thm)],[c_292,c_657]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_919,plain,
% 1.87/0.99      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(X1_47))
% 1.87/0.99      | r1_tarski(X0_47,X1_47) ),
% 1.87/0.99      inference(subtyping,[status(esa)],[c_695]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1275,plain,
% 1.87/0.99      ( m1_subset_1(X0_47,k1_zfmisc_1(X1_47)) != iProver_top
% 1.87/0.99      | r1_tarski(X0_47,X1_47) = iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_919]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2078,plain,
% 1.87/0.99      ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
% 1.87/0.99      inference(superposition,[status(thm)],[c_2073,c_1275]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(contradiction,plain,
% 1.87/0.99      ( $false ),
% 1.87/0.99      inference(minisat,[status(thm)],[c_2457,c_2078]) ).
% 1.87/0.99  
% 1.87/0.99  
% 1.87/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.87/0.99  
% 1.87/0.99  ------                               Statistics
% 1.87/0.99  
% 1.87/0.99  ------ General
% 1.87/0.99  
% 1.87/0.99  abstr_ref_over_cycles:                  0
% 1.87/0.99  abstr_ref_under_cycles:                 0
% 1.87/0.99  gc_basic_clause_elim:                   0
% 1.87/0.99  forced_gc_time:                         0
% 1.87/0.99  parsing_time:                           0.009
% 1.87/0.99  unif_index_cands_time:                  0.
% 1.87/0.99  unif_index_add_time:                    0.
% 1.87/0.99  orderings_time:                         0.
% 1.87/0.99  out_proof_time:                         0.009
% 1.87/0.99  total_time:                             0.098
% 1.87/0.99  num_of_symbols:                         52
% 1.87/0.99  num_of_terms:                           1779
% 1.87/0.99  
% 1.87/0.99  ------ Preprocessing
% 1.87/0.99  
% 1.87/0.99  num_of_splits:                          0
% 1.87/0.99  num_of_split_atoms:                     0
% 1.87/0.99  num_of_reused_defs:                     0
% 1.87/0.99  num_eq_ax_congr_red:                    19
% 1.87/0.99  num_of_sem_filtered_clauses:            1
% 1.87/0.99  num_of_subtypes:                        2
% 1.87/0.99  monotx_restored_types:                  0
% 1.87/0.99  sat_num_of_epr_types:                   0
% 1.87/0.99  sat_num_of_non_cyclic_types:            0
% 1.87/0.99  sat_guarded_non_collapsed_types:        0
% 1.87/0.99  num_pure_diseq_elim:                    0
% 1.87/0.99  simp_replaced_by:                       0
% 1.87/0.99  res_preprocessed:                       123
% 1.87/0.99  prep_upred:                             0
% 1.87/0.99  prep_unflattend:                        25
% 1.87/0.99  smt_new_axioms:                         0
% 1.87/0.99  pred_elim_cands:                        4
% 1.87/0.99  pred_elim:                              4
% 1.87/0.99  pred_elim_cl:                           5
% 1.87/0.99  pred_elim_cycles:                       8
% 1.87/0.99  merged_defs:                            4
% 1.87/0.99  merged_defs_ncl:                        0
% 1.87/0.99  bin_hyper_res:                          5
% 1.87/0.99  prep_cycles:                            5
% 1.87/0.99  pred_elim_time:                         0.008
% 1.87/0.99  splitting_time:                         0.
% 1.87/0.99  sem_filter_time:                        0.
% 1.87/0.99  monotx_time:                            0.
% 1.87/0.99  subtype_inf_time:                       0.
% 1.87/0.99  
% 1.87/0.99  ------ Problem properties
% 1.87/0.99  
% 1.87/0.99  clauses:                                17
% 1.87/0.99  conjectures:                            3
% 1.87/0.99  epr:                                    1
% 1.87/0.99  horn:                                   16
% 1.87/0.99  ground:                                 7
% 1.87/0.99  unary:                                  3
% 1.87/0.99  binary:                                 7
% 1.87/0.99  lits:                                   41
% 1.87/0.99  lits_eq:                                10
% 1.87/0.99  fd_pure:                                0
% 1.87/0.99  fd_pseudo:                              0
% 1.87/0.99  fd_cond:                                0
% 1.87/0.99  fd_pseudo_cond:                         0
% 1.87/0.99  ac_symbols:                             0
% 1.87/0.99  
% 1.87/0.99  ------ Propositional Solver
% 1.87/0.99  
% 1.87/0.99  prop_solver_calls:                      31
% 1.87/0.99  prop_fast_solver_calls:                 740
% 1.87/0.99  smt_solver_calls:                       0
% 1.87/0.99  smt_fast_solver_calls:                  0
% 1.87/0.99  prop_num_of_clauses:                    679
% 1.87/0.99  prop_preprocess_simplified:             3553
% 1.87/0.99  prop_fo_subsumed:                       11
% 1.87/0.99  prop_solver_time:                       0.
% 1.87/0.99  smt_solver_time:                        0.
% 1.87/0.99  smt_fast_solver_time:                   0.
% 1.87/0.99  prop_fast_solver_time:                  0.
% 1.87/0.99  prop_unsat_core_time:                   0.
% 1.87/0.99  
% 1.87/0.99  ------ QBF
% 1.87/0.99  
% 1.87/0.99  qbf_q_res:                              0
% 1.87/0.99  qbf_num_tautologies:                    0
% 1.87/0.99  qbf_prep_cycles:                        0
% 1.87/0.99  
% 1.87/0.99  ------ BMC1
% 1.87/0.99  
% 1.87/0.99  bmc1_current_bound:                     -1
% 1.87/0.99  bmc1_last_solved_bound:                 -1
% 1.87/0.99  bmc1_unsat_core_size:                   -1
% 1.87/0.99  bmc1_unsat_core_parents_size:           -1
% 1.87/0.99  bmc1_merge_next_fun:                    0
% 1.87/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.87/0.99  
% 1.87/0.99  ------ Instantiation
% 1.87/0.99  
% 1.87/0.99  inst_num_of_clauses:                    193
% 1.87/0.99  inst_num_in_passive:                    8
% 1.87/0.99  inst_num_in_active:                     126
% 1.87/0.99  inst_num_in_unprocessed:                59
% 1.87/0.99  inst_num_of_loops:                      140
% 1.87/0.99  inst_num_of_learning_restarts:          0
% 1.87/0.99  inst_num_moves_active_passive:          11
% 1.87/0.99  inst_lit_activity:                      0
% 1.87/0.99  inst_lit_activity_moves:                0
% 1.87/0.99  inst_num_tautologies:                   0
% 1.87/0.99  inst_num_prop_implied:                  0
% 1.87/0.99  inst_num_existing_simplified:           0
% 1.87/0.99  inst_num_eq_res_simplified:             0
% 1.87/0.99  inst_num_child_elim:                    0
% 1.87/0.99  inst_num_of_dismatching_blockings:      105
% 1.87/0.99  inst_num_of_non_proper_insts:           189
% 1.87/0.99  inst_num_of_duplicates:                 0
% 1.87/0.99  inst_inst_num_from_inst_to_res:         0
% 1.87/0.99  inst_dismatching_checking_time:         0.
% 1.87/0.99  
% 1.87/0.99  ------ Resolution
% 1.87/0.99  
% 1.87/0.99  res_num_of_clauses:                     0
% 1.87/0.99  res_num_in_passive:                     0
% 1.87/0.99  res_num_in_active:                      0
% 1.87/0.99  res_num_of_loops:                       128
% 1.87/0.99  res_forward_subset_subsumed:            38
% 1.87/0.99  res_backward_subset_subsumed:           0
% 1.87/0.99  res_forward_subsumed:                   0
% 1.87/0.99  res_backward_subsumed:                  0
% 1.87/0.99  res_forward_subsumption_resolution:     1
% 1.87/0.99  res_backward_subsumption_resolution:    0
% 1.87/0.99  res_clause_to_clause_subsumption:       65
% 1.87/0.99  res_orphan_elimination:                 0
% 1.87/0.99  res_tautology_del:                      51
% 1.87/0.99  res_num_eq_res_simplified:              0
% 1.87/0.99  res_num_sel_changes:                    0
% 1.87/0.99  res_moves_from_active_to_pass:          0
% 1.87/0.99  
% 1.87/0.99  ------ Superposition
% 1.87/0.99  
% 1.87/0.99  sup_time_total:                         0.
% 1.87/0.99  sup_time_generating:                    0.
% 1.87/0.99  sup_time_sim_full:                      0.
% 1.87/0.99  sup_time_sim_immed:                     0.
% 1.87/0.99  
% 1.87/0.99  sup_num_of_clauses:                     36
% 1.87/0.99  sup_num_in_active:                      26
% 1.87/0.99  sup_num_in_passive:                     10
% 1.87/0.99  sup_num_of_loops:                       27
% 1.87/0.99  sup_fw_superposition:                   11
% 1.87/0.99  sup_bw_superposition:                   15
% 1.87/0.99  sup_immediate_simplified:               4
% 1.87/0.99  sup_given_eliminated:                   0
% 1.87/0.99  comparisons_done:                       0
% 1.87/0.99  comparisons_avoided:                    0
% 1.87/0.99  
% 1.87/0.99  ------ Simplifications
% 1.87/0.99  
% 1.87/0.99  
% 1.87/0.99  sim_fw_subset_subsumed:                 0
% 1.87/0.99  sim_bw_subset_subsumed:                 0
% 1.87/0.99  sim_fw_subsumed:                        0
% 1.87/0.99  sim_bw_subsumed:                        0
% 1.87/0.99  sim_fw_subsumption_res:                 0
% 1.87/0.99  sim_bw_subsumption_res:                 0
% 1.87/0.99  sim_tautology_del:                      1
% 1.87/0.99  sim_eq_tautology_del:                   0
% 1.87/0.99  sim_eq_res_simp:                        1
% 1.87/0.99  sim_fw_demodulated:                     0
% 1.87/0.99  sim_bw_demodulated:                     2
% 1.87/0.99  sim_light_normalised:                   7
% 1.87/0.99  sim_joinable_taut:                      0
% 1.87/0.99  sim_joinable_simp:                      0
% 1.87/0.99  sim_ac_normalised:                      0
% 1.87/0.99  sim_smt_subsumption:                    0
% 1.87/0.99  
%------------------------------------------------------------------------------
