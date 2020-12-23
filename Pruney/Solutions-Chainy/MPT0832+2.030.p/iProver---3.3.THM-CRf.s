%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:55:51 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 189 expanded)
%              Number of clauses        :   65 (  93 expanded)
%              Number of leaves         :   16 (  32 expanded)
%              Depth                    :   20
%              Number of atoms          :  275 ( 422 expanded)
%              Number of equality atoms :   68 (  80 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
       => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f29,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f34,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
   => ( ~ m1_subset_1(k6_relset_1(sK3,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ~ m1_subset_1(k6_relset_1(sK3,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f29,f34])).

fof(f52,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f35])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f53,plain,(
    ~ m1_subset_1(k6_relset_1(sK3,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f55,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k8_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_648,plain,
    ( ~ v1_relat_1(X0_45)
    | v1_relat_1(k8_relat_1(X1_45,X0_45)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_950,plain,
    ( v1_relat_1(X0_45) != iProver_top
    | v1_relat_1(k8_relat_1(X1_45,X0_45)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_648])).

cnf(c_10,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_646,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X0_45,X1_45)),X0_45)
    | ~ v1_relat_1(X1_45) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_952,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X0_45,X1_45)),X0_45) = iProver_top
    | v1_relat_1(X1_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_646])).

cnf(c_15,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_641,plain,
    ( m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X1_45,X2_45)))
    | ~ r1_tarski(k1_relat_1(X0_45),X1_45)
    | ~ r1_tarski(k2_relat_1(X0_45),X2_45)
    | ~ v1_relat_1(X0_45) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_957,plain,
    ( m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X1_45,X2_45))) = iProver_top
    | r1_tarski(k1_relat_1(X0_45),X1_45) != iProver_top
    | r1_tarski(k2_relat_1(X0_45),X2_45) != iProver_top
    | v1_relat_1(X0_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_641])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_639,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_959,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_639])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k6_relset_1(X1,X2,X3,X0) = k8_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_642,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X1_45,X2_45)))
    | k6_relset_1(X1_45,X2_45,X3_45,X0_45) = k8_relat_1(X3_45,X0_45) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_956,plain,
    ( k6_relset_1(X0_45,X1_45,X2_45,X3_45) = k8_relat_1(X2_45,X3_45)
    | m1_subset_1(X3_45,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_642])).

cnf(c_1683,plain,
    ( k6_relset_1(sK3,sK1,X0_45,sK4) = k8_relat_1(X0_45,sK4) ),
    inference(superposition,[status(thm)],[c_959,c_956])).

cnf(c_16,negated_conjecture,
    ( ~ m1_subset_1(k6_relset_1(sK3,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_640,negated_conjecture,
    ( ~ m1_subset_1(k6_relset_1(sK3,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_958,plain,
    ( m1_subset_1(k6_relset_1(sK3,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_640])).

cnf(c_1796,plain,
    ( m1_subset_1(k8_relat_1(sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1683,c_958])).

cnf(c_2096,plain,
    ( r1_tarski(k1_relat_1(k8_relat_1(sK2,sK4)),sK3) != iProver_top
    | r1_tarski(k2_relat_1(k8_relat_1(sK2,sK4)),sK2) != iProver_top
    | v1_relat_1(k8_relat_1(sK2,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_957,c_1796])).

cnf(c_11,plain,
    ( r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_645,plain,
    ( r1_tarski(k1_relat_1(k8_relat_1(X0_45,X1_45)),k1_relat_1(X1_45))
    | ~ v1_relat_1(X1_45) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_953,plain,
    ( r1_tarski(k1_relat_1(k8_relat_1(X0_45,X1_45)),k1_relat_1(X1_45)) = iProver_top
    | v1_relat_1(X1_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_645])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_643,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X1_45,X2_45)))
    | k1_relset_1(X1_45,X2_45,X0_45) = k1_relat_1(X0_45) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_955,plain,
    ( k1_relset_1(X0_45,X1_45,X2_45) = k1_relat_1(X2_45)
    | m1_subset_1(X2_45,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_643])).

cnf(c_1367,plain,
    ( k1_relset_1(sK3,sK1,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_959,c_955])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_644,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X1_45,X2_45)))
    | m1_subset_1(k1_relset_1(X1_45,X2_45,X0_45),k1_zfmisc_1(X1_45)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_954,plain,
    ( m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X1_45,X2_45))) != iProver_top
    | m1_subset_1(k1_relset_1(X1_45,X2_45,X0_45),k1_zfmisc_1(X1_45)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_644])).

cnf(c_1696,plain,
    ( m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(sK3)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1367,c_954])).

cnf(c_18,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1980,plain,
    ( m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1696,c_18])).

cnf(c_5,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_249,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | k1_zfmisc_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_6])).

cnf(c_250,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(unflattening,[status(thm)],[c_249])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_393,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_394,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_393])).

cnf(c_427,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(bin_hyper_res,[status(thm)],[c_250,c_394])).

cnf(c_638,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(X1_45))
    | r1_tarski(X0_45,X1_45) ),
    inference(subtyping,[status(esa)],[c_427])).

cnf(c_960,plain,
    ( m1_subset_1(X0_45,k1_zfmisc_1(X1_45)) != iProver_top
    | r1_tarski(X0_45,X1_45) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_638])).

cnf(c_1986,plain,
    ( r1_tarski(k1_relat_1(sK4),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1980,c_960])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_650,plain,
    ( ~ r1_tarski(X0_45,X1_45)
    | ~ r1_tarski(X2_45,X0_45)
    | r1_tarski(X2_45,X1_45) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_948,plain,
    ( r1_tarski(X0_45,X1_45) != iProver_top
    | r1_tarski(X2_45,X0_45) != iProver_top
    | r1_tarski(X2_45,X1_45) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_650])).

cnf(c_1997,plain,
    ( r1_tarski(X0_45,k1_relat_1(sK4)) != iProver_top
    | r1_tarski(X0_45,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1986,c_948])).

cnf(c_2402,plain,
    ( r1_tarski(k1_relat_1(k8_relat_1(X0_45,sK4)),sK3) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_953,c_1997])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_649,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(X1_45))
    | ~ v1_relat_1(X1_45)
    | v1_relat_1(X0_45) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1065,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X1_45,X2_45)))
    | v1_relat_1(X0_45)
    | ~ v1_relat_1(k2_zfmisc_1(X1_45,X2_45)) ),
    inference(instantiation,[status(thm)],[c_649])).

cnf(c_1183,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK3,sK1))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1065])).

cnf(c_1184,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK3,sK1)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1183])).

cnf(c_9,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_647,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_45,X1_45)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1229,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK1)) ),
    inference(instantiation,[status(thm)],[c_647])).

cnf(c_1230,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1229])).

cnf(c_2419,plain,
    ( r1_tarski(k1_relat_1(k8_relat_1(X0_45,sK4)),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2402,c_18,c_1184,c_1230])).

cnf(c_2890,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(sK2,sK4)),sK2) != iProver_top
    | v1_relat_1(k8_relat_1(sK2,sK4)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2096,c_2419])).

cnf(c_2892,plain,
    ( v1_relat_1(k8_relat_1(sK2,sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_952,c_2890])).

cnf(c_3176,plain,
    ( v1_relat_1(k8_relat_1(sK2,sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2892,c_18,c_1184,c_1230])).

cnf(c_3181,plain,
    ( v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_950,c_3176])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3181,c_1230,c_1184,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:05:17 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.52/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/0.96  
% 2.52/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.52/0.96  
% 2.52/0.96  ------  iProver source info
% 2.52/0.96  
% 2.52/0.96  git: date: 2020-06-30 10:37:57 +0100
% 2.52/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.52/0.96  git: non_committed_changes: false
% 2.52/0.96  git: last_make_outside_of_git: false
% 2.52/0.96  
% 2.52/0.96  ------ 
% 2.52/0.96  
% 2.52/0.96  ------ Input Options
% 2.52/0.96  
% 2.52/0.96  --out_options                           all
% 2.52/0.96  --tptp_safe_out                         true
% 2.52/0.96  --problem_path                          ""
% 2.52/0.96  --include_path                          ""
% 2.52/0.96  --clausifier                            res/vclausify_rel
% 2.52/0.96  --clausifier_options                    --mode clausify
% 2.52/0.96  --stdin                                 false
% 2.52/0.96  --stats_out                             all
% 2.52/0.96  
% 2.52/0.96  ------ General Options
% 2.52/0.96  
% 2.52/0.96  --fof                                   false
% 2.52/0.96  --time_out_real                         305.
% 2.52/0.96  --time_out_virtual                      -1.
% 2.52/0.96  --symbol_type_check                     false
% 2.52/0.96  --clausify_out                          false
% 2.52/0.96  --sig_cnt_out                           false
% 2.52/0.96  --trig_cnt_out                          false
% 2.52/0.96  --trig_cnt_out_tolerance                1.
% 2.52/0.96  --trig_cnt_out_sk_spl                   false
% 2.52/0.96  --abstr_cl_out                          false
% 2.52/0.96  
% 2.52/0.96  ------ Global Options
% 2.52/0.96  
% 2.52/0.96  --schedule                              default
% 2.52/0.96  --add_important_lit                     false
% 2.52/0.96  --prop_solver_per_cl                    1000
% 2.52/0.96  --min_unsat_core                        false
% 2.52/0.96  --soft_assumptions                      false
% 2.52/0.96  --soft_lemma_size                       3
% 2.52/0.96  --prop_impl_unit_size                   0
% 2.52/0.96  --prop_impl_unit                        []
% 2.52/0.96  --share_sel_clauses                     true
% 2.52/0.96  --reset_solvers                         false
% 2.52/0.96  --bc_imp_inh                            [conj_cone]
% 2.52/0.96  --conj_cone_tolerance                   3.
% 2.52/0.96  --extra_neg_conj                        none
% 2.52/0.96  --large_theory_mode                     true
% 2.52/0.96  --prolific_symb_bound                   200
% 2.52/0.96  --lt_threshold                          2000
% 2.52/0.96  --clause_weak_htbl                      true
% 2.52/0.96  --gc_record_bc_elim                     false
% 2.52/0.96  
% 2.52/0.96  ------ Preprocessing Options
% 2.52/0.96  
% 2.52/0.96  --preprocessing_flag                    true
% 2.52/0.96  --time_out_prep_mult                    0.1
% 2.52/0.96  --splitting_mode                        input
% 2.52/0.96  --splitting_grd                         true
% 2.52/0.96  --splitting_cvd                         false
% 2.52/0.96  --splitting_cvd_svl                     false
% 2.52/0.96  --splitting_nvd                         32
% 2.52/0.96  --sub_typing                            true
% 2.52/0.96  --prep_gs_sim                           true
% 2.52/0.96  --prep_unflatten                        true
% 2.52/0.96  --prep_res_sim                          true
% 2.52/0.96  --prep_upred                            true
% 2.52/0.96  --prep_sem_filter                       exhaustive
% 2.52/0.96  --prep_sem_filter_out                   false
% 2.52/0.96  --pred_elim                             true
% 2.52/0.96  --res_sim_input                         true
% 2.52/0.96  --eq_ax_congr_red                       true
% 2.52/0.96  --pure_diseq_elim                       true
% 2.52/0.96  --brand_transform                       false
% 2.52/0.96  --non_eq_to_eq                          false
% 2.52/0.96  --prep_def_merge                        true
% 2.52/0.96  --prep_def_merge_prop_impl              false
% 2.52/0.96  --prep_def_merge_mbd                    true
% 2.52/0.96  --prep_def_merge_tr_red                 false
% 2.52/0.96  --prep_def_merge_tr_cl                  false
% 2.52/0.96  --smt_preprocessing                     true
% 2.52/0.96  --smt_ac_axioms                         fast
% 2.52/0.96  --preprocessed_out                      false
% 2.52/0.96  --preprocessed_stats                    false
% 2.52/0.96  
% 2.52/0.96  ------ Abstraction refinement Options
% 2.52/0.96  
% 2.52/0.96  --abstr_ref                             []
% 2.52/0.96  --abstr_ref_prep                        false
% 2.52/0.96  --abstr_ref_until_sat                   false
% 2.52/0.96  --abstr_ref_sig_restrict                funpre
% 2.52/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 2.52/0.96  --abstr_ref_under                       []
% 2.52/0.96  
% 2.52/0.96  ------ SAT Options
% 2.52/0.96  
% 2.52/0.96  --sat_mode                              false
% 2.52/0.96  --sat_fm_restart_options                ""
% 2.52/0.96  --sat_gr_def                            false
% 2.52/0.96  --sat_epr_types                         true
% 2.52/0.96  --sat_non_cyclic_types                  false
% 2.52/0.96  --sat_finite_models                     false
% 2.52/0.96  --sat_fm_lemmas                         false
% 2.52/0.96  --sat_fm_prep                           false
% 2.52/0.96  --sat_fm_uc_incr                        true
% 2.52/0.96  --sat_out_model                         small
% 2.52/0.96  --sat_out_clauses                       false
% 2.52/0.96  
% 2.52/0.96  ------ QBF Options
% 2.52/0.96  
% 2.52/0.96  --qbf_mode                              false
% 2.52/0.96  --qbf_elim_univ                         false
% 2.52/0.96  --qbf_dom_inst                          none
% 2.52/0.96  --qbf_dom_pre_inst                      false
% 2.52/0.96  --qbf_sk_in                             false
% 2.52/0.96  --qbf_pred_elim                         true
% 2.52/0.96  --qbf_split                             512
% 2.52/0.96  
% 2.52/0.96  ------ BMC1 Options
% 2.52/0.96  
% 2.52/0.96  --bmc1_incremental                      false
% 2.52/0.96  --bmc1_axioms                           reachable_all
% 2.52/0.96  --bmc1_min_bound                        0
% 2.52/0.96  --bmc1_max_bound                        -1
% 2.52/0.96  --bmc1_max_bound_default                -1
% 2.52/0.96  --bmc1_symbol_reachability              true
% 2.52/0.96  --bmc1_property_lemmas                  false
% 2.52/0.96  --bmc1_k_induction                      false
% 2.52/0.96  --bmc1_non_equiv_states                 false
% 2.52/0.96  --bmc1_deadlock                         false
% 2.52/0.96  --bmc1_ucm                              false
% 2.52/0.96  --bmc1_add_unsat_core                   none
% 2.52/0.96  --bmc1_unsat_core_children              false
% 2.52/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 2.52/0.96  --bmc1_out_stat                         full
% 2.52/0.96  --bmc1_ground_init                      false
% 2.52/0.96  --bmc1_pre_inst_next_state              false
% 2.52/0.96  --bmc1_pre_inst_state                   false
% 2.52/0.96  --bmc1_pre_inst_reach_state             false
% 2.52/0.96  --bmc1_out_unsat_core                   false
% 2.52/0.96  --bmc1_aig_witness_out                  false
% 2.52/0.96  --bmc1_verbose                          false
% 2.52/0.96  --bmc1_dump_clauses_tptp                false
% 2.52/0.96  --bmc1_dump_unsat_core_tptp             false
% 2.52/0.96  --bmc1_dump_file                        -
% 2.52/0.96  --bmc1_ucm_expand_uc_limit              128
% 2.52/0.96  --bmc1_ucm_n_expand_iterations          6
% 2.52/0.96  --bmc1_ucm_extend_mode                  1
% 2.52/0.96  --bmc1_ucm_init_mode                    2
% 2.52/0.96  --bmc1_ucm_cone_mode                    none
% 2.52/0.96  --bmc1_ucm_reduced_relation_type        0
% 2.52/0.96  --bmc1_ucm_relax_model                  4
% 2.52/0.96  --bmc1_ucm_full_tr_after_sat            true
% 2.52/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 2.52/0.96  --bmc1_ucm_layered_model                none
% 2.52/0.96  --bmc1_ucm_max_lemma_size               10
% 2.52/0.96  
% 2.52/0.96  ------ AIG Options
% 2.52/0.96  
% 2.52/0.96  --aig_mode                              false
% 2.52/0.96  
% 2.52/0.96  ------ Instantiation Options
% 2.52/0.96  
% 2.52/0.96  --instantiation_flag                    true
% 2.52/0.96  --inst_sos_flag                         false
% 2.52/0.96  --inst_sos_phase                        true
% 2.52/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.52/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.52/0.96  --inst_lit_sel_side                     num_symb
% 2.52/0.96  --inst_solver_per_active                1400
% 2.52/0.96  --inst_solver_calls_frac                1.
% 2.52/0.96  --inst_passive_queue_type               priority_queues
% 2.52/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.52/0.96  --inst_passive_queues_freq              [25;2]
% 2.52/0.96  --inst_dismatching                      true
% 2.52/0.96  --inst_eager_unprocessed_to_passive     true
% 2.52/0.96  --inst_prop_sim_given                   true
% 2.52/0.96  --inst_prop_sim_new                     false
% 2.52/0.96  --inst_subs_new                         false
% 2.52/0.96  --inst_eq_res_simp                      false
% 2.52/0.96  --inst_subs_given                       false
% 2.52/0.96  --inst_orphan_elimination               true
% 2.52/0.96  --inst_learning_loop_flag               true
% 2.52/0.96  --inst_learning_start                   3000
% 2.52/0.96  --inst_learning_factor                  2
% 2.52/0.96  --inst_start_prop_sim_after_learn       3
% 2.52/0.96  --inst_sel_renew                        solver
% 2.52/0.96  --inst_lit_activity_flag                true
% 2.52/0.96  --inst_restr_to_given                   false
% 2.52/0.96  --inst_activity_threshold               500
% 2.52/0.96  --inst_out_proof                        true
% 2.52/0.96  
% 2.52/0.96  ------ Resolution Options
% 2.52/0.96  
% 2.52/0.96  --resolution_flag                       true
% 2.52/0.96  --res_lit_sel                           adaptive
% 2.52/0.96  --res_lit_sel_side                      none
% 2.52/0.96  --res_ordering                          kbo
% 2.52/0.96  --res_to_prop_solver                    active
% 2.52/0.96  --res_prop_simpl_new                    false
% 2.52/0.96  --res_prop_simpl_given                  true
% 2.52/0.96  --res_passive_queue_type                priority_queues
% 2.52/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.52/0.96  --res_passive_queues_freq               [15;5]
% 2.52/0.96  --res_forward_subs                      full
% 2.52/0.96  --res_backward_subs                     full
% 2.52/0.96  --res_forward_subs_resolution           true
% 2.52/0.96  --res_backward_subs_resolution          true
% 2.52/0.96  --res_orphan_elimination                true
% 2.52/0.96  --res_time_limit                        2.
% 2.52/0.96  --res_out_proof                         true
% 2.52/0.96  
% 2.52/0.96  ------ Superposition Options
% 2.52/0.96  
% 2.52/0.96  --superposition_flag                    true
% 2.52/0.96  --sup_passive_queue_type                priority_queues
% 2.52/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.52/0.96  --sup_passive_queues_freq               [8;1;4]
% 2.52/0.96  --demod_completeness_check              fast
% 2.52/0.96  --demod_use_ground                      true
% 2.52/0.96  --sup_to_prop_solver                    passive
% 2.52/0.96  --sup_prop_simpl_new                    true
% 2.52/0.96  --sup_prop_simpl_given                  true
% 2.52/0.96  --sup_fun_splitting                     false
% 2.52/0.96  --sup_smt_interval                      50000
% 2.52/0.96  
% 2.52/0.96  ------ Superposition Simplification Setup
% 2.52/0.96  
% 2.52/0.96  --sup_indices_passive                   []
% 2.52/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 2.52/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/0.96  --sup_full_bw                           [BwDemod]
% 2.52/0.96  --sup_immed_triv                        [TrivRules]
% 2.52/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.52/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/0.96  --sup_immed_bw_main                     []
% 2.52/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.52/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 2.52/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.52/0.96  
% 2.52/0.96  ------ Combination Options
% 2.52/0.96  
% 2.52/0.96  --comb_res_mult                         3
% 2.52/0.96  --comb_sup_mult                         2
% 2.52/0.96  --comb_inst_mult                        10
% 2.52/0.96  
% 2.52/0.96  ------ Debug Options
% 2.52/0.96  
% 2.52/0.96  --dbg_backtrace                         false
% 2.52/0.96  --dbg_dump_prop_clauses                 false
% 2.52/0.96  --dbg_dump_prop_clauses_file            -
% 2.52/0.96  --dbg_out_stat                          false
% 2.52/0.96  ------ Parsing...
% 2.52/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.52/0.96  
% 2.52/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.52/0.96  
% 2.52/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.52/0.96  
% 2.52/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.52/0.96  ------ Proving...
% 2.52/0.96  ------ Problem Properties 
% 2.52/0.96  
% 2.52/0.96  
% 2.52/0.96  clauses                                 15
% 2.52/0.96  conjectures                             2
% 2.52/0.96  EPR                                     1
% 2.52/0.96  Horn                                    14
% 2.52/0.96  unary                                   3
% 2.52/0.96  binary                                  7
% 2.52/0.96  lits                                    33
% 2.52/0.96  lits eq                                 4
% 2.52/0.96  fd_pure                                 0
% 2.52/0.96  fd_pseudo                               0
% 2.52/0.96  fd_cond                                 0
% 2.52/0.96  fd_pseudo_cond                          0
% 2.52/0.96  AC symbols                              0
% 2.52/0.96  
% 2.52/0.96  ------ Schedule dynamic 5 is on 
% 2.52/0.96  
% 2.52/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.52/0.96  
% 2.52/0.96  
% 2.52/0.96  ------ 
% 2.52/0.96  Current options:
% 2.52/0.96  ------ 
% 2.52/0.96  
% 2.52/0.96  ------ Input Options
% 2.52/0.96  
% 2.52/0.96  --out_options                           all
% 2.52/0.96  --tptp_safe_out                         true
% 2.52/0.96  --problem_path                          ""
% 2.52/0.96  --include_path                          ""
% 2.52/0.96  --clausifier                            res/vclausify_rel
% 2.52/0.96  --clausifier_options                    --mode clausify
% 2.52/0.96  --stdin                                 false
% 2.52/0.96  --stats_out                             all
% 2.52/0.96  
% 2.52/0.96  ------ General Options
% 2.52/0.96  
% 2.52/0.96  --fof                                   false
% 2.52/0.96  --time_out_real                         305.
% 2.52/0.96  --time_out_virtual                      -1.
% 2.52/0.96  --symbol_type_check                     false
% 2.52/0.96  --clausify_out                          false
% 2.52/0.96  --sig_cnt_out                           false
% 2.52/0.96  --trig_cnt_out                          false
% 2.52/0.96  --trig_cnt_out_tolerance                1.
% 2.52/0.96  --trig_cnt_out_sk_spl                   false
% 2.52/0.96  --abstr_cl_out                          false
% 2.52/0.96  
% 2.52/0.96  ------ Global Options
% 2.52/0.96  
% 2.52/0.96  --schedule                              default
% 2.52/0.96  --add_important_lit                     false
% 2.52/0.96  --prop_solver_per_cl                    1000
% 2.52/0.96  --min_unsat_core                        false
% 2.52/0.96  --soft_assumptions                      false
% 2.52/0.96  --soft_lemma_size                       3
% 2.52/0.96  --prop_impl_unit_size                   0
% 2.52/0.96  --prop_impl_unit                        []
% 2.52/0.96  --share_sel_clauses                     true
% 2.52/0.96  --reset_solvers                         false
% 2.52/0.96  --bc_imp_inh                            [conj_cone]
% 2.52/0.96  --conj_cone_tolerance                   3.
% 2.52/0.96  --extra_neg_conj                        none
% 2.52/0.96  --large_theory_mode                     true
% 2.52/0.96  --prolific_symb_bound                   200
% 2.52/0.96  --lt_threshold                          2000
% 2.52/0.96  --clause_weak_htbl                      true
% 2.52/0.96  --gc_record_bc_elim                     false
% 2.52/0.96  
% 2.52/0.96  ------ Preprocessing Options
% 2.52/0.96  
% 2.52/0.96  --preprocessing_flag                    true
% 2.52/0.96  --time_out_prep_mult                    0.1
% 2.52/0.96  --splitting_mode                        input
% 2.52/0.96  --splitting_grd                         true
% 2.52/0.96  --splitting_cvd                         false
% 2.52/0.96  --splitting_cvd_svl                     false
% 2.52/0.96  --splitting_nvd                         32
% 2.52/0.96  --sub_typing                            true
% 2.52/0.96  --prep_gs_sim                           true
% 2.52/0.96  --prep_unflatten                        true
% 2.52/0.96  --prep_res_sim                          true
% 2.52/0.96  --prep_upred                            true
% 2.52/0.96  --prep_sem_filter                       exhaustive
% 2.52/0.96  --prep_sem_filter_out                   false
% 2.52/0.96  --pred_elim                             true
% 2.52/0.96  --res_sim_input                         true
% 2.52/0.96  --eq_ax_congr_red                       true
% 2.52/0.96  --pure_diseq_elim                       true
% 2.52/0.96  --brand_transform                       false
% 2.52/0.96  --non_eq_to_eq                          false
% 2.52/0.96  --prep_def_merge                        true
% 2.52/0.96  --prep_def_merge_prop_impl              false
% 2.52/0.96  --prep_def_merge_mbd                    true
% 2.52/0.96  --prep_def_merge_tr_red                 false
% 2.52/0.96  --prep_def_merge_tr_cl                  false
% 2.52/0.96  --smt_preprocessing                     true
% 2.52/0.96  --smt_ac_axioms                         fast
% 2.52/0.96  --preprocessed_out                      false
% 2.52/0.96  --preprocessed_stats                    false
% 2.52/0.96  
% 2.52/0.96  ------ Abstraction refinement Options
% 2.52/0.96  
% 2.52/0.96  --abstr_ref                             []
% 2.52/0.96  --abstr_ref_prep                        false
% 2.52/0.96  --abstr_ref_until_sat                   false
% 2.52/0.96  --abstr_ref_sig_restrict                funpre
% 2.52/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 2.52/0.96  --abstr_ref_under                       []
% 2.52/0.96  
% 2.52/0.96  ------ SAT Options
% 2.52/0.96  
% 2.52/0.96  --sat_mode                              false
% 2.52/0.96  --sat_fm_restart_options                ""
% 2.52/0.96  --sat_gr_def                            false
% 2.52/0.96  --sat_epr_types                         true
% 2.52/0.96  --sat_non_cyclic_types                  false
% 2.52/0.96  --sat_finite_models                     false
% 2.52/0.96  --sat_fm_lemmas                         false
% 2.52/0.96  --sat_fm_prep                           false
% 2.52/0.96  --sat_fm_uc_incr                        true
% 2.52/0.96  --sat_out_model                         small
% 2.52/0.96  --sat_out_clauses                       false
% 2.52/0.96  
% 2.52/0.96  ------ QBF Options
% 2.52/0.96  
% 2.52/0.96  --qbf_mode                              false
% 2.52/0.96  --qbf_elim_univ                         false
% 2.52/0.96  --qbf_dom_inst                          none
% 2.52/0.96  --qbf_dom_pre_inst                      false
% 2.52/0.96  --qbf_sk_in                             false
% 2.52/0.96  --qbf_pred_elim                         true
% 2.52/0.96  --qbf_split                             512
% 2.52/0.96  
% 2.52/0.96  ------ BMC1 Options
% 2.52/0.96  
% 2.52/0.96  --bmc1_incremental                      false
% 2.52/0.96  --bmc1_axioms                           reachable_all
% 2.52/0.96  --bmc1_min_bound                        0
% 2.52/0.96  --bmc1_max_bound                        -1
% 2.52/0.96  --bmc1_max_bound_default                -1
% 2.52/0.96  --bmc1_symbol_reachability              true
% 2.52/0.96  --bmc1_property_lemmas                  false
% 2.52/0.96  --bmc1_k_induction                      false
% 2.52/0.96  --bmc1_non_equiv_states                 false
% 2.52/0.96  --bmc1_deadlock                         false
% 2.52/0.96  --bmc1_ucm                              false
% 2.52/0.96  --bmc1_add_unsat_core                   none
% 2.52/0.96  --bmc1_unsat_core_children              false
% 2.52/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 2.52/0.96  --bmc1_out_stat                         full
% 2.52/0.96  --bmc1_ground_init                      false
% 2.52/0.96  --bmc1_pre_inst_next_state              false
% 2.52/0.96  --bmc1_pre_inst_state                   false
% 2.52/0.96  --bmc1_pre_inst_reach_state             false
% 2.52/0.96  --bmc1_out_unsat_core                   false
% 2.52/0.96  --bmc1_aig_witness_out                  false
% 2.52/0.96  --bmc1_verbose                          false
% 2.52/0.96  --bmc1_dump_clauses_tptp                false
% 2.52/0.96  --bmc1_dump_unsat_core_tptp             false
% 2.52/0.96  --bmc1_dump_file                        -
% 2.52/0.96  --bmc1_ucm_expand_uc_limit              128
% 2.52/0.96  --bmc1_ucm_n_expand_iterations          6
% 2.52/0.96  --bmc1_ucm_extend_mode                  1
% 2.52/0.96  --bmc1_ucm_init_mode                    2
% 2.52/0.96  --bmc1_ucm_cone_mode                    none
% 2.52/0.96  --bmc1_ucm_reduced_relation_type        0
% 2.52/0.96  --bmc1_ucm_relax_model                  4
% 2.52/0.96  --bmc1_ucm_full_tr_after_sat            true
% 2.52/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 2.52/0.96  --bmc1_ucm_layered_model                none
% 2.52/0.96  --bmc1_ucm_max_lemma_size               10
% 2.52/0.96  
% 2.52/0.96  ------ AIG Options
% 2.52/0.96  
% 2.52/0.96  --aig_mode                              false
% 2.52/0.96  
% 2.52/0.96  ------ Instantiation Options
% 2.52/0.96  
% 2.52/0.96  --instantiation_flag                    true
% 2.52/0.96  --inst_sos_flag                         false
% 2.52/0.96  --inst_sos_phase                        true
% 2.52/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.52/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.52/0.96  --inst_lit_sel_side                     none
% 2.52/0.96  --inst_solver_per_active                1400
% 2.52/0.96  --inst_solver_calls_frac                1.
% 2.52/0.96  --inst_passive_queue_type               priority_queues
% 2.52/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.52/0.96  --inst_passive_queues_freq              [25;2]
% 2.52/0.96  --inst_dismatching                      true
% 2.52/0.96  --inst_eager_unprocessed_to_passive     true
% 2.52/0.96  --inst_prop_sim_given                   true
% 2.52/0.96  --inst_prop_sim_new                     false
% 2.52/0.96  --inst_subs_new                         false
% 2.52/0.96  --inst_eq_res_simp                      false
% 2.52/0.96  --inst_subs_given                       false
% 2.52/0.96  --inst_orphan_elimination               true
% 2.52/0.96  --inst_learning_loop_flag               true
% 2.52/0.96  --inst_learning_start                   3000
% 2.52/0.96  --inst_learning_factor                  2
% 2.52/0.96  --inst_start_prop_sim_after_learn       3
% 2.52/0.96  --inst_sel_renew                        solver
% 2.52/0.96  --inst_lit_activity_flag                true
% 2.52/0.96  --inst_restr_to_given                   false
% 2.52/0.96  --inst_activity_threshold               500
% 2.52/0.96  --inst_out_proof                        true
% 2.52/0.96  
% 2.52/0.96  ------ Resolution Options
% 2.52/0.96  
% 2.52/0.96  --resolution_flag                       false
% 2.52/0.96  --res_lit_sel                           adaptive
% 2.52/0.96  --res_lit_sel_side                      none
% 2.52/0.96  --res_ordering                          kbo
% 2.52/0.96  --res_to_prop_solver                    active
% 2.52/0.96  --res_prop_simpl_new                    false
% 2.52/0.96  --res_prop_simpl_given                  true
% 2.52/0.96  --res_passive_queue_type                priority_queues
% 2.52/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.52/0.96  --res_passive_queues_freq               [15;5]
% 2.52/0.96  --res_forward_subs                      full
% 2.52/0.96  --res_backward_subs                     full
% 2.52/0.96  --res_forward_subs_resolution           true
% 2.52/0.96  --res_backward_subs_resolution          true
% 2.52/0.96  --res_orphan_elimination                true
% 2.52/0.96  --res_time_limit                        2.
% 2.52/0.96  --res_out_proof                         true
% 2.52/0.96  
% 2.52/0.96  ------ Superposition Options
% 2.52/0.96  
% 2.52/0.96  --superposition_flag                    true
% 2.52/0.96  --sup_passive_queue_type                priority_queues
% 2.52/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.52/0.96  --sup_passive_queues_freq               [8;1;4]
% 2.52/0.96  --demod_completeness_check              fast
% 2.52/0.96  --demod_use_ground                      true
% 2.52/0.96  --sup_to_prop_solver                    passive
% 2.52/0.96  --sup_prop_simpl_new                    true
% 2.52/0.96  --sup_prop_simpl_given                  true
% 2.52/0.96  --sup_fun_splitting                     false
% 2.52/0.96  --sup_smt_interval                      50000
% 2.52/0.96  
% 2.52/0.96  ------ Superposition Simplification Setup
% 2.52/0.96  
% 2.52/0.96  --sup_indices_passive                   []
% 2.52/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 2.52/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/0.96  --sup_full_bw                           [BwDemod]
% 2.52/0.96  --sup_immed_triv                        [TrivRules]
% 2.52/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.52/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/0.96  --sup_immed_bw_main                     []
% 2.52/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.52/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 2.52/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.52/0.96  
% 2.52/0.96  ------ Combination Options
% 2.52/0.96  
% 2.52/0.96  --comb_res_mult                         3
% 2.52/0.96  --comb_sup_mult                         2
% 2.52/0.96  --comb_inst_mult                        10
% 2.52/0.96  
% 2.52/0.96  ------ Debug Options
% 2.52/0.96  
% 2.52/0.96  --dbg_backtrace                         false
% 2.52/0.96  --dbg_dump_prop_clauses                 false
% 2.52/0.96  --dbg_dump_prop_clauses_file            -
% 2.52/0.96  --dbg_out_stat                          false
% 2.52/0.96  
% 2.52/0.96  
% 2.52/0.96  
% 2.52/0.96  
% 2.52/0.96  ------ Proving...
% 2.52/0.96  
% 2.52/0.96  
% 2.52/0.96  % SZS status Theorem for theBenchmark.p
% 2.52/0.96  
% 2.52/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 2.52/0.96  
% 2.52/0.96  fof(f6,axiom,(
% 2.52/0.96    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 2.52/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.96  
% 2.52/0.96  fof(f21,plain,(
% 2.52/0.96    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 2.52/0.96    inference(ennf_transformation,[],[f6])).
% 2.52/0.96  
% 2.52/0.96  fof(f44,plain,(
% 2.52/0.96    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 2.52/0.96    inference(cnf_transformation,[],[f21])).
% 2.52/0.96  
% 2.52/0.96  fof(f8,axiom,(
% 2.52/0.96    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0))),
% 2.52/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.96  
% 2.52/0.96  fof(f22,plain,(
% 2.52/0.96    ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1))),
% 2.52/0.96    inference(ennf_transformation,[],[f8])).
% 2.52/0.96  
% 2.52/0.96  fof(f46,plain,(
% 2.52/0.96    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1)) )),
% 2.52/0.96    inference(cnf_transformation,[],[f22])).
% 2.52/0.96  
% 2.52/0.96  fof(f13,axiom,(
% 2.52/0.96    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.52/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.96  
% 2.52/0.96  fof(f27,plain,(
% 2.52/0.96    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 2.52/0.96    inference(ennf_transformation,[],[f13])).
% 2.52/0.96  
% 2.52/0.96  fof(f28,plain,(
% 2.52/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 2.52/0.96    inference(flattening,[],[f27])).
% 2.52/0.96  
% 2.52/0.96  fof(f51,plain,(
% 2.52/0.96    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 2.52/0.96    inference(cnf_transformation,[],[f28])).
% 2.52/0.96  
% 2.52/0.96  fof(f14,conjecture,(
% 2.52/0.96    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))),
% 2.52/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.96  
% 2.52/0.96  fof(f15,negated_conjecture,(
% 2.52/0.96    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))),
% 2.52/0.96    inference(negated_conjecture,[],[f14])).
% 2.52/0.96  
% 2.52/0.96  fof(f29,plain,(
% 2.52/0.96    ? [X0,X1,X2,X3] : (~m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 2.52/0.96    inference(ennf_transformation,[],[f15])).
% 2.52/0.96  
% 2.52/0.96  fof(f34,plain,(
% 2.52/0.96    ? [X0,X1,X2,X3] : (~m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) => (~m1_subset_1(k6_relset_1(sK3,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))))),
% 2.52/0.96    introduced(choice_axiom,[])).
% 2.52/0.96  
% 2.52/0.96  fof(f35,plain,(
% 2.52/0.96    ~m1_subset_1(k6_relset_1(sK3,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 2.52/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f29,f34])).
% 2.52/0.96  
% 2.52/0.96  fof(f52,plain,(
% 2.52/0.96    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 2.52/0.96    inference(cnf_transformation,[],[f35])).
% 2.52/0.96  
% 2.52/0.96  fof(f12,axiom,(
% 2.52/0.96    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3))),
% 2.52/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.96  
% 2.52/0.96  fof(f26,plain,(
% 2.52/0.96    ! [X0,X1,X2,X3] : (k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.52/0.96    inference(ennf_transformation,[],[f12])).
% 2.52/0.96  
% 2.52/0.96  fof(f50,plain,(
% 2.52/0.96    ( ! [X2,X0,X3,X1] : (k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.52/0.96    inference(cnf_transformation,[],[f26])).
% 2.52/0.96  
% 2.52/0.96  fof(f53,plain,(
% 2.52/0.96    ~m1_subset_1(k6_relset_1(sK3,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))),
% 2.52/0.96    inference(cnf_transformation,[],[f35])).
% 2.52/0.96  
% 2.52/0.96  fof(f9,axiom,(
% 2.52/0.96    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)))),
% 2.52/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.96  
% 2.52/0.96  fof(f23,plain,(
% 2.52/0.96    ! [X0,X1] : (r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.52/0.96    inference(ennf_transformation,[],[f9])).
% 2.52/0.96  
% 2.52/0.96  fof(f47,plain,(
% 2.52/0.96    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.52/0.96    inference(cnf_transformation,[],[f23])).
% 2.52/0.96  
% 2.52/0.96  fof(f11,axiom,(
% 2.52/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.52/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.96  
% 2.52/0.96  fof(f25,plain,(
% 2.52/0.96    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.52/0.96    inference(ennf_transformation,[],[f11])).
% 2.52/0.96  
% 2.52/0.96  fof(f49,plain,(
% 2.52/0.96    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.52/0.96    inference(cnf_transformation,[],[f25])).
% 2.52/0.96  
% 2.52/0.96  fof(f10,axiom,(
% 2.52/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.52/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.96  
% 2.52/0.96  fof(f24,plain,(
% 2.52/0.96    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.52/0.96    inference(ennf_transformation,[],[f10])).
% 2.52/0.96  
% 2.52/0.96  fof(f48,plain,(
% 2.52/0.96    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.52/0.96    inference(cnf_transformation,[],[f24])).
% 2.52/0.96  
% 2.52/0.96  fof(f3,axiom,(
% 2.52/0.96    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 2.52/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.96  
% 2.52/0.96  fof(f41,plain,(
% 2.52/0.96    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 2.52/0.96    inference(cnf_transformation,[],[f3])).
% 2.52/0.96  
% 2.52/0.96  fof(f4,axiom,(
% 2.52/0.96    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.52/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.96  
% 2.52/0.96  fof(f18,plain,(
% 2.52/0.96    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.52/0.96    inference(ennf_transformation,[],[f4])).
% 2.52/0.96  
% 2.52/0.96  fof(f19,plain,(
% 2.52/0.96    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.52/0.96    inference(flattening,[],[f18])).
% 2.52/0.96  
% 2.52/0.96  fof(f42,plain,(
% 2.52/0.96    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.52/0.96    inference(cnf_transformation,[],[f19])).
% 2.52/0.96  
% 2.52/0.96  fof(f2,axiom,(
% 2.52/0.96    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.52/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.96  
% 2.52/0.96  fof(f30,plain,(
% 2.52/0.96    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.52/0.96    inference(nnf_transformation,[],[f2])).
% 2.52/0.96  
% 2.52/0.96  fof(f31,plain,(
% 2.52/0.96    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.52/0.96    inference(rectify,[],[f30])).
% 2.52/0.96  
% 2.52/0.96  fof(f32,plain,(
% 2.52/0.96    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 2.52/0.96    introduced(choice_axiom,[])).
% 2.52/0.96  
% 2.52/0.96  fof(f33,plain,(
% 2.52/0.96    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.52/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 2.52/0.96  
% 2.52/0.96  fof(f37,plain,(
% 2.52/0.96    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.52/0.96    inference(cnf_transformation,[],[f33])).
% 2.52/0.96  
% 2.52/0.96  fof(f55,plain,(
% 2.52/0.96    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 2.52/0.96    inference(equality_resolution,[],[f37])).
% 2.52/0.96  
% 2.52/0.96  fof(f1,axiom,(
% 2.52/0.96    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.52/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.96  
% 2.52/0.96  fof(f16,plain,(
% 2.52/0.96    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.52/0.96    inference(ennf_transformation,[],[f1])).
% 2.52/0.96  
% 2.52/0.96  fof(f17,plain,(
% 2.52/0.96    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.52/0.96    inference(flattening,[],[f16])).
% 2.52/0.96  
% 2.52/0.96  fof(f36,plain,(
% 2.52/0.96    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.52/0.96    inference(cnf_transformation,[],[f17])).
% 2.52/0.96  
% 2.52/0.96  fof(f5,axiom,(
% 2.52/0.96    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.52/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.96  
% 2.52/0.96  fof(f20,plain,(
% 2.52/0.96    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.52/0.96    inference(ennf_transformation,[],[f5])).
% 2.52/0.96  
% 2.52/0.96  fof(f43,plain,(
% 2.52/0.96    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.52/0.96    inference(cnf_transformation,[],[f20])).
% 2.52/0.96  
% 2.52/0.96  fof(f7,axiom,(
% 2.52/0.96    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.52/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.96  
% 2.52/0.96  fof(f45,plain,(
% 2.52/0.96    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.52/0.96    inference(cnf_transformation,[],[f7])).
% 2.52/0.96  
% 2.52/0.96  cnf(c_8,plain,
% 2.52/0.96      ( ~ v1_relat_1(X0) | v1_relat_1(k8_relat_1(X1,X0)) ),
% 2.52/0.96      inference(cnf_transformation,[],[f44]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_648,plain,
% 2.52/0.96      ( ~ v1_relat_1(X0_45) | v1_relat_1(k8_relat_1(X1_45,X0_45)) ),
% 2.52/0.96      inference(subtyping,[status(esa)],[c_8]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_950,plain,
% 2.52/0.96      ( v1_relat_1(X0_45) != iProver_top
% 2.52/0.96      | v1_relat_1(k8_relat_1(X1_45,X0_45)) = iProver_top ),
% 2.52/0.96      inference(predicate_to_equality,[status(thm)],[c_648]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_10,plain,
% 2.52/0.96      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~ v1_relat_1(X1) ),
% 2.52/0.96      inference(cnf_transformation,[],[f46]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_646,plain,
% 2.52/0.96      ( r1_tarski(k2_relat_1(k8_relat_1(X0_45,X1_45)),X0_45)
% 2.52/0.96      | ~ v1_relat_1(X1_45) ),
% 2.52/0.96      inference(subtyping,[status(esa)],[c_10]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_952,plain,
% 2.52/0.96      ( r1_tarski(k2_relat_1(k8_relat_1(X0_45,X1_45)),X0_45) = iProver_top
% 2.52/0.96      | v1_relat_1(X1_45) != iProver_top ),
% 2.52/0.96      inference(predicate_to_equality,[status(thm)],[c_646]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_15,plain,
% 2.52/0.96      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.52/0.96      | ~ r1_tarski(k1_relat_1(X0),X1)
% 2.52/0.96      | ~ r1_tarski(k2_relat_1(X0),X2)
% 2.52/0.96      | ~ v1_relat_1(X0) ),
% 2.52/0.96      inference(cnf_transformation,[],[f51]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_641,plain,
% 2.52/0.96      ( m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X1_45,X2_45)))
% 2.52/0.96      | ~ r1_tarski(k1_relat_1(X0_45),X1_45)
% 2.52/0.96      | ~ r1_tarski(k2_relat_1(X0_45),X2_45)
% 2.52/0.96      | ~ v1_relat_1(X0_45) ),
% 2.52/0.96      inference(subtyping,[status(esa)],[c_15]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_957,plain,
% 2.52/0.96      ( m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X1_45,X2_45))) = iProver_top
% 2.52/0.96      | r1_tarski(k1_relat_1(X0_45),X1_45) != iProver_top
% 2.52/0.96      | r1_tarski(k2_relat_1(X0_45),X2_45) != iProver_top
% 2.52/0.96      | v1_relat_1(X0_45) != iProver_top ),
% 2.52/0.96      inference(predicate_to_equality,[status(thm)],[c_641]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_17,negated_conjecture,
% 2.52/0.96      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 2.52/0.96      inference(cnf_transformation,[],[f52]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_639,negated_conjecture,
% 2.52/0.96      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 2.52/0.96      inference(subtyping,[status(esa)],[c_17]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_959,plain,
% 2.52/0.96      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 2.52/0.96      inference(predicate_to_equality,[status(thm)],[c_639]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_14,plain,
% 2.52/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.52/0.96      | k6_relset_1(X1,X2,X3,X0) = k8_relat_1(X3,X0) ),
% 2.52/0.96      inference(cnf_transformation,[],[f50]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_642,plain,
% 2.52/0.96      ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X1_45,X2_45)))
% 2.52/0.96      | k6_relset_1(X1_45,X2_45,X3_45,X0_45) = k8_relat_1(X3_45,X0_45) ),
% 2.52/0.96      inference(subtyping,[status(esa)],[c_14]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_956,plain,
% 2.52/0.96      ( k6_relset_1(X0_45,X1_45,X2_45,X3_45) = k8_relat_1(X2_45,X3_45)
% 2.52/0.96      | m1_subset_1(X3_45,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45))) != iProver_top ),
% 2.52/0.96      inference(predicate_to_equality,[status(thm)],[c_642]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_1683,plain,
% 2.52/0.96      ( k6_relset_1(sK3,sK1,X0_45,sK4) = k8_relat_1(X0_45,sK4) ),
% 2.52/0.96      inference(superposition,[status(thm)],[c_959,c_956]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_16,negated_conjecture,
% 2.52/0.96      ( ~ m1_subset_1(k6_relset_1(sK3,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
% 2.52/0.96      inference(cnf_transformation,[],[f53]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_640,negated_conjecture,
% 2.52/0.96      ( ~ m1_subset_1(k6_relset_1(sK3,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
% 2.52/0.96      inference(subtyping,[status(esa)],[c_16]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_958,plain,
% 2.52/0.96      ( m1_subset_1(k6_relset_1(sK3,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 2.52/0.96      inference(predicate_to_equality,[status(thm)],[c_640]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_1796,plain,
% 2.52/0.96      ( m1_subset_1(k8_relat_1(sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 2.52/0.96      inference(demodulation,[status(thm)],[c_1683,c_958]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_2096,plain,
% 2.52/0.96      ( r1_tarski(k1_relat_1(k8_relat_1(sK2,sK4)),sK3) != iProver_top
% 2.52/0.96      | r1_tarski(k2_relat_1(k8_relat_1(sK2,sK4)),sK2) != iProver_top
% 2.52/0.96      | v1_relat_1(k8_relat_1(sK2,sK4)) != iProver_top ),
% 2.52/0.96      inference(superposition,[status(thm)],[c_957,c_1796]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_11,plain,
% 2.52/0.96      ( r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1))
% 2.52/0.96      | ~ v1_relat_1(X1) ),
% 2.52/0.96      inference(cnf_transformation,[],[f47]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_645,plain,
% 2.52/0.96      ( r1_tarski(k1_relat_1(k8_relat_1(X0_45,X1_45)),k1_relat_1(X1_45))
% 2.52/0.96      | ~ v1_relat_1(X1_45) ),
% 2.52/0.96      inference(subtyping,[status(esa)],[c_11]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_953,plain,
% 2.52/0.96      ( r1_tarski(k1_relat_1(k8_relat_1(X0_45,X1_45)),k1_relat_1(X1_45)) = iProver_top
% 2.52/0.96      | v1_relat_1(X1_45) != iProver_top ),
% 2.52/0.96      inference(predicate_to_equality,[status(thm)],[c_645]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_13,plain,
% 2.52/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.52/0.96      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.52/0.96      inference(cnf_transformation,[],[f49]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_643,plain,
% 2.52/0.96      ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X1_45,X2_45)))
% 2.52/0.96      | k1_relset_1(X1_45,X2_45,X0_45) = k1_relat_1(X0_45) ),
% 2.52/0.96      inference(subtyping,[status(esa)],[c_13]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_955,plain,
% 2.52/0.96      ( k1_relset_1(X0_45,X1_45,X2_45) = k1_relat_1(X2_45)
% 2.52/0.96      | m1_subset_1(X2_45,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45))) != iProver_top ),
% 2.52/0.96      inference(predicate_to_equality,[status(thm)],[c_643]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_1367,plain,
% 2.52/0.96      ( k1_relset_1(sK3,sK1,sK4) = k1_relat_1(sK4) ),
% 2.52/0.96      inference(superposition,[status(thm)],[c_959,c_955]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_12,plain,
% 2.52/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.52/0.96      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 2.52/0.96      inference(cnf_transformation,[],[f48]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_644,plain,
% 2.52/0.96      ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X1_45,X2_45)))
% 2.52/0.96      | m1_subset_1(k1_relset_1(X1_45,X2_45,X0_45),k1_zfmisc_1(X1_45)) ),
% 2.52/0.96      inference(subtyping,[status(esa)],[c_12]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_954,plain,
% 2.52/0.96      ( m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X1_45,X2_45))) != iProver_top
% 2.52/0.96      | m1_subset_1(k1_relset_1(X1_45,X2_45,X0_45),k1_zfmisc_1(X1_45)) = iProver_top ),
% 2.52/0.96      inference(predicate_to_equality,[status(thm)],[c_644]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_1696,plain,
% 2.52/0.96      ( m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(sK3)) = iProver_top
% 2.52/0.96      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top ),
% 2.52/0.96      inference(superposition,[status(thm)],[c_1367,c_954]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_18,plain,
% 2.52/0.96      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 2.52/0.96      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_1980,plain,
% 2.52/0.96      ( m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(sK3)) = iProver_top ),
% 2.52/0.96      inference(global_propositional_subsumption,
% 2.52/0.96                [status(thm)],
% 2.52/0.96                [c_1696,c_18]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_5,plain,
% 2.52/0.96      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 2.52/0.96      inference(cnf_transformation,[],[f41]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_6,plain,
% 2.52/0.96      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.52/0.96      inference(cnf_transformation,[],[f42]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_249,plain,
% 2.52/0.96      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | k1_zfmisc_1(X2) != X1 ),
% 2.52/0.96      inference(resolution_lifted,[status(thm)],[c_5,c_6]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_250,plain,
% 2.52/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.52/0.96      | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 2.52/0.96      inference(unflattening,[status(thm)],[c_249]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_4,plain,
% 2.52/0.96      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.52/0.96      inference(cnf_transformation,[],[f55]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_393,plain,
% 2.52/0.96      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 2.52/0.96      inference(prop_impl,[status(thm)],[c_4]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_394,plain,
% 2.52/0.96      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.52/0.96      inference(renaming,[status(thm)],[c_393]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_427,plain,
% 2.52/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.52/0.96      inference(bin_hyper_res,[status(thm)],[c_250,c_394]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_638,plain,
% 2.52/0.96      ( ~ m1_subset_1(X0_45,k1_zfmisc_1(X1_45))
% 2.52/0.96      | r1_tarski(X0_45,X1_45) ),
% 2.52/0.96      inference(subtyping,[status(esa)],[c_427]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_960,plain,
% 2.52/0.96      ( m1_subset_1(X0_45,k1_zfmisc_1(X1_45)) != iProver_top
% 2.52/0.96      | r1_tarski(X0_45,X1_45) = iProver_top ),
% 2.52/0.96      inference(predicate_to_equality,[status(thm)],[c_638]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_1986,plain,
% 2.52/0.96      ( r1_tarski(k1_relat_1(sK4),sK3) = iProver_top ),
% 2.52/0.96      inference(superposition,[status(thm)],[c_1980,c_960]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_0,plain,
% 2.52/0.96      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 2.52/0.96      inference(cnf_transformation,[],[f36]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_650,plain,
% 2.52/0.96      ( ~ r1_tarski(X0_45,X1_45)
% 2.52/0.96      | ~ r1_tarski(X2_45,X0_45)
% 2.52/0.96      | r1_tarski(X2_45,X1_45) ),
% 2.52/0.96      inference(subtyping,[status(esa)],[c_0]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_948,plain,
% 2.52/0.96      ( r1_tarski(X0_45,X1_45) != iProver_top
% 2.52/0.96      | r1_tarski(X2_45,X0_45) != iProver_top
% 2.52/0.96      | r1_tarski(X2_45,X1_45) = iProver_top ),
% 2.52/0.96      inference(predicate_to_equality,[status(thm)],[c_650]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_1997,plain,
% 2.52/0.96      ( r1_tarski(X0_45,k1_relat_1(sK4)) != iProver_top
% 2.52/0.96      | r1_tarski(X0_45,sK3) = iProver_top ),
% 2.52/0.96      inference(superposition,[status(thm)],[c_1986,c_948]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_2402,plain,
% 2.52/0.96      ( r1_tarski(k1_relat_1(k8_relat_1(X0_45,sK4)),sK3) = iProver_top
% 2.52/0.96      | v1_relat_1(sK4) != iProver_top ),
% 2.52/0.96      inference(superposition,[status(thm)],[c_953,c_1997]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_7,plain,
% 2.52/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.52/0.96      | ~ v1_relat_1(X1)
% 2.52/0.96      | v1_relat_1(X0) ),
% 2.52/0.96      inference(cnf_transformation,[],[f43]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_649,plain,
% 2.52/0.96      ( ~ m1_subset_1(X0_45,k1_zfmisc_1(X1_45))
% 2.52/0.96      | ~ v1_relat_1(X1_45)
% 2.52/0.96      | v1_relat_1(X0_45) ),
% 2.52/0.96      inference(subtyping,[status(esa)],[c_7]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_1065,plain,
% 2.52/0.96      ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X1_45,X2_45)))
% 2.52/0.96      | v1_relat_1(X0_45)
% 2.52/0.96      | ~ v1_relat_1(k2_zfmisc_1(X1_45,X2_45)) ),
% 2.52/0.96      inference(instantiation,[status(thm)],[c_649]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_1183,plain,
% 2.52/0.96      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 2.52/0.96      | ~ v1_relat_1(k2_zfmisc_1(sK3,sK1))
% 2.52/0.96      | v1_relat_1(sK4) ),
% 2.52/0.96      inference(instantiation,[status(thm)],[c_1065]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_1184,plain,
% 2.52/0.96      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 2.52/0.96      | v1_relat_1(k2_zfmisc_1(sK3,sK1)) != iProver_top
% 2.52/0.96      | v1_relat_1(sK4) = iProver_top ),
% 2.52/0.96      inference(predicate_to_equality,[status(thm)],[c_1183]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_9,plain,
% 2.52/0.96      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.52/0.96      inference(cnf_transformation,[],[f45]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_647,plain,
% 2.52/0.96      ( v1_relat_1(k2_zfmisc_1(X0_45,X1_45)) ),
% 2.52/0.96      inference(subtyping,[status(esa)],[c_9]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_1229,plain,
% 2.52/0.96      ( v1_relat_1(k2_zfmisc_1(sK3,sK1)) ),
% 2.52/0.96      inference(instantiation,[status(thm)],[c_647]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_1230,plain,
% 2.52/0.96      ( v1_relat_1(k2_zfmisc_1(sK3,sK1)) = iProver_top ),
% 2.52/0.96      inference(predicate_to_equality,[status(thm)],[c_1229]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_2419,plain,
% 2.52/0.96      ( r1_tarski(k1_relat_1(k8_relat_1(X0_45,sK4)),sK3) = iProver_top ),
% 2.52/0.96      inference(global_propositional_subsumption,
% 2.52/0.96                [status(thm)],
% 2.52/0.96                [c_2402,c_18,c_1184,c_1230]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_2890,plain,
% 2.52/0.96      ( r1_tarski(k2_relat_1(k8_relat_1(sK2,sK4)),sK2) != iProver_top
% 2.52/0.96      | v1_relat_1(k8_relat_1(sK2,sK4)) != iProver_top ),
% 2.52/0.96      inference(forward_subsumption_resolution,
% 2.52/0.96                [status(thm)],
% 2.52/0.96                [c_2096,c_2419]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_2892,plain,
% 2.52/0.96      ( v1_relat_1(k8_relat_1(sK2,sK4)) != iProver_top
% 2.52/0.96      | v1_relat_1(sK4) != iProver_top ),
% 2.52/0.96      inference(superposition,[status(thm)],[c_952,c_2890]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_3176,plain,
% 2.52/0.96      ( v1_relat_1(k8_relat_1(sK2,sK4)) != iProver_top ),
% 2.52/0.96      inference(global_propositional_subsumption,
% 2.52/0.96                [status(thm)],
% 2.52/0.96                [c_2892,c_18,c_1184,c_1230]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(c_3181,plain,
% 2.52/0.96      ( v1_relat_1(sK4) != iProver_top ),
% 2.52/0.96      inference(superposition,[status(thm)],[c_950,c_3176]) ).
% 2.52/0.96  
% 2.52/0.96  cnf(contradiction,plain,
% 2.52/0.96      ( $false ),
% 2.52/0.96      inference(minisat,[status(thm)],[c_3181,c_1230,c_1184,c_18]) ).
% 2.52/0.96  
% 2.52/0.96  
% 2.52/0.96  % SZS output end CNFRefutation for theBenchmark.p
% 2.52/0.96  
% 2.52/0.96  ------                               Statistics
% 2.52/0.96  
% 2.52/0.96  ------ General
% 2.52/0.96  
% 2.52/0.96  abstr_ref_over_cycles:                  0
% 2.52/0.96  abstr_ref_under_cycles:                 0
% 2.52/0.96  gc_basic_clause_elim:                   0
% 2.52/0.96  forced_gc_time:                         0
% 2.52/0.96  parsing_time:                           0.008
% 2.52/0.96  unif_index_cands_time:                  0.
% 2.52/0.96  unif_index_add_time:                    0.
% 2.52/0.96  orderings_time:                         0.
% 2.52/0.96  out_proof_time:                         0.006
% 2.52/0.96  total_time:                             0.14
% 2.52/0.96  num_of_symbols:                         50
% 2.52/0.96  num_of_terms:                           4913
% 2.52/0.96  
% 2.52/0.96  ------ Preprocessing
% 2.52/0.96  
% 2.52/0.96  num_of_splits:                          0
% 2.52/0.96  num_of_split_atoms:                     0
% 2.52/0.96  num_of_reused_defs:                     0
% 2.52/0.96  num_eq_ax_congr_red:                    26
% 2.52/0.96  num_of_sem_filtered_clauses:            1
% 2.52/0.96  num_of_subtypes:                        2
% 2.52/0.96  monotx_restored_types:                  0
% 2.52/0.96  sat_num_of_epr_types:                   0
% 2.52/0.96  sat_num_of_non_cyclic_types:            0
% 2.52/0.96  sat_guarded_non_collapsed_types:        0
% 2.52/0.96  num_pure_diseq_elim:                    0
% 2.52/0.96  simp_replaced_by:                       0
% 2.52/0.96  res_preprocessed:                       107
% 2.52/0.96  prep_upred:                             0
% 2.52/0.96  prep_unflattend:                        11
% 2.52/0.96  smt_new_axioms:                         0
% 2.52/0.96  pred_elim_cands:                        3
% 2.52/0.96  pred_elim:                              2
% 2.52/0.96  pred_elim_cl:                           3
% 2.52/0.96  pred_elim_cycles:                       5
% 2.52/0.96  merged_defs:                            4
% 2.52/0.96  merged_defs_ncl:                        0
% 2.52/0.96  bin_hyper_res:                          5
% 2.52/0.96  prep_cycles:                            5
% 2.52/0.96  pred_elim_time:                         0.002
% 2.52/0.96  splitting_time:                         0.
% 2.52/0.96  sem_filter_time:                        0.
% 2.52/0.96  monotx_time:                            0.
% 2.52/0.96  subtype_inf_time:                       0.
% 2.52/0.96  
% 2.52/0.96  ------ Problem properties
% 2.52/0.96  
% 2.52/0.96  clauses:                                15
% 2.52/0.96  conjectures:                            2
% 2.52/0.96  epr:                                    1
% 2.52/0.96  horn:                                   14
% 2.52/0.96  ground:                                 2
% 2.52/0.96  unary:                                  3
% 2.52/0.96  binary:                                 7
% 2.52/0.96  lits:                                   33
% 2.52/0.96  lits_eq:                                4
% 2.52/0.96  fd_pure:                                0
% 2.52/0.96  fd_pseudo:                              0
% 2.52/0.96  fd_cond:                                0
% 2.52/0.96  fd_pseudo_cond:                         0
% 2.52/0.96  ac_symbols:                             0
% 2.52/0.96  
% 2.52/0.96  ------ Propositional Solver
% 2.52/0.96  
% 2.52/0.96  prop_solver_calls:                      31
% 2.52/0.96  prop_fast_solver_calls:                 573
% 2.52/0.96  smt_solver_calls:                       0
% 2.52/0.96  smt_fast_solver_calls:                  0
% 2.52/0.96  prop_num_of_clauses:                    1473
% 2.52/0.96  prop_preprocess_simplified:             4683
% 2.52/0.96  prop_fo_subsumed:                       4
% 2.52/0.96  prop_solver_time:                       0.
% 2.52/0.96  smt_solver_time:                        0.
% 2.52/0.96  smt_fast_solver_time:                   0.
% 2.52/0.96  prop_fast_solver_time:                  0.
% 2.52/0.96  prop_unsat_core_time:                   0.
% 2.52/0.96  
% 2.52/0.96  ------ QBF
% 2.52/0.96  
% 2.52/0.96  qbf_q_res:                              0
% 2.52/0.96  qbf_num_tautologies:                    0
% 2.52/0.96  qbf_prep_cycles:                        0
% 2.52/0.96  
% 2.52/0.96  ------ BMC1
% 2.52/0.96  
% 2.52/0.96  bmc1_current_bound:                     -1
% 2.52/0.96  bmc1_last_solved_bound:                 -1
% 2.52/0.96  bmc1_unsat_core_size:                   -1
% 2.52/0.96  bmc1_unsat_core_parents_size:           -1
% 2.52/0.96  bmc1_merge_next_fun:                    0
% 2.52/0.96  bmc1_unsat_core_clauses_time:           0.
% 2.52/0.96  
% 2.52/0.96  ------ Instantiation
% 2.52/0.96  
% 2.52/0.96  inst_num_of_clauses:                    377
% 2.52/0.96  inst_num_in_passive:                    101
% 2.52/0.96  inst_num_in_active:                     143
% 2.52/0.96  inst_num_in_unprocessed:                133
% 2.52/0.96  inst_num_of_loops:                      150
% 2.52/0.96  inst_num_of_learning_restarts:          0
% 2.52/0.96  inst_num_moves_active_passive:          5
% 2.52/0.96  inst_lit_activity:                      0
% 2.52/0.96  inst_lit_activity_moves:                0
% 2.52/0.96  inst_num_tautologies:                   0
% 2.52/0.96  inst_num_prop_implied:                  0
% 2.52/0.96  inst_num_existing_simplified:           0
% 2.52/0.96  inst_num_eq_res_simplified:             0
% 2.52/0.96  inst_num_child_elim:                    0
% 2.52/0.96  inst_num_of_dismatching_blockings:      57
% 2.52/0.96  inst_num_of_non_proper_insts:           155
% 2.52/0.96  inst_num_of_duplicates:                 0
% 2.52/0.96  inst_inst_num_from_inst_to_res:         0
% 2.52/0.96  inst_dismatching_checking_time:         0.
% 2.52/0.96  
% 2.52/0.96  ------ Resolution
% 2.52/0.96  
% 2.52/0.96  res_num_of_clauses:                     0
% 2.52/0.96  res_num_in_passive:                     0
% 2.52/0.96  res_num_in_active:                      0
% 2.52/0.96  res_num_of_loops:                       112
% 2.52/0.96  res_forward_subset_subsumed:            8
% 2.52/0.96  res_backward_subset_subsumed:           0
% 2.52/0.96  res_forward_subsumed:                   0
% 2.52/0.96  res_backward_subsumed:                  0
% 2.52/0.96  res_forward_subsumption_resolution:     0
% 2.52/0.96  res_backward_subsumption_resolution:    0
% 2.52/0.96  res_clause_to_clause_subsumption:       67
% 2.52/0.96  res_orphan_elimination:                 0
% 2.52/0.96  res_tautology_del:                      34
% 2.52/0.96  res_num_eq_res_simplified:              0
% 2.52/0.96  res_num_sel_changes:                    0
% 2.52/0.96  res_moves_from_active_to_pass:          0
% 2.52/0.96  
% 2.52/0.96  ------ Superposition
% 2.52/0.96  
% 2.52/0.96  sup_time_total:                         0.
% 2.52/0.96  sup_time_generating:                    0.
% 2.52/0.96  sup_time_sim_full:                      0.
% 2.52/0.96  sup_time_sim_immed:                     0.
% 2.52/0.96  
% 2.52/0.96  sup_num_of_clauses:                     48
% 2.52/0.96  sup_num_in_active:                      28
% 2.52/0.96  sup_num_in_passive:                     20
% 2.52/0.96  sup_num_of_loops:                       28
% 2.52/0.96  sup_fw_superposition:                   21
% 2.52/0.96  sup_bw_superposition:                   15
% 2.52/0.96  sup_immediate_simplified:               2
% 2.52/0.96  sup_given_eliminated:                   0
% 2.52/0.96  comparisons_done:                       0
% 2.52/0.96  comparisons_avoided:                    0
% 2.52/0.96  
% 2.52/0.96  ------ Simplifications
% 2.52/0.96  
% 2.52/0.96  
% 2.52/0.96  sim_fw_subset_subsumed:                 2
% 2.52/0.96  sim_bw_subset_subsumed:                 0
% 2.52/0.96  sim_fw_subsumed:                        0
% 2.52/0.96  sim_bw_subsumed:                        0
% 2.52/0.96  sim_fw_subsumption_res:                 1
% 2.52/0.96  sim_bw_subsumption_res:                 0
% 2.52/0.96  sim_tautology_del:                      1
% 2.52/0.96  sim_eq_tautology_del:                   0
% 2.52/0.96  sim_eq_res_simp:                        0
% 2.52/0.96  sim_fw_demodulated:                     0
% 2.52/0.96  sim_bw_demodulated:                     1
% 2.52/0.96  sim_light_normalised:                   0
% 2.52/0.96  sim_joinable_taut:                      0
% 2.52/0.96  sim_joinable_simp:                      0
% 2.52/0.96  sim_ac_normalised:                      0
% 2.52/0.96  sim_smt_subsumption:                    0
% 2.52/0.96  
%------------------------------------------------------------------------------
