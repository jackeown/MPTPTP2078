%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:37 EST 2020

% Result     : Theorem 50.95s
% Output     : CNFRefutation 50.95s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 121 expanded)
%              Number of clauses        :   56 (  58 expanded)
%              Number of leaves         :   17 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :  254 ( 363 expanded)
%              Number of equality atoms :   61 (  66 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k6_subset_1(X1,X0)) ),
    inference(definition_unfolding,[],[f26,f30])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k2_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)) = k5_relat_1(X0,k2_xboole_0(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)) = k5_relat_1(X0,k2_xboole_0(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)) = k5_relat_1(X0,k2_xboole_0(X1,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f27,f30])).

fof(f11,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2)))
          & v1_relat_1(X2) )
     => ( ~ r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,sK2)),k5_relat_1(X0,k6_subset_1(X1,sK2)))
        & v1_relat_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
     => ( ? [X2] :
            ( ~ r1_tarski(k6_subset_1(k5_relat_1(X0,sK1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(sK1,X2)))
            & v1_relat_1(X2) )
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2)))
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k6_subset_1(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2)),k5_relat_1(sK0,k6_subset_1(X1,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ~ r1_tarski(k6_subset_1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)),k5_relat_1(sK0,k6_subset_1(sK1,sK2)))
    & v1_relat_1(sK2)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f23,f22,f21])).

fof(f38,plain,(
    ~ r1_tarski(k6_subset_1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)),k5_relat_1(sK0,k6_subset_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f24])).

fof(f37,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f36,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f35,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_3,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_112,plain,
    ( r1_tarski(X0_38,k2_xboole_0(X0_38,X1_38)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_165014,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK1,X0_38)) ),
    inference(instantiation,[status(thm)],[c_112])).

cnf(c_181709,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_165014])).

cnf(c_122,plain,
    ( ~ r1_tarski(X0_38,X1_38)
    | r1_tarski(X2_38,X3_38)
    | X2_38 != X0_38
    | X3_38 != X1_38 ),
    theory(equality)).

cnf(c_155642,plain,
    ( r1_tarski(X0_38,X1_38)
    | ~ r1_tarski(X2_38,k2_xboole_0(X3_38,X4_38))
    | X0_38 != X2_38
    | X1_38 != k2_xboole_0(X3_38,X4_38) ),
    inference(instantiation,[status(thm)],[c_122])).

cnf(c_155886,plain,
    ( ~ r1_tarski(X0_38,k2_xboole_0(X1_38,X2_38))
    | r1_tarski(X3_38,k2_xboole_0(X4_38,X5_38))
    | X3_38 != X0_38
    | k2_xboole_0(X4_38,X5_38) != k2_xboole_0(X1_38,X2_38) ),
    inference(instantiation,[status(thm)],[c_155642])).

cnf(c_158351,plain,
    ( ~ r1_tarski(X0_38,k2_xboole_0(X1_38,X2_38))
    | r1_tarski(sK1,k2_xboole_0(sK2,k6_subset_1(sK1,sK2)))
    | k2_xboole_0(sK2,k6_subset_1(sK1,sK2)) != k2_xboole_0(X1_38,X2_38)
    | sK1 != X0_38 ),
    inference(instantiation,[status(thm)],[c_155886])).

cnf(c_160191,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(X0_38,X1_38))
    | r1_tarski(sK1,k2_xboole_0(sK2,k6_subset_1(sK1,sK2)))
    | k2_xboole_0(sK2,k6_subset_1(sK1,sK2)) != k2_xboole_0(X0_38,X1_38)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_158351])).

cnf(c_167005,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK2,k6_subset_1(sK1,sK2)))
    | ~ r1_tarski(sK1,k2_xboole_0(sK1,sK2))
    | k2_xboole_0(sK2,k6_subset_1(sK1,sK2)) != k2_xboole_0(sK1,sK2)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_160191])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_109,plain,
    ( ~ v1_relat_1(X0_38)
    | ~ v1_relat_1(X1_38)
    | v1_relat_1(k2_xboole_0(X0_38,X1_38)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_103519,plain,
    ( ~ v1_relat_1(k6_subset_1(sK1,sK2))
    | v1_relat_1(k2_xboole_0(sK2,k6_subset_1(sK1,sK2)))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_109])).

cnf(c_119,plain,
    ( X0_38 != X1_38
    | X2_38 != X1_38
    | X2_38 = X0_38 ),
    theory(equality)).

cnf(c_502,plain,
    ( X0_38 != X1_38
    | X0_38 = k2_xboole_0(X2_38,X3_38)
    | k2_xboole_0(X2_38,X3_38) != X1_38 ),
    inference(instantiation,[status(thm)],[c_119])).

cnf(c_731,plain,
    ( X0_38 != k2_xboole_0(X1_38,X2_38)
    | X0_38 = k2_xboole_0(X2_38,X1_38)
    | k2_xboole_0(X2_38,X1_38) != k2_xboole_0(X1_38,X2_38) ),
    inference(instantiation,[status(thm)],[c_502])).

cnf(c_1236,plain,
    ( k2_xboole_0(X0_38,X1_38) != k2_xboole_0(X1_38,X0_38)
    | k2_xboole_0(X1_38,k6_subset_1(X0_38,X1_38)) != k2_xboole_0(X1_38,X0_38)
    | k2_xboole_0(X1_38,k6_subset_1(X0_38,X1_38)) = k2_xboole_0(X0_38,X1_38) ),
    inference(instantiation,[status(thm)],[c_731])).

cnf(c_52997,plain,
    ( k2_xboole_0(sK2,k6_subset_1(sK1,sK2)) != k2_xboole_0(sK2,sK1)
    | k2_xboole_0(sK2,k6_subset_1(sK1,sK2)) = k2_xboole_0(sK1,sK2)
    | k2_xboole_0(sK1,sK2) != k2_xboole_0(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_1236])).

cnf(c_1,plain,
    ( k2_xboole_0(X0,k6_subset_1(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_114,plain,
    ( k2_xboole_0(X0_38,k6_subset_1(X1_38,X0_38)) = k2_xboole_0(X0_38,X1_38) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_52461,plain,
    ( k2_xboole_0(sK2,k6_subset_1(sK1,sK2)) = k2_xboole_0(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_114])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_115,plain,
    ( k2_xboole_0(X0_38,X1_38) = k2_xboole_0(X1_38,X0_38) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_52020,plain,
    ( k2_xboole_0(sK1,sK2) = k2_xboole_0(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_115])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_108,plain,
    ( ~ r1_tarski(X0_38,X1_38)
    | r1_tarski(k5_relat_1(X2_38,X0_38),k5_relat_1(X2_38,X1_38))
    | ~ v1_relat_1(X0_38)
    | ~ v1_relat_1(X1_38)
    | ~ v1_relat_1(X2_38) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_606,plain,
    ( ~ r1_tarski(X0_38,k2_xboole_0(X1_38,X2_38))
    | r1_tarski(k5_relat_1(X3_38,X0_38),k5_relat_1(X3_38,k2_xboole_0(X1_38,X2_38)))
    | ~ v1_relat_1(X0_38)
    | ~ v1_relat_1(X3_38)
    | ~ v1_relat_1(k2_xboole_0(X1_38,X2_38)) ),
    inference(instantiation,[status(thm)],[c_108])).

cnf(c_50187,plain,
    ( r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK0,k2_xboole_0(sK2,k6_subset_1(sK1,sK2))))
    | ~ r1_tarski(sK1,k2_xboole_0(sK2,k6_subset_1(sK1,sK2)))
    | ~ v1_relat_1(k2_xboole_0(sK2,k6_subset_1(sK1,sK2)))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_606])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k2_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)) = k5_relat_1(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_107,plain,
    ( ~ v1_relat_1(X0_38)
    | ~ v1_relat_1(X1_38)
    | ~ v1_relat_1(X2_38)
    | k2_xboole_0(k5_relat_1(X0_38,X1_38),k5_relat_1(X0_38,X2_38)) = k5_relat_1(X0_38,k2_xboole_0(X1_38,X2_38)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_11541,plain,
    ( ~ v1_relat_1(X0_38)
    | ~ v1_relat_1(X1_38)
    | ~ v1_relat_1(sK0)
    | k2_xboole_0(k5_relat_1(sK0,X0_38),k5_relat_1(sK0,X1_38)) = k5_relat_1(sK0,k2_xboole_0(X0_38,X1_38)) ),
    inference(instantiation,[status(thm)],[c_107])).

cnf(c_33628,plain,
    ( ~ v1_relat_1(k6_subset_1(sK1,sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK0)
    | k2_xboole_0(k5_relat_1(sK0,sK2),k5_relat_1(sK0,k6_subset_1(sK1,sK2))) = k5_relat_1(sK0,k2_xboole_0(sK2,k6_subset_1(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_11541])).

cnf(c_4,plain,
    ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_111,plain,
    ( m1_subset_1(k6_subset_1(X0_38,X1_38),k1_zfmisc_1(X0_38)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_13574,plain,
    ( m1_subset_1(k6_subset_1(sK1,sK2),k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_111])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_110,plain,
    ( ~ m1_subset_1(X0_38,k1_zfmisc_1(X1_38))
    | ~ v1_relat_1(X1_38)
    | v1_relat_1(X0_38) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_5345,plain,
    ( ~ m1_subset_1(k6_subset_1(sK1,sK2),k1_zfmisc_1(X0_38))
    | ~ v1_relat_1(X0_38)
    | v1_relat_1(k6_subset_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_110])).

cnf(c_13573,plain,
    ( ~ m1_subset_1(k6_subset_1(sK1,sK2),k1_zfmisc_1(sK1))
    | v1_relat_1(k6_subset_1(sK1,sK2))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_5345])).

cnf(c_921,plain,
    ( r1_tarski(X0_38,X1_38)
    | ~ r1_tarski(k5_relat_1(X2_38,X3_38),k5_relat_1(X2_38,k2_xboole_0(X4_38,X5_38)))
    | X0_38 != k5_relat_1(X2_38,X3_38)
    | X1_38 != k5_relat_1(X2_38,k2_xboole_0(X4_38,X5_38)) ),
    inference(instantiation,[status(thm)],[c_122])).

cnf(c_1268,plain,
    ( r1_tarski(X0_38,k2_xboole_0(k5_relat_1(X1_38,X2_38),k5_relat_1(X1_38,X3_38)))
    | ~ r1_tarski(k5_relat_1(X1_38,X4_38),k5_relat_1(X1_38,k2_xboole_0(X2_38,X3_38)))
    | X0_38 != k5_relat_1(X1_38,X4_38)
    | k2_xboole_0(k5_relat_1(X1_38,X2_38),k5_relat_1(X1_38,X3_38)) != k5_relat_1(X1_38,k2_xboole_0(X2_38,X3_38)) ),
    inference(instantiation,[status(thm)],[c_921])).

cnf(c_3196,plain,
    ( ~ r1_tarski(k5_relat_1(X0_38,X1_38),k5_relat_1(X0_38,k2_xboole_0(X2_38,X3_38)))
    | r1_tarski(k5_relat_1(X4_38,X5_38),k2_xboole_0(k5_relat_1(X0_38,X2_38),k5_relat_1(X0_38,X3_38)))
    | k5_relat_1(X4_38,X5_38) != k5_relat_1(X0_38,X1_38)
    | k2_xboole_0(k5_relat_1(X0_38,X2_38),k5_relat_1(X0_38,X3_38)) != k5_relat_1(X0_38,k2_xboole_0(X2_38,X3_38)) ),
    inference(instantiation,[status(thm)],[c_1268])).

cnf(c_7280,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,X0_38),k5_relat_1(sK0,k2_xboole_0(sK2,k6_subset_1(sK1,sK2))))
    | r1_tarski(k5_relat_1(sK0,sK1),k2_xboole_0(k5_relat_1(sK0,sK2),k5_relat_1(sK0,k6_subset_1(sK1,sK2))))
    | k5_relat_1(sK0,sK1) != k5_relat_1(sK0,X0_38)
    | k2_xboole_0(k5_relat_1(sK0,sK2),k5_relat_1(sK0,k6_subset_1(sK1,sK2))) != k5_relat_1(sK0,k2_xboole_0(sK2,k6_subset_1(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_3196])).

cnf(c_8728,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK0,k2_xboole_0(sK2,k6_subset_1(sK1,sK2))))
    | r1_tarski(k5_relat_1(sK0,sK1),k2_xboole_0(k5_relat_1(sK0,sK2),k5_relat_1(sK0,k6_subset_1(sK1,sK2))))
    | k5_relat_1(sK0,sK1) != k5_relat_1(sK0,sK1)
    | k2_xboole_0(k5_relat_1(sK0,sK2),k5_relat_1(sK0,k6_subset_1(sK1,sK2))) != k5_relat_1(sK0,k2_xboole_0(sK2,k6_subset_1(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_7280])).

cnf(c_117,plain,
    ( X0_38 = X0_38 ),
    theory(equality)).

cnf(c_1092,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_117])).

cnf(c_692,plain,
    ( k5_relat_1(X0_38,X1_38) = k5_relat_1(X0_38,X1_38) ),
    inference(instantiation,[status(thm)],[c_117])).

cnf(c_1089,plain,
    ( k5_relat_1(sK0,sK1) = k5_relat_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_692])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k6_subset_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_113,plain,
    ( ~ r1_tarski(X0_38,k2_xboole_0(X1_38,X2_38))
    | r1_tarski(k6_subset_1(X0_38,X1_38),X2_38) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_432,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,sK1),k2_xboole_0(k5_relat_1(sK0,sK2),k5_relat_1(sK0,k6_subset_1(sK1,sK2))))
    | r1_tarski(k6_subset_1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)),k5_relat_1(sK0,k6_subset_1(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_113])).

cnf(c_9,negated_conjecture,
    ( ~ r1_tarski(k6_subset_1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)),k5_relat_1(sK0,k6_subset_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_10,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_11,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_12,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f35])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_181709,c_167005,c_103519,c_52997,c_52461,c_52020,c_50187,c_33628,c_13574,c_13573,c_8728,c_1092,c_1089,c_432,c_9,c_10,c_11,c_12])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:19:11 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 50.95/6.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 50.95/6.96  
% 50.95/6.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 50.95/6.96  
% 50.95/6.96  ------  iProver source info
% 50.95/6.96  
% 50.95/6.96  git: date: 2020-06-30 10:37:57 +0100
% 50.95/6.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 50.95/6.96  git: non_committed_changes: false
% 50.95/6.96  git: last_make_outside_of_git: false
% 50.95/6.96  
% 50.95/6.96  ------ 
% 50.95/6.96  
% 50.95/6.96  ------ Input Options
% 50.95/6.96  
% 50.95/6.96  --out_options                           all
% 50.95/6.96  --tptp_safe_out                         true
% 50.95/6.96  --problem_path                          ""
% 50.95/6.96  --include_path                          ""
% 50.95/6.96  --clausifier                            res/vclausify_rel
% 50.95/6.96  --clausifier_options                    --mode clausify
% 50.95/6.96  --stdin                                 false
% 50.95/6.96  --stats_out                             sel
% 50.95/6.96  
% 50.95/6.96  ------ General Options
% 50.95/6.96  
% 50.95/6.96  --fof                                   false
% 50.95/6.96  --time_out_real                         604.99
% 50.95/6.96  --time_out_virtual                      -1.
% 50.95/6.96  --symbol_type_check                     false
% 50.95/6.96  --clausify_out                          false
% 50.95/6.96  --sig_cnt_out                           false
% 50.95/6.96  --trig_cnt_out                          false
% 50.95/6.96  --trig_cnt_out_tolerance                1.
% 50.95/6.96  --trig_cnt_out_sk_spl                   false
% 50.95/6.96  --abstr_cl_out                          false
% 50.95/6.96  
% 50.95/6.96  ------ Global Options
% 50.95/6.96  
% 50.95/6.96  --schedule                              none
% 50.95/6.96  --add_important_lit                     false
% 50.95/6.96  --prop_solver_per_cl                    1000
% 50.95/6.96  --min_unsat_core                        false
% 50.95/6.96  --soft_assumptions                      false
% 50.95/6.96  --soft_lemma_size                       3
% 50.95/6.96  --prop_impl_unit_size                   0
% 50.95/6.96  --prop_impl_unit                        []
% 50.95/6.96  --share_sel_clauses                     true
% 50.95/6.96  --reset_solvers                         false
% 50.95/6.96  --bc_imp_inh                            [conj_cone]
% 50.95/6.96  --conj_cone_tolerance                   3.
% 50.95/6.96  --extra_neg_conj                        none
% 50.95/6.96  --large_theory_mode                     true
% 50.95/6.96  --prolific_symb_bound                   200
% 50.95/6.96  --lt_threshold                          2000
% 50.95/6.96  --clause_weak_htbl                      true
% 50.95/6.96  --gc_record_bc_elim                     false
% 50.95/6.96  
% 50.95/6.96  ------ Preprocessing Options
% 50.95/6.96  
% 50.95/6.96  --preprocessing_flag                    true
% 50.95/6.96  --time_out_prep_mult                    0.1
% 50.95/6.96  --splitting_mode                        input
% 50.95/6.96  --splitting_grd                         true
% 50.95/6.96  --splitting_cvd                         false
% 50.95/6.96  --splitting_cvd_svl                     false
% 50.95/6.96  --splitting_nvd                         32
% 50.95/6.96  --sub_typing                            true
% 50.95/6.96  --prep_gs_sim                           false
% 50.95/6.96  --prep_unflatten                        true
% 50.95/6.96  --prep_res_sim                          true
% 50.95/6.96  --prep_upred                            true
% 50.95/6.96  --prep_sem_filter                       exhaustive
% 50.95/6.96  --prep_sem_filter_out                   false
% 50.95/6.96  --pred_elim                             false
% 50.95/6.96  --res_sim_input                         true
% 50.95/6.96  --eq_ax_congr_red                       true
% 50.95/6.96  --pure_diseq_elim                       true
% 50.95/6.96  --brand_transform                       false
% 50.95/6.96  --non_eq_to_eq                          false
% 50.95/6.96  --prep_def_merge                        true
% 50.95/6.96  --prep_def_merge_prop_impl              false
% 50.95/6.96  --prep_def_merge_mbd                    true
% 50.95/6.96  --prep_def_merge_tr_red                 false
% 50.95/6.96  --prep_def_merge_tr_cl                  false
% 50.95/6.96  --smt_preprocessing                     true
% 50.95/6.96  --smt_ac_axioms                         fast
% 50.95/6.96  --preprocessed_out                      false
% 50.95/6.96  --preprocessed_stats                    false
% 50.95/6.96  
% 50.95/6.96  ------ Abstraction refinement Options
% 50.95/6.96  
% 50.95/6.96  --abstr_ref                             []
% 50.95/6.96  --abstr_ref_prep                        false
% 50.95/6.96  --abstr_ref_until_sat                   false
% 50.95/6.96  --abstr_ref_sig_restrict                funpre
% 50.95/6.96  --abstr_ref_af_restrict_to_split_sk     false
% 50.95/6.96  --abstr_ref_under                       []
% 50.95/6.96  
% 50.95/6.96  ------ SAT Options
% 50.95/6.96  
% 50.95/6.96  --sat_mode                              false
% 50.95/6.96  --sat_fm_restart_options                ""
% 50.95/6.96  --sat_gr_def                            false
% 50.95/6.96  --sat_epr_types                         true
% 50.95/6.96  --sat_non_cyclic_types                  false
% 50.95/6.96  --sat_finite_models                     false
% 50.95/6.96  --sat_fm_lemmas                         false
% 50.95/6.96  --sat_fm_prep                           false
% 50.95/6.96  --sat_fm_uc_incr                        true
% 50.95/6.96  --sat_out_model                         small
% 50.95/6.96  --sat_out_clauses                       false
% 50.95/6.96  
% 50.95/6.96  ------ QBF Options
% 50.95/6.96  
% 50.95/6.96  --qbf_mode                              false
% 50.95/6.96  --qbf_elim_univ                         false
% 50.95/6.96  --qbf_dom_inst                          none
% 50.95/6.96  --qbf_dom_pre_inst                      false
% 50.95/6.96  --qbf_sk_in                             false
% 50.95/6.96  --qbf_pred_elim                         true
% 50.95/6.96  --qbf_split                             512
% 50.95/6.96  
% 50.95/6.96  ------ BMC1 Options
% 50.95/6.96  
% 50.95/6.96  --bmc1_incremental                      false
% 50.95/6.96  --bmc1_axioms                           reachable_all
% 50.95/6.96  --bmc1_min_bound                        0
% 50.95/6.96  --bmc1_max_bound                        -1
% 50.95/6.96  --bmc1_max_bound_default                -1
% 50.95/6.96  --bmc1_symbol_reachability              true
% 50.95/6.96  --bmc1_property_lemmas                  false
% 50.95/6.96  --bmc1_k_induction                      false
% 50.95/6.96  --bmc1_non_equiv_states                 false
% 50.95/6.96  --bmc1_deadlock                         false
% 50.95/6.96  --bmc1_ucm                              false
% 50.95/6.96  --bmc1_add_unsat_core                   none
% 50.95/6.96  --bmc1_unsat_core_children              false
% 50.95/6.96  --bmc1_unsat_core_extrapolate_axioms    false
% 50.95/6.96  --bmc1_out_stat                         full
% 50.95/6.96  --bmc1_ground_init                      false
% 50.95/6.96  --bmc1_pre_inst_next_state              false
% 50.95/6.96  --bmc1_pre_inst_state                   false
% 50.95/6.96  --bmc1_pre_inst_reach_state             false
% 50.95/6.96  --bmc1_out_unsat_core                   false
% 50.95/6.96  --bmc1_aig_witness_out                  false
% 50.95/6.96  --bmc1_verbose                          false
% 50.95/6.96  --bmc1_dump_clauses_tptp                false
% 50.95/6.96  --bmc1_dump_unsat_core_tptp             false
% 50.95/6.96  --bmc1_dump_file                        -
% 50.95/6.96  --bmc1_ucm_expand_uc_limit              128
% 50.95/6.96  --bmc1_ucm_n_expand_iterations          6
% 50.95/6.96  --bmc1_ucm_extend_mode                  1
% 50.95/6.96  --bmc1_ucm_init_mode                    2
% 50.95/6.96  --bmc1_ucm_cone_mode                    none
% 50.95/6.96  --bmc1_ucm_reduced_relation_type        0
% 50.95/6.96  --bmc1_ucm_relax_model                  4
% 50.95/6.96  --bmc1_ucm_full_tr_after_sat            true
% 50.95/6.96  --bmc1_ucm_expand_neg_assumptions       false
% 50.95/6.96  --bmc1_ucm_layered_model                none
% 50.95/6.96  --bmc1_ucm_max_lemma_size               10
% 50.95/6.96  
% 50.95/6.96  ------ AIG Options
% 50.95/6.96  
% 50.95/6.96  --aig_mode                              false
% 50.95/6.96  
% 50.95/6.96  ------ Instantiation Options
% 50.95/6.96  
% 50.95/6.96  --instantiation_flag                    true
% 50.95/6.96  --inst_sos_flag                         false
% 50.95/6.96  --inst_sos_phase                        true
% 50.95/6.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 50.95/6.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 50.95/6.96  --inst_lit_sel_side                     num_symb
% 50.95/6.96  --inst_solver_per_active                1400
% 50.95/6.96  --inst_solver_calls_frac                1.
% 50.95/6.96  --inst_passive_queue_type               priority_queues
% 50.95/6.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 50.95/6.96  --inst_passive_queues_freq              [25;2]
% 50.95/6.96  --inst_dismatching                      true
% 50.95/6.96  --inst_eager_unprocessed_to_passive     true
% 50.95/6.96  --inst_prop_sim_given                   true
% 50.95/6.96  --inst_prop_sim_new                     false
% 50.95/6.96  --inst_subs_new                         false
% 50.95/6.96  --inst_eq_res_simp                      false
% 50.95/6.96  --inst_subs_given                       false
% 50.95/6.96  --inst_orphan_elimination               true
% 50.95/6.96  --inst_learning_loop_flag               true
% 50.95/6.96  --inst_learning_start                   3000
% 50.95/6.96  --inst_learning_factor                  2
% 50.95/6.96  --inst_start_prop_sim_after_learn       3
% 50.95/6.96  --inst_sel_renew                        solver
% 50.95/6.96  --inst_lit_activity_flag                true
% 50.95/6.96  --inst_restr_to_given                   false
% 50.95/6.96  --inst_activity_threshold               500
% 50.95/6.96  --inst_out_proof                        true
% 50.95/6.96  
% 50.95/6.96  ------ Resolution Options
% 50.95/6.96  
% 50.95/6.96  --resolution_flag                       true
% 50.95/6.96  --res_lit_sel                           adaptive
% 50.95/6.96  --res_lit_sel_side                      none
% 50.95/6.96  --res_ordering                          kbo
% 50.95/6.96  --res_to_prop_solver                    active
% 50.95/6.96  --res_prop_simpl_new                    false
% 50.95/6.96  --res_prop_simpl_given                  true
% 50.95/6.96  --res_passive_queue_type                priority_queues
% 50.95/6.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 50.95/6.96  --res_passive_queues_freq               [15;5]
% 50.95/6.96  --res_forward_subs                      full
% 50.95/6.96  --res_backward_subs                     full
% 50.95/6.96  --res_forward_subs_resolution           true
% 50.95/6.96  --res_backward_subs_resolution          true
% 50.95/6.96  --res_orphan_elimination                true
% 50.95/6.96  --res_time_limit                        2.
% 50.95/6.96  --res_out_proof                         true
% 50.95/6.96  
% 50.95/6.96  ------ Superposition Options
% 50.95/6.96  
% 50.95/6.96  --superposition_flag                    true
% 50.95/6.96  --sup_passive_queue_type                priority_queues
% 50.95/6.96  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 50.95/6.96  --sup_passive_queues_freq               [1;4]
% 50.95/6.96  --demod_completeness_check              fast
% 50.95/6.96  --demod_use_ground                      true
% 50.95/6.96  --sup_to_prop_solver                    passive
% 50.95/6.96  --sup_prop_simpl_new                    true
% 50.95/6.96  --sup_prop_simpl_given                  true
% 50.95/6.96  --sup_fun_splitting                     false
% 50.95/6.96  --sup_smt_interval                      50000
% 50.95/6.96  
% 50.95/6.96  ------ Superposition Simplification Setup
% 50.95/6.96  
% 50.95/6.96  --sup_indices_passive                   []
% 50.95/6.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 50.95/6.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 50.95/6.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 50.95/6.96  --sup_full_triv                         [TrivRules;PropSubs]
% 50.95/6.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 50.95/6.96  --sup_full_bw                           [BwDemod]
% 50.95/6.96  --sup_immed_triv                        [TrivRules]
% 50.95/6.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 50.95/6.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 50.95/6.96  --sup_immed_bw_main                     []
% 50.95/6.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 50.95/6.96  --sup_input_triv                        [Unflattening;TrivRules]
% 50.95/6.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 50.95/6.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 50.95/6.96  
% 50.95/6.96  ------ Combination Options
% 50.95/6.96  
% 50.95/6.96  --comb_res_mult                         3
% 50.95/6.96  --comb_sup_mult                         2
% 50.95/6.96  --comb_inst_mult                        10
% 50.95/6.96  
% 50.95/6.96  ------ Debug Options
% 50.95/6.96  
% 50.95/6.96  --dbg_backtrace                         false
% 50.95/6.96  --dbg_dump_prop_clauses                 false
% 50.95/6.96  --dbg_dump_prop_clauses_file            -
% 50.95/6.96  --dbg_out_stat                          false
% 50.95/6.96  ------ Parsing...
% 50.95/6.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 50.95/6.96  
% 50.95/6.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 50.95/6.96  
% 50.95/6.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 50.95/6.96  
% 50.95/6.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 50.95/6.96  ------ Proving...
% 50.95/6.96  ------ Problem Properties 
% 50.95/6.96  
% 50.95/6.96  
% 50.95/6.96  clauses                                 13
% 50.95/6.96  conjectures                             4
% 50.95/6.96  EPR                                     3
% 50.95/6.96  Horn                                    13
% 50.95/6.96  unary                                   8
% 50.95/6.96  binary                                  1
% 50.95/6.96  lits                                    25
% 50.95/6.96  lits eq                                 3
% 50.95/6.96  fd_pure                                 0
% 50.95/6.96  fd_pseudo                               0
% 50.95/6.96  fd_cond                                 0
% 50.95/6.96  fd_pseudo_cond                          0
% 50.95/6.96  AC symbols                              0
% 50.95/6.96  
% 50.95/6.96  ------ Input Options Time Limit: Unbounded
% 50.95/6.96  
% 50.95/6.96  
% 50.95/6.96  ------ 
% 50.95/6.96  Current options:
% 50.95/6.96  ------ 
% 50.95/6.96  
% 50.95/6.96  ------ Input Options
% 50.95/6.96  
% 50.95/6.96  --out_options                           all
% 50.95/6.96  --tptp_safe_out                         true
% 50.95/6.96  --problem_path                          ""
% 50.95/6.96  --include_path                          ""
% 50.95/6.96  --clausifier                            res/vclausify_rel
% 50.95/6.96  --clausifier_options                    --mode clausify
% 50.95/6.96  --stdin                                 false
% 50.95/6.96  --stats_out                             sel
% 50.95/6.96  
% 50.95/6.96  ------ General Options
% 50.95/6.96  
% 50.95/6.96  --fof                                   false
% 50.95/6.96  --time_out_real                         604.99
% 50.95/6.96  --time_out_virtual                      -1.
% 50.95/6.96  --symbol_type_check                     false
% 50.95/6.96  --clausify_out                          false
% 50.95/6.96  --sig_cnt_out                           false
% 50.95/6.96  --trig_cnt_out                          false
% 50.95/6.96  --trig_cnt_out_tolerance                1.
% 50.95/6.96  --trig_cnt_out_sk_spl                   false
% 50.95/6.96  --abstr_cl_out                          false
% 50.95/6.96  
% 50.95/6.96  ------ Global Options
% 50.95/6.96  
% 50.95/6.96  --schedule                              none
% 50.95/6.96  --add_important_lit                     false
% 50.95/6.96  --prop_solver_per_cl                    1000
% 50.95/6.96  --min_unsat_core                        false
% 50.95/6.96  --soft_assumptions                      false
% 50.95/6.96  --soft_lemma_size                       3
% 50.95/6.96  --prop_impl_unit_size                   0
% 50.95/6.96  --prop_impl_unit                        []
% 50.95/6.96  --share_sel_clauses                     true
% 50.95/6.96  --reset_solvers                         false
% 50.95/6.96  --bc_imp_inh                            [conj_cone]
% 50.95/6.96  --conj_cone_tolerance                   3.
% 50.95/6.96  --extra_neg_conj                        none
% 50.95/6.96  --large_theory_mode                     true
% 50.95/6.96  --prolific_symb_bound                   200
% 50.95/6.96  --lt_threshold                          2000
% 50.95/6.96  --clause_weak_htbl                      true
% 50.95/6.96  --gc_record_bc_elim                     false
% 50.95/6.96  
% 50.95/6.96  ------ Preprocessing Options
% 50.95/6.96  
% 50.95/6.96  --preprocessing_flag                    true
% 50.95/6.96  --time_out_prep_mult                    0.1
% 50.95/6.96  --splitting_mode                        input
% 50.95/6.96  --splitting_grd                         true
% 50.95/6.96  --splitting_cvd                         false
% 50.95/6.96  --splitting_cvd_svl                     false
% 50.95/6.96  --splitting_nvd                         32
% 50.95/6.96  --sub_typing                            true
% 50.95/6.96  --prep_gs_sim                           false
% 50.95/6.96  --prep_unflatten                        true
% 50.95/6.96  --prep_res_sim                          true
% 50.95/6.96  --prep_upred                            true
% 50.95/6.96  --prep_sem_filter                       exhaustive
% 50.95/6.96  --prep_sem_filter_out                   false
% 50.95/6.96  --pred_elim                             false
% 50.95/6.96  --res_sim_input                         true
% 50.95/6.96  --eq_ax_congr_red                       true
% 50.95/6.96  --pure_diseq_elim                       true
% 50.95/6.96  --brand_transform                       false
% 50.95/6.96  --non_eq_to_eq                          false
% 50.95/6.96  --prep_def_merge                        true
% 50.95/6.96  --prep_def_merge_prop_impl              false
% 50.95/6.96  --prep_def_merge_mbd                    true
% 50.95/6.96  --prep_def_merge_tr_red                 false
% 50.95/6.96  --prep_def_merge_tr_cl                  false
% 50.95/6.96  --smt_preprocessing                     true
% 50.95/6.96  --smt_ac_axioms                         fast
% 50.95/6.96  --preprocessed_out                      false
% 50.95/6.96  --preprocessed_stats                    false
% 50.95/6.96  
% 50.95/6.96  ------ Abstraction refinement Options
% 50.95/6.96  
% 50.95/6.96  --abstr_ref                             []
% 50.95/6.96  --abstr_ref_prep                        false
% 50.95/6.96  --abstr_ref_until_sat                   false
% 50.95/6.96  --abstr_ref_sig_restrict                funpre
% 50.95/6.96  --abstr_ref_af_restrict_to_split_sk     false
% 50.95/6.96  --abstr_ref_under                       []
% 50.95/6.96  
% 50.95/6.96  ------ SAT Options
% 50.95/6.96  
% 50.95/6.96  --sat_mode                              false
% 50.95/6.96  --sat_fm_restart_options                ""
% 50.95/6.96  --sat_gr_def                            false
% 50.95/6.96  --sat_epr_types                         true
% 50.95/6.96  --sat_non_cyclic_types                  false
% 50.95/6.96  --sat_finite_models                     false
% 50.95/6.96  --sat_fm_lemmas                         false
% 50.95/6.96  --sat_fm_prep                           false
% 50.95/6.96  --sat_fm_uc_incr                        true
% 50.95/6.96  --sat_out_model                         small
% 50.95/6.96  --sat_out_clauses                       false
% 50.95/6.96  
% 50.95/6.96  ------ QBF Options
% 50.95/6.96  
% 50.95/6.96  --qbf_mode                              false
% 50.95/6.96  --qbf_elim_univ                         false
% 50.95/6.96  --qbf_dom_inst                          none
% 50.95/6.96  --qbf_dom_pre_inst                      false
% 50.95/6.96  --qbf_sk_in                             false
% 50.95/6.96  --qbf_pred_elim                         true
% 50.95/6.96  --qbf_split                             512
% 50.95/6.96  
% 50.95/6.96  ------ BMC1 Options
% 50.95/6.96  
% 50.95/6.96  --bmc1_incremental                      false
% 50.95/6.96  --bmc1_axioms                           reachable_all
% 50.95/6.96  --bmc1_min_bound                        0
% 50.95/6.96  --bmc1_max_bound                        -1
% 50.95/6.96  --bmc1_max_bound_default                -1
% 50.95/6.96  --bmc1_symbol_reachability              true
% 50.95/6.96  --bmc1_property_lemmas                  false
% 50.95/6.96  --bmc1_k_induction                      false
% 50.95/6.96  --bmc1_non_equiv_states                 false
% 50.95/6.96  --bmc1_deadlock                         false
% 50.95/6.96  --bmc1_ucm                              false
% 50.95/6.96  --bmc1_add_unsat_core                   none
% 50.95/6.96  --bmc1_unsat_core_children              false
% 50.95/6.96  --bmc1_unsat_core_extrapolate_axioms    false
% 50.95/6.96  --bmc1_out_stat                         full
% 50.95/6.96  --bmc1_ground_init                      false
% 50.95/6.96  --bmc1_pre_inst_next_state              false
% 50.95/6.96  --bmc1_pre_inst_state                   false
% 50.95/6.96  --bmc1_pre_inst_reach_state             false
% 50.95/6.96  --bmc1_out_unsat_core                   false
% 50.95/6.96  --bmc1_aig_witness_out                  false
% 50.95/6.96  --bmc1_verbose                          false
% 50.95/6.96  --bmc1_dump_clauses_tptp                false
% 50.95/6.96  --bmc1_dump_unsat_core_tptp             false
% 50.95/6.96  --bmc1_dump_file                        -
% 50.95/6.96  --bmc1_ucm_expand_uc_limit              128
% 50.95/6.96  --bmc1_ucm_n_expand_iterations          6
% 50.95/6.96  --bmc1_ucm_extend_mode                  1
% 50.95/6.96  --bmc1_ucm_init_mode                    2
% 50.95/6.96  --bmc1_ucm_cone_mode                    none
% 50.95/6.96  --bmc1_ucm_reduced_relation_type        0
% 50.95/6.96  --bmc1_ucm_relax_model                  4
% 50.95/6.96  --bmc1_ucm_full_tr_after_sat            true
% 50.95/6.96  --bmc1_ucm_expand_neg_assumptions       false
% 50.95/6.96  --bmc1_ucm_layered_model                none
% 50.95/6.96  --bmc1_ucm_max_lemma_size               10
% 50.95/6.96  
% 50.95/6.96  ------ AIG Options
% 50.95/6.96  
% 50.95/6.96  --aig_mode                              false
% 50.95/6.96  
% 50.95/6.96  ------ Instantiation Options
% 50.95/6.96  
% 50.95/6.96  --instantiation_flag                    true
% 50.95/6.96  --inst_sos_flag                         false
% 50.95/6.96  --inst_sos_phase                        true
% 50.95/6.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 50.95/6.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 50.95/6.96  --inst_lit_sel_side                     num_symb
% 50.95/6.96  --inst_solver_per_active                1400
% 50.95/6.96  --inst_solver_calls_frac                1.
% 50.95/6.96  --inst_passive_queue_type               priority_queues
% 50.95/6.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 50.95/6.96  --inst_passive_queues_freq              [25;2]
% 50.95/6.96  --inst_dismatching                      true
% 50.95/6.96  --inst_eager_unprocessed_to_passive     true
% 50.95/6.96  --inst_prop_sim_given                   true
% 50.95/6.96  --inst_prop_sim_new                     false
% 50.95/6.96  --inst_subs_new                         false
% 50.95/6.96  --inst_eq_res_simp                      false
% 50.95/6.96  --inst_subs_given                       false
% 50.95/6.96  --inst_orphan_elimination               true
% 50.95/6.96  --inst_learning_loop_flag               true
% 50.95/6.96  --inst_learning_start                   3000
% 50.95/6.96  --inst_learning_factor                  2
% 50.95/6.96  --inst_start_prop_sim_after_learn       3
% 50.95/6.96  --inst_sel_renew                        solver
% 50.95/6.96  --inst_lit_activity_flag                true
% 50.95/6.96  --inst_restr_to_given                   false
% 50.95/6.96  --inst_activity_threshold               500
% 50.95/6.96  --inst_out_proof                        true
% 50.95/6.96  
% 50.95/6.96  ------ Resolution Options
% 50.95/6.96  
% 50.95/6.96  --resolution_flag                       true
% 50.95/6.96  --res_lit_sel                           adaptive
% 50.95/6.96  --res_lit_sel_side                      none
% 50.95/6.96  --res_ordering                          kbo
% 50.95/6.96  --res_to_prop_solver                    active
% 50.95/6.96  --res_prop_simpl_new                    false
% 50.95/6.96  --res_prop_simpl_given                  true
% 50.95/6.96  --res_passive_queue_type                priority_queues
% 50.95/6.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 50.95/6.96  --res_passive_queues_freq               [15;5]
% 50.95/6.96  --res_forward_subs                      full
% 50.95/6.96  --res_backward_subs                     full
% 50.95/6.96  --res_forward_subs_resolution           true
% 50.95/6.96  --res_backward_subs_resolution          true
% 50.95/6.96  --res_orphan_elimination                true
% 50.95/6.96  --res_time_limit                        2.
% 50.95/6.96  --res_out_proof                         true
% 50.95/6.96  
% 50.95/6.96  ------ Superposition Options
% 50.95/6.96  
% 50.95/6.96  --superposition_flag                    true
% 50.95/6.96  --sup_passive_queue_type                priority_queues
% 50.95/6.96  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 50.95/6.96  --sup_passive_queues_freq               [1;4]
% 50.95/6.96  --demod_completeness_check              fast
% 50.95/6.96  --demod_use_ground                      true
% 50.95/6.96  --sup_to_prop_solver                    passive
% 50.95/6.96  --sup_prop_simpl_new                    true
% 50.95/6.96  --sup_prop_simpl_given                  true
% 50.95/6.96  --sup_fun_splitting                     false
% 50.95/6.96  --sup_smt_interval                      50000
% 50.95/6.96  
% 50.95/6.96  ------ Superposition Simplification Setup
% 50.95/6.96  
% 50.95/6.96  --sup_indices_passive                   []
% 50.95/6.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 50.95/6.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 50.95/6.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 50.95/6.96  --sup_full_triv                         [TrivRules;PropSubs]
% 50.95/6.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 50.95/6.96  --sup_full_bw                           [BwDemod]
% 50.95/6.96  --sup_immed_triv                        [TrivRules]
% 50.95/6.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 50.95/6.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 50.95/6.96  --sup_immed_bw_main                     []
% 50.95/6.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 50.95/6.96  --sup_input_triv                        [Unflattening;TrivRules]
% 50.95/6.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 50.95/6.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 50.95/6.96  
% 50.95/6.96  ------ Combination Options
% 50.95/6.96  
% 50.95/6.96  --comb_res_mult                         3
% 50.95/6.96  --comb_sup_mult                         2
% 50.95/6.96  --comb_inst_mult                        10
% 50.95/6.96  
% 50.95/6.96  ------ Debug Options
% 50.95/6.96  
% 50.95/6.96  --dbg_backtrace                         false
% 50.95/6.96  --dbg_dump_prop_clauses                 false
% 50.95/6.96  --dbg_dump_prop_clauses_file            -
% 50.95/6.96  --dbg_out_stat                          false
% 50.95/6.96  
% 50.95/6.96  
% 50.95/6.96  
% 50.95/6.96  
% 50.95/6.96  ------ Proving...
% 50.95/6.96  
% 50.95/6.96  
% 50.95/6.96  % SZS status Theorem for theBenchmark.p
% 50.95/6.96  
% 50.95/6.96  % SZS output start CNFRefutation for theBenchmark.p
% 50.95/6.96  
% 50.95/6.96  fof(f4,axiom,(
% 50.95/6.96    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 50.95/6.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 50.95/6.96  
% 50.95/6.96  fof(f28,plain,(
% 50.95/6.96    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 50.95/6.96    inference(cnf_transformation,[],[f4])).
% 50.95/6.96  
% 50.95/6.96  fof(f8,axiom,(
% 50.95/6.96    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k2_xboole_0(X0,X1)))),
% 50.95/6.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 50.95/6.96  
% 50.95/6.96  fof(f15,plain,(
% 50.95/6.96    ! [X0,X1] : (v1_relat_1(k2_xboole_0(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 50.95/6.96    inference(ennf_transformation,[],[f8])).
% 50.95/6.96  
% 50.95/6.96  fof(f16,plain,(
% 50.95/6.96    ! [X0,X1] : (v1_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 50.95/6.96    inference(flattening,[],[f15])).
% 50.95/6.96  
% 50.95/6.96  fof(f32,plain,(
% 50.95/6.96    ( ! [X0,X1] : (v1_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 50.95/6.96    inference(cnf_transformation,[],[f16])).
% 50.95/6.96  
% 50.95/6.96  fof(f2,axiom,(
% 50.95/6.96    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 50.95/6.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 50.95/6.96  
% 50.95/6.96  fof(f26,plain,(
% 50.95/6.96    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 50.95/6.96    inference(cnf_transformation,[],[f2])).
% 50.95/6.96  
% 50.95/6.96  fof(f6,axiom,(
% 50.95/6.96    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 50.95/6.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 50.95/6.96  
% 50.95/6.96  fof(f30,plain,(
% 50.95/6.96    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 50.95/6.96    inference(cnf_transformation,[],[f6])).
% 50.95/6.96  
% 50.95/6.96  fof(f39,plain,(
% 50.95/6.96    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k6_subset_1(X1,X0))) )),
% 50.95/6.96    inference(definition_unfolding,[],[f26,f30])).
% 50.95/6.96  
% 50.95/6.96  fof(f1,axiom,(
% 50.95/6.96    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 50.95/6.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 50.95/6.96  
% 50.95/6.96  fof(f25,plain,(
% 50.95/6.96    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 50.95/6.96    inference(cnf_transformation,[],[f1])).
% 50.95/6.96  
% 50.95/6.96  fof(f9,axiom,(
% 50.95/6.96    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))))))),
% 50.95/6.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 50.95/6.96  
% 50.95/6.96  fof(f17,plain,(
% 50.95/6.96    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 50.95/6.96    inference(ennf_transformation,[],[f9])).
% 50.95/6.96  
% 50.95/6.96  fof(f18,plain,(
% 50.95/6.96    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 50.95/6.96    inference(flattening,[],[f17])).
% 50.95/6.96  
% 50.95/6.96  fof(f33,plain,(
% 50.95/6.96    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 50.95/6.96    inference(cnf_transformation,[],[f18])).
% 50.95/6.96  
% 50.95/6.96  fof(f10,axiom,(
% 50.95/6.96    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k2_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)) = k5_relat_1(X0,k2_xboole_0(X1,X2)))))),
% 50.95/6.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 50.95/6.96  
% 50.95/6.96  fof(f19,plain,(
% 50.95/6.96    ! [X0] : (! [X1] : (! [X2] : (k2_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)) = k5_relat_1(X0,k2_xboole_0(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 50.95/6.96    inference(ennf_transformation,[],[f10])).
% 50.95/6.96  
% 50.95/6.96  fof(f34,plain,(
% 50.95/6.96    ( ! [X2,X0,X1] : (k2_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)) = k5_relat_1(X0,k2_xboole_0(X1,X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 50.95/6.96    inference(cnf_transformation,[],[f19])).
% 50.95/6.96  
% 50.95/6.96  fof(f5,axiom,(
% 50.95/6.96    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 50.95/6.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 50.95/6.96  
% 50.95/6.96  fof(f29,plain,(
% 50.95/6.96    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 50.95/6.96    inference(cnf_transformation,[],[f5])).
% 50.95/6.96  
% 50.95/6.96  fof(f7,axiom,(
% 50.95/6.96    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 50.95/6.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 50.95/6.96  
% 50.95/6.96  fof(f14,plain,(
% 50.95/6.96    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 50.95/6.96    inference(ennf_transformation,[],[f7])).
% 50.95/6.96  
% 50.95/6.96  fof(f31,plain,(
% 50.95/6.96    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 50.95/6.96    inference(cnf_transformation,[],[f14])).
% 50.95/6.96  
% 50.95/6.96  fof(f3,axiom,(
% 50.95/6.96    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 50.95/6.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 50.95/6.96  
% 50.95/6.96  fof(f13,plain,(
% 50.95/6.96    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 50.95/6.96    inference(ennf_transformation,[],[f3])).
% 50.95/6.96  
% 50.95/6.96  fof(f27,plain,(
% 50.95/6.96    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 50.95/6.96    inference(cnf_transformation,[],[f13])).
% 50.95/6.96  
% 50.95/6.96  fof(f40,plain,(
% 50.95/6.96    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 50.95/6.96    inference(definition_unfolding,[],[f27,f30])).
% 50.95/6.96  
% 50.95/6.96  fof(f11,conjecture,(
% 50.95/6.96    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2))))))),
% 50.95/6.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 50.95/6.96  
% 50.95/6.96  fof(f12,negated_conjecture,(
% 50.95/6.96    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2))))))),
% 50.95/6.96    inference(negated_conjecture,[],[f11])).
% 50.95/6.96  
% 50.95/6.96  fof(f20,plain,(
% 50.95/6.96    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 50.95/6.96    inference(ennf_transformation,[],[f12])).
% 50.95/6.96  
% 50.95/6.96  fof(f23,plain,(
% 50.95/6.96    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2))) & v1_relat_1(X2)) => (~r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,sK2)),k5_relat_1(X0,k6_subset_1(X1,sK2))) & v1_relat_1(sK2))) )),
% 50.95/6.96    introduced(choice_axiom,[])).
% 50.95/6.96  
% 50.95/6.96  fof(f22,plain,(
% 50.95/6.96    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~r1_tarski(k6_subset_1(k5_relat_1(X0,sK1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(sK1,X2))) & v1_relat_1(X2)) & v1_relat_1(sK1))) )),
% 50.95/6.96    introduced(choice_axiom,[])).
% 50.95/6.96  
% 50.95/6.96  fof(f21,plain,(
% 50.95/6.96    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k6_subset_1(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2)),k5_relat_1(sK0,k6_subset_1(X1,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 50.95/6.96    introduced(choice_axiom,[])).
% 50.95/6.96  
% 50.95/6.96  fof(f24,plain,(
% 50.95/6.96    ((~r1_tarski(k6_subset_1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)),k5_relat_1(sK0,k6_subset_1(sK1,sK2))) & v1_relat_1(sK2)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 50.95/6.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f23,f22,f21])).
% 50.95/6.96  
% 50.95/6.96  fof(f38,plain,(
% 50.95/6.96    ~r1_tarski(k6_subset_1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)),k5_relat_1(sK0,k6_subset_1(sK1,sK2)))),
% 50.95/6.96    inference(cnf_transformation,[],[f24])).
% 50.95/6.96  
% 50.95/6.96  fof(f37,plain,(
% 50.95/6.96    v1_relat_1(sK2)),
% 50.95/6.96    inference(cnf_transformation,[],[f24])).
% 50.95/6.96  
% 50.95/6.96  fof(f36,plain,(
% 50.95/6.96    v1_relat_1(sK1)),
% 50.95/6.96    inference(cnf_transformation,[],[f24])).
% 50.95/6.96  
% 50.95/6.96  fof(f35,plain,(
% 50.95/6.96    v1_relat_1(sK0)),
% 50.95/6.96    inference(cnf_transformation,[],[f24])).
% 50.95/6.96  
% 50.95/6.96  cnf(c_3,plain,
% 50.95/6.96      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 50.95/6.96      inference(cnf_transformation,[],[f28]) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_112,plain,
% 50.95/6.96      ( r1_tarski(X0_38,k2_xboole_0(X0_38,X1_38)) ),
% 50.95/6.96      inference(subtyping,[status(esa)],[c_3]) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_165014,plain,
% 50.95/6.96      ( r1_tarski(sK1,k2_xboole_0(sK1,X0_38)) ),
% 50.95/6.96      inference(instantiation,[status(thm)],[c_112]) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_181709,plain,
% 50.95/6.96      ( r1_tarski(sK1,k2_xboole_0(sK1,sK2)) ),
% 50.95/6.96      inference(instantiation,[status(thm)],[c_165014]) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_122,plain,
% 50.95/6.96      ( ~ r1_tarski(X0_38,X1_38)
% 50.95/6.96      | r1_tarski(X2_38,X3_38)
% 50.95/6.96      | X2_38 != X0_38
% 50.95/6.96      | X3_38 != X1_38 ),
% 50.95/6.96      theory(equality) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_155642,plain,
% 50.95/6.96      ( r1_tarski(X0_38,X1_38)
% 50.95/6.96      | ~ r1_tarski(X2_38,k2_xboole_0(X3_38,X4_38))
% 50.95/6.96      | X0_38 != X2_38
% 50.95/6.96      | X1_38 != k2_xboole_0(X3_38,X4_38) ),
% 50.95/6.96      inference(instantiation,[status(thm)],[c_122]) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_155886,plain,
% 50.95/6.96      ( ~ r1_tarski(X0_38,k2_xboole_0(X1_38,X2_38))
% 50.95/6.96      | r1_tarski(X3_38,k2_xboole_0(X4_38,X5_38))
% 50.95/6.96      | X3_38 != X0_38
% 50.95/6.96      | k2_xboole_0(X4_38,X5_38) != k2_xboole_0(X1_38,X2_38) ),
% 50.95/6.96      inference(instantiation,[status(thm)],[c_155642]) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_158351,plain,
% 50.95/6.96      ( ~ r1_tarski(X0_38,k2_xboole_0(X1_38,X2_38))
% 50.95/6.96      | r1_tarski(sK1,k2_xboole_0(sK2,k6_subset_1(sK1,sK2)))
% 50.95/6.96      | k2_xboole_0(sK2,k6_subset_1(sK1,sK2)) != k2_xboole_0(X1_38,X2_38)
% 50.95/6.96      | sK1 != X0_38 ),
% 50.95/6.96      inference(instantiation,[status(thm)],[c_155886]) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_160191,plain,
% 50.95/6.96      ( ~ r1_tarski(sK1,k2_xboole_0(X0_38,X1_38))
% 50.95/6.96      | r1_tarski(sK1,k2_xboole_0(sK2,k6_subset_1(sK1,sK2)))
% 50.95/6.96      | k2_xboole_0(sK2,k6_subset_1(sK1,sK2)) != k2_xboole_0(X0_38,X1_38)
% 50.95/6.96      | sK1 != sK1 ),
% 50.95/6.96      inference(instantiation,[status(thm)],[c_158351]) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_167005,plain,
% 50.95/6.96      ( r1_tarski(sK1,k2_xboole_0(sK2,k6_subset_1(sK1,sK2)))
% 50.95/6.96      | ~ r1_tarski(sK1,k2_xboole_0(sK1,sK2))
% 50.95/6.96      | k2_xboole_0(sK2,k6_subset_1(sK1,sK2)) != k2_xboole_0(sK1,sK2)
% 50.95/6.96      | sK1 != sK1 ),
% 50.95/6.96      inference(instantiation,[status(thm)],[c_160191]) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_6,plain,
% 50.95/6.96      ( ~ v1_relat_1(X0)
% 50.95/6.96      | ~ v1_relat_1(X1)
% 50.95/6.96      | v1_relat_1(k2_xboole_0(X0,X1)) ),
% 50.95/6.96      inference(cnf_transformation,[],[f32]) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_109,plain,
% 50.95/6.96      ( ~ v1_relat_1(X0_38)
% 50.95/6.96      | ~ v1_relat_1(X1_38)
% 50.95/6.96      | v1_relat_1(k2_xboole_0(X0_38,X1_38)) ),
% 50.95/6.96      inference(subtyping,[status(esa)],[c_6]) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_103519,plain,
% 50.95/6.96      ( ~ v1_relat_1(k6_subset_1(sK1,sK2))
% 50.95/6.96      | v1_relat_1(k2_xboole_0(sK2,k6_subset_1(sK1,sK2)))
% 50.95/6.96      | ~ v1_relat_1(sK2) ),
% 50.95/6.96      inference(instantiation,[status(thm)],[c_109]) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_119,plain,
% 50.95/6.96      ( X0_38 != X1_38 | X2_38 != X1_38 | X2_38 = X0_38 ),
% 50.95/6.96      theory(equality) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_502,plain,
% 50.95/6.96      ( X0_38 != X1_38
% 50.95/6.96      | X0_38 = k2_xboole_0(X2_38,X3_38)
% 50.95/6.96      | k2_xboole_0(X2_38,X3_38) != X1_38 ),
% 50.95/6.96      inference(instantiation,[status(thm)],[c_119]) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_731,plain,
% 50.95/6.96      ( X0_38 != k2_xboole_0(X1_38,X2_38)
% 50.95/6.96      | X0_38 = k2_xboole_0(X2_38,X1_38)
% 50.95/6.96      | k2_xboole_0(X2_38,X1_38) != k2_xboole_0(X1_38,X2_38) ),
% 50.95/6.96      inference(instantiation,[status(thm)],[c_502]) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_1236,plain,
% 50.95/6.96      ( k2_xboole_0(X0_38,X1_38) != k2_xboole_0(X1_38,X0_38)
% 50.95/6.96      | k2_xboole_0(X1_38,k6_subset_1(X0_38,X1_38)) != k2_xboole_0(X1_38,X0_38)
% 50.95/6.96      | k2_xboole_0(X1_38,k6_subset_1(X0_38,X1_38)) = k2_xboole_0(X0_38,X1_38) ),
% 50.95/6.96      inference(instantiation,[status(thm)],[c_731]) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_52997,plain,
% 50.95/6.96      ( k2_xboole_0(sK2,k6_subset_1(sK1,sK2)) != k2_xboole_0(sK2,sK1)
% 50.95/6.96      | k2_xboole_0(sK2,k6_subset_1(sK1,sK2)) = k2_xboole_0(sK1,sK2)
% 50.95/6.96      | k2_xboole_0(sK1,sK2) != k2_xboole_0(sK2,sK1) ),
% 50.95/6.96      inference(instantiation,[status(thm)],[c_1236]) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_1,plain,
% 50.95/6.96      ( k2_xboole_0(X0,k6_subset_1(X1,X0)) = k2_xboole_0(X0,X1) ),
% 50.95/6.96      inference(cnf_transformation,[],[f39]) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_114,plain,
% 50.95/6.96      ( k2_xboole_0(X0_38,k6_subset_1(X1_38,X0_38)) = k2_xboole_0(X0_38,X1_38) ),
% 50.95/6.96      inference(subtyping,[status(esa)],[c_1]) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_52461,plain,
% 50.95/6.96      ( k2_xboole_0(sK2,k6_subset_1(sK1,sK2)) = k2_xboole_0(sK2,sK1) ),
% 50.95/6.96      inference(instantiation,[status(thm)],[c_114]) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_0,plain,
% 50.95/6.96      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 50.95/6.96      inference(cnf_transformation,[],[f25]) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_115,plain,
% 50.95/6.96      ( k2_xboole_0(X0_38,X1_38) = k2_xboole_0(X1_38,X0_38) ),
% 50.95/6.96      inference(subtyping,[status(esa)],[c_0]) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_52020,plain,
% 50.95/6.96      ( k2_xboole_0(sK1,sK2) = k2_xboole_0(sK2,sK1) ),
% 50.95/6.96      inference(instantiation,[status(thm)],[c_115]) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_7,plain,
% 50.95/6.96      ( ~ r1_tarski(X0,X1)
% 50.95/6.96      | r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
% 50.95/6.96      | ~ v1_relat_1(X0)
% 50.95/6.96      | ~ v1_relat_1(X1)
% 50.95/6.96      | ~ v1_relat_1(X2) ),
% 50.95/6.96      inference(cnf_transformation,[],[f33]) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_108,plain,
% 50.95/6.96      ( ~ r1_tarski(X0_38,X1_38)
% 50.95/6.96      | r1_tarski(k5_relat_1(X2_38,X0_38),k5_relat_1(X2_38,X1_38))
% 50.95/6.96      | ~ v1_relat_1(X0_38)
% 50.95/6.96      | ~ v1_relat_1(X1_38)
% 50.95/6.96      | ~ v1_relat_1(X2_38) ),
% 50.95/6.96      inference(subtyping,[status(esa)],[c_7]) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_606,plain,
% 50.95/6.96      ( ~ r1_tarski(X0_38,k2_xboole_0(X1_38,X2_38))
% 50.95/6.96      | r1_tarski(k5_relat_1(X3_38,X0_38),k5_relat_1(X3_38,k2_xboole_0(X1_38,X2_38)))
% 50.95/6.96      | ~ v1_relat_1(X0_38)
% 50.95/6.96      | ~ v1_relat_1(X3_38)
% 50.95/6.96      | ~ v1_relat_1(k2_xboole_0(X1_38,X2_38)) ),
% 50.95/6.96      inference(instantiation,[status(thm)],[c_108]) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_50187,plain,
% 50.95/6.96      ( r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK0,k2_xboole_0(sK2,k6_subset_1(sK1,sK2))))
% 50.95/6.96      | ~ r1_tarski(sK1,k2_xboole_0(sK2,k6_subset_1(sK1,sK2)))
% 50.95/6.96      | ~ v1_relat_1(k2_xboole_0(sK2,k6_subset_1(sK1,sK2)))
% 50.95/6.96      | ~ v1_relat_1(sK1)
% 50.95/6.96      | ~ v1_relat_1(sK0) ),
% 50.95/6.96      inference(instantiation,[status(thm)],[c_606]) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_8,plain,
% 50.95/6.96      ( ~ v1_relat_1(X0)
% 50.95/6.96      | ~ v1_relat_1(X1)
% 50.95/6.96      | ~ v1_relat_1(X2)
% 50.95/6.96      | k2_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)) = k5_relat_1(X0,k2_xboole_0(X1,X2)) ),
% 50.95/6.96      inference(cnf_transformation,[],[f34]) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_107,plain,
% 50.95/6.96      ( ~ v1_relat_1(X0_38)
% 50.95/6.96      | ~ v1_relat_1(X1_38)
% 50.95/6.96      | ~ v1_relat_1(X2_38)
% 50.95/6.96      | k2_xboole_0(k5_relat_1(X0_38,X1_38),k5_relat_1(X0_38,X2_38)) = k5_relat_1(X0_38,k2_xboole_0(X1_38,X2_38)) ),
% 50.95/6.96      inference(subtyping,[status(esa)],[c_8]) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_11541,plain,
% 50.95/6.96      ( ~ v1_relat_1(X0_38)
% 50.95/6.96      | ~ v1_relat_1(X1_38)
% 50.95/6.96      | ~ v1_relat_1(sK0)
% 50.95/6.96      | k2_xboole_0(k5_relat_1(sK0,X0_38),k5_relat_1(sK0,X1_38)) = k5_relat_1(sK0,k2_xboole_0(X0_38,X1_38)) ),
% 50.95/6.96      inference(instantiation,[status(thm)],[c_107]) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_33628,plain,
% 50.95/6.96      ( ~ v1_relat_1(k6_subset_1(sK1,sK2))
% 50.95/6.96      | ~ v1_relat_1(sK2)
% 50.95/6.96      | ~ v1_relat_1(sK0)
% 50.95/6.96      | k2_xboole_0(k5_relat_1(sK0,sK2),k5_relat_1(sK0,k6_subset_1(sK1,sK2))) = k5_relat_1(sK0,k2_xboole_0(sK2,k6_subset_1(sK1,sK2))) ),
% 50.95/6.96      inference(instantiation,[status(thm)],[c_11541]) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_4,plain,
% 50.95/6.96      ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
% 50.95/6.96      inference(cnf_transformation,[],[f29]) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_111,plain,
% 50.95/6.96      ( m1_subset_1(k6_subset_1(X0_38,X1_38),k1_zfmisc_1(X0_38)) ),
% 50.95/6.96      inference(subtyping,[status(esa)],[c_4]) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_13574,plain,
% 50.95/6.96      ( m1_subset_1(k6_subset_1(sK1,sK2),k1_zfmisc_1(sK1)) ),
% 50.95/6.96      inference(instantiation,[status(thm)],[c_111]) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_5,plain,
% 50.95/6.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 50.95/6.96      | ~ v1_relat_1(X1)
% 50.95/6.96      | v1_relat_1(X0) ),
% 50.95/6.96      inference(cnf_transformation,[],[f31]) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_110,plain,
% 50.95/6.96      ( ~ m1_subset_1(X0_38,k1_zfmisc_1(X1_38))
% 50.95/6.96      | ~ v1_relat_1(X1_38)
% 50.95/6.96      | v1_relat_1(X0_38) ),
% 50.95/6.96      inference(subtyping,[status(esa)],[c_5]) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_5345,plain,
% 50.95/6.96      ( ~ m1_subset_1(k6_subset_1(sK1,sK2),k1_zfmisc_1(X0_38))
% 50.95/6.96      | ~ v1_relat_1(X0_38)
% 50.95/6.96      | v1_relat_1(k6_subset_1(sK1,sK2)) ),
% 50.95/6.96      inference(instantiation,[status(thm)],[c_110]) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_13573,plain,
% 50.95/6.96      ( ~ m1_subset_1(k6_subset_1(sK1,sK2),k1_zfmisc_1(sK1))
% 50.95/6.96      | v1_relat_1(k6_subset_1(sK1,sK2))
% 50.95/6.96      | ~ v1_relat_1(sK1) ),
% 50.95/6.96      inference(instantiation,[status(thm)],[c_5345]) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_921,plain,
% 50.95/6.96      ( r1_tarski(X0_38,X1_38)
% 50.95/6.96      | ~ r1_tarski(k5_relat_1(X2_38,X3_38),k5_relat_1(X2_38,k2_xboole_0(X4_38,X5_38)))
% 50.95/6.96      | X0_38 != k5_relat_1(X2_38,X3_38)
% 50.95/6.96      | X1_38 != k5_relat_1(X2_38,k2_xboole_0(X4_38,X5_38)) ),
% 50.95/6.96      inference(instantiation,[status(thm)],[c_122]) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_1268,plain,
% 50.95/6.96      ( r1_tarski(X0_38,k2_xboole_0(k5_relat_1(X1_38,X2_38),k5_relat_1(X1_38,X3_38)))
% 50.95/6.96      | ~ r1_tarski(k5_relat_1(X1_38,X4_38),k5_relat_1(X1_38,k2_xboole_0(X2_38,X3_38)))
% 50.95/6.96      | X0_38 != k5_relat_1(X1_38,X4_38)
% 50.95/6.96      | k2_xboole_0(k5_relat_1(X1_38,X2_38),k5_relat_1(X1_38,X3_38)) != k5_relat_1(X1_38,k2_xboole_0(X2_38,X3_38)) ),
% 50.95/6.96      inference(instantiation,[status(thm)],[c_921]) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_3196,plain,
% 50.95/6.96      ( ~ r1_tarski(k5_relat_1(X0_38,X1_38),k5_relat_1(X0_38,k2_xboole_0(X2_38,X3_38)))
% 50.95/6.96      | r1_tarski(k5_relat_1(X4_38,X5_38),k2_xboole_0(k5_relat_1(X0_38,X2_38),k5_relat_1(X0_38,X3_38)))
% 50.95/6.96      | k5_relat_1(X4_38,X5_38) != k5_relat_1(X0_38,X1_38)
% 50.95/6.96      | k2_xboole_0(k5_relat_1(X0_38,X2_38),k5_relat_1(X0_38,X3_38)) != k5_relat_1(X0_38,k2_xboole_0(X2_38,X3_38)) ),
% 50.95/6.96      inference(instantiation,[status(thm)],[c_1268]) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_7280,plain,
% 50.95/6.96      ( ~ r1_tarski(k5_relat_1(sK0,X0_38),k5_relat_1(sK0,k2_xboole_0(sK2,k6_subset_1(sK1,sK2))))
% 50.95/6.96      | r1_tarski(k5_relat_1(sK0,sK1),k2_xboole_0(k5_relat_1(sK0,sK2),k5_relat_1(sK0,k6_subset_1(sK1,sK2))))
% 50.95/6.96      | k5_relat_1(sK0,sK1) != k5_relat_1(sK0,X0_38)
% 50.95/6.96      | k2_xboole_0(k5_relat_1(sK0,sK2),k5_relat_1(sK0,k6_subset_1(sK1,sK2))) != k5_relat_1(sK0,k2_xboole_0(sK2,k6_subset_1(sK1,sK2))) ),
% 50.95/6.96      inference(instantiation,[status(thm)],[c_3196]) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_8728,plain,
% 50.95/6.96      ( ~ r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK0,k2_xboole_0(sK2,k6_subset_1(sK1,sK2))))
% 50.95/6.96      | r1_tarski(k5_relat_1(sK0,sK1),k2_xboole_0(k5_relat_1(sK0,sK2),k5_relat_1(sK0,k6_subset_1(sK1,sK2))))
% 50.95/6.96      | k5_relat_1(sK0,sK1) != k5_relat_1(sK0,sK1)
% 50.95/6.96      | k2_xboole_0(k5_relat_1(sK0,sK2),k5_relat_1(sK0,k6_subset_1(sK1,sK2))) != k5_relat_1(sK0,k2_xboole_0(sK2,k6_subset_1(sK1,sK2))) ),
% 50.95/6.96      inference(instantiation,[status(thm)],[c_7280]) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_117,plain,( X0_38 = X0_38 ),theory(equality) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_1092,plain,
% 50.95/6.96      ( sK1 = sK1 ),
% 50.95/6.96      inference(instantiation,[status(thm)],[c_117]) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_692,plain,
% 50.95/6.96      ( k5_relat_1(X0_38,X1_38) = k5_relat_1(X0_38,X1_38) ),
% 50.95/6.96      inference(instantiation,[status(thm)],[c_117]) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_1089,plain,
% 50.95/6.96      ( k5_relat_1(sK0,sK1) = k5_relat_1(sK0,sK1) ),
% 50.95/6.96      inference(instantiation,[status(thm)],[c_692]) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_2,plain,
% 50.95/6.96      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
% 50.95/6.96      | r1_tarski(k6_subset_1(X0,X1),X2) ),
% 50.95/6.96      inference(cnf_transformation,[],[f40]) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_113,plain,
% 50.95/6.96      ( ~ r1_tarski(X0_38,k2_xboole_0(X1_38,X2_38))
% 50.95/6.96      | r1_tarski(k6_subset_1(X0_38,X1_38),X2_38) ),
% 50.95/6.96      inference(subtyping,[status(esa)],[c_2]) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_432,plain,
% 50.95/6.96      ( ~ r1_tarski(k5_relat_1(sK0,sK1),k2_xboole_0(k5_relat_1(sK0,sK2),k5_relat_1(sK0,k6_subset_1(sK1,sK2))))
% 50.95/6.96      | r1_tarski(k6_subset_1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)),k5_relat_1(sK0,k6_subset_1(sK1,sK2))) ),
% 50.95/6.96      inference(instantiation,[status(thm)],[c_113]) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_9,negated_conjecture,
% 50.95/6.96      ( ~ r1_tarski(k6_subset_1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)),k5_relat_1(sK0,k6_subset_1(sK1,sK2))) ),
% 50.95/6.96      inference(cnf_transformation,[],[f38]) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_10,negated_conjecture,
% 50.95/6.96      ( v1_relat_1(sK2) ),
% 50.95/6.96      inference(cnf_transformation,[],[f37]) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_11,negated_conjecture,
% 50.95/6.96      ( v1_relat_1(sK1) ),
% 50.95/6.96      inference(cnf_transformation,[],[f36]) ).
% 50.95/6.96  
% 50.95/6.96  cnf(c_12,negated_conjecture,
% 50.95/6.96      ( v1_relat_1(sK0) ),
% 50.95/6.96      inference(cnf_transformation,[],[f35]) ).
% 50.95/6.96  
% 50.95/6.96  cnf(contradiction,plain,
% 50.95/6.96      ( $false ),
% 50.95/6.96      inference(minisat,
% 50.95/6.96                [status(thm)],
% 50.95/6.96                [c_181709,c_167005,c_103519,c_52997,c_52461,c_52020,
% 50.95/6.96                 c_50187,c_33628,c_13574,c_13573,c_8728,c_1092,c_1089,
% 50.95/6.96                 c_432,c_9,c_10,c_11,c_12]) ).
% 50.95/6.96  
% 50.95/6.96  
% 50.95/6.96  % SZS output end CNFRefutation for theBenchmark.p
% 50.95/6.96  
% 50.95/6.96  ------                               Statistics
% 50.95/6.96  
% 50.95/6.96  ------ Selected
% 50.95/6.96  
% 50.95/6.96  total_time:                             6.125
% 50.95/6.96  
%------------------------------------------------------------------------------
