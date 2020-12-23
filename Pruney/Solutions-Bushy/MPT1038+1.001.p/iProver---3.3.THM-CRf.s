%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1038+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:44 EST 2020

% Result     : Theorem 1.09s
% Output     : CNFRefutation 1.09s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 230 expanded)
%              Number of clauses        :   56 (  72 expanded)
%              Number of leaves         :   11 (  66 expanded)
%              Depth                    :   18
%              Number of atoms          :  431 (1737 expanded)
%              Number of equality atoms :   25 (  37 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   20 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_1(X4) )
             => ( ( v1_partfun1(X4,X0)
                  & r1_partfun1(X3,X4)
                  & r1_partfun1(X2,X4) )
               => r1_partfun1(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( r1_partfun1(X2,X3)
              | ~ v1_partfun1(X4,X0)
              | ~ r1_partfun1(X3,X4)
              | ~ r1_partfun1(X2,X4)
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( r1_partfun1(X2,X3)
              | ~ v1_partfun1(X4,X0)
              | ~ r1_partfun1(X3,X4)
              | ~ r1_partfun1(X2,X4)
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r1_partfun1(X2,X3)
      | ~ v1_partfun1(X4,X0)
      | ~ r1_partfun1(X3,X4)
      | ~ r1_partfun1(X2,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f11])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_1(X2) )
         => ! [X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
                & v1_funct_2(X3,X0,X0)
                & v1_funct_1(X3) )
             => ( ( r1_partfun1(X2,X3)
                  & r1_partfun1(X1,X3) )
               => r1_partfun1(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_1(X2) )
           => ! [X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
                  & v1_funct_2(X3,X0,X0)
                  & v1_funct_1(X3) )
               => ( ( r1_partfun1(X2,X3)
                    & r1_partfun1(X1,X3) )
                 => r1_partfun1(X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_partfun1(X1,X2)
              & r1_partfun1(X2,X3)
              & r1_partfun1(X1,X3)
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X3,X0,X0)
              & v1_funct_1(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_partfun1(X1,X2)
              & r1_partfun1(X2,X3)
              & r1_partfun1(X1,X3)
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X3,X0,X0)
              & v1_funct_1(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_partfun1(X1,X2)
          & r1_partfun1(X2,X3)
          & r1_partfun1(X1,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X3,X0,X0)
          & v1_funct_1(X3) )
     => ( ~ r1_partfun1(X1,X2)
        & r1_partfun1(X2,sK3)
        & r1_partfun1(X1,sK3)
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(sK3,X0,X0)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_partfun1(X1,X2)
              & r1_partfun1(X2,X3)
              & r1_partfun1(X1,X3)
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X3,X0,X0)
              & v1_funct_1(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_1(X2) )
     => ( ? [X3] :
            ( ~ r1_partfun1(X1,sK2)
            & r1_partfun1(sK2,X3)
            & r1_partfun1(X1,X3)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X3,X0,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_partfun1(X1,X2)
                & r1_partfun1(X2,X3)
                & r1_partfun1(X1,X3)
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
                & v1_funct_2(X3,X0,X0)
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_partfun1(sK1,X2)
              & r1_partfun1(X2,X3)
              & r1_partfun1(sK1,X3)
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
              & v1_funct_2(X3,sK0,sK0)
              & v1_funct_1(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v1_funct_1(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ~ r1_partfun1(sK1,sK2)
    & r1_partfun1(sK2,sK3)
    & r1_partfun1(sK1,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK3,sK0,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f22,f21,f20])).

fof(f36,plain,(
    v1_funct_2(sK3,sK0,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f35,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f37,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => r1_partfun1(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_partfun1(X0,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_partfun1(X0,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_partfun1(X0,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f40,plain,(
    ~ r1_partfun1(sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f39,plain,(
    r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f38,plain,(
    r1_partfun1(sK1,sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f34,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f33,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f32,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f31,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_353,plain,
    ( ~ r1_partfun1(X0_41,X1_41)
    | r1_partfun1(X2_41,X3_41)
    | X2_41 != X0_41
    | X3_41 != X1_41 ),
    theory(equality)).

cnf(c_1416,plain,
    ( ~ r1_partfun1(X0_41,X1_41)
    | r1_partfun1(sK1,sK2)
    | sK2 != X1_41
    | sK1 != X0_41 ),
    inference(instantiation,[status(thm)],[c_353])).

cnf(c_1418,plain,
    ( ~ r1_partfun1(sK0,sK0)
    | r1_partfun1(sK1,sK2)
    | sK2 != sK0
    | sK1 != sK0 ),
    inference(instantiation,[status(thm)],[c_1416])).

cnf(c_5,plain,
    ( ~ r1_partfun1(X0,X1)
    | ~ r1_partfun1(X2,X1)
    | r1_partfun1(X2,X0)
    | ~ v1_partfun1(X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_2,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_11,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_166,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | sK0 != X2
    | sK0 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_11])).

cnf(c_167,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK0) ),
    inference(unflattening,[status(thm)],[c_166])).

cnf(c_12,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_169,plain,
    ( v1_partfun1(sK3,sK0)
    | v1_xboole_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_167,c_12,c_10])).

cnf(c_183,plain,
    ( ~ r1_partfun1(X0,X1)
    | ~ r1_partfun1(X2,X1)
    | r1_partfun1(X2,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | v1_xboole_0(sK0)
    | sK0 != X3
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_169])).

cnf(c_184,plain,
    ( r1_partfun1(X0,X1)
    | ~ r1_partfun1(X0,sK3)
    | ~ r1_partfun1(X1,sK3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK0) ),
    inference(unflattening,[status(thm)],[c_183])).

cnf(c_188,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
    | ~ r1_partfun1(X1,sK3)
    | ~ r1_partfun1(X0,sK3)
    | r1_partfun1(X0,X1)
    | v1_xboole_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_184,c_12])).

cnf(c_189,plain,
    ( r1_partfun1(X0,X1)
    | ~ r1_partfun1(X0,sK3)
    | ~ r1_partfun1(X1,sK3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v1_xboole_0(sK0) ),
    inference(renaming,[status(thm)],[c_188])).

cnf(c_326,plain,
    ( r1_partfun1(X0_41,X1_41)
    | ~ r1_partfun1(X0_41,sK3)
    | ~ r1_partfun1(X1_41,sK3)
    | ~ m1_subset_1(X1_41,k1_zfmisc_1(k2_zfmisc_1(sK0,X2_41)))
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(k2_zfmisc_1(sK0,X2_41)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X2_41)))
    | ~ v1_funct_1(X0_41)
    | ~ v1_funct_1(X1_41)
    | v1_xboole_0(sK0) ),
    inference(subtyping,[status(esa)],[c_189])).

cnf(c_1129,plain,
    ( ~ r1_partfun1(X0_41,sK3)
    | r1_partfun1(sK1,X0_41)
    | ~ r1_partfun1(sK1,sK3)
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(k2_zfmisc_1(sK0,X1_41)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1_41)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X1_41)))
    | ~ v1_funct_1(X0_41)
    | ~ v1_funct_1(sK1)
    | v1_xboole_0(sK0) ),
    inference(instantiation,[status(thm)],[c_326])).

cnf(c_1179,plain,
    ( ~ r1_partfun1(sK2,sK3)
    | ~ r1_partfun1(sK1,sK3)
    | r1_partfun1(sK1,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_41)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_41)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_41)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK1)
    | v1_xboole_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1129])).

cnf(c_1181,plain,
    ( ~ r1_partfun1(sK2,sK3)
    | ~ r1_partfun1(sK1,sK3)
    | r1_partfun1(sK1,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK1)
    | v1_xboole_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1179])).

cnf(c_6,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_336,plain,
    ( ~ v1_xboole_0(X0_41)
    | ~ v1_xboole_0(X1_41)
    | X1_41 = X0_41 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1014,plain,
    ( ~ v1_xboole_0(X0_41)
    | ~ v1_xboole_0(sK1)
    | sK1 = X0_41 ),
    inference(instantiation,[status(thm)],[c_336])).

cnf(c_1016,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ v1_xboole_0(sK1)
    | sK1 = sK0 ),
    inference(instantiation,[status(thm)],[c_1014])).

cnf(c_1006,plain,
    ( ~ v1_xboole_0(X0_41)
    | ~ v1_xboole_0(sK2)
    | sK2 = X0_41 ),
    inference(instantiation,[status(thm)],[c_336])).

cnf(c_1008,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ v1_xboole_0(sK2)
    | sK2 = sK0 ),
    inference(instantiation,[status(thm)],[c_1006])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_338,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(k2_zfmisc_1(X1_41,X2_41)))
    | ~ v1_xboole_0(X2_41)
    | v1_xboole_0(X0_41) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_940,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_41,X1_41)))
    | ~ v1_xboole_0(X1_41)
    | v1_xboole_0(sK1) ),
    inference(instantiation,[status(thm)],[c_338])).

cnf(c_942,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_xboole_0(sK0)
    | v1_xboole_0(sK1) ),
    inference(instantiation,[status(thm)],[c_940])).

cnf(c_930,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_41,X1_41)))
    | ~ v1_xboole_0(X1_41)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_338])).

cnf(c_932,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_xboole_0(sK0)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_930])).

cnf(c_920,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_41,X1_41)))
    | ~ v1_xboole_0(X1_41)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_338])).

cnf(c_922,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_xboole_0(sK0)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_920])).

cnf(c_838,plain,
    ( ~ v1_xboole_0(X0_41)
    | ~ v1_xboole_0(sK3)
    | X0_41 = sK3 ),
    inference(instantiation,[status(thm)],[c_336])).

cnf(c_840,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ v1_xboole_0(sK3)
    | sK0 = sK3 ),
    inference(instantiation,[status(thm)],[c_838])).

cnf(c_819,plain,
    ( r1_partfun1(X0_41,X1_41)
    | ~ r1_partfun1(sK3,sK3)
    | X0_41 != sK3
    | X1_41 != sK3 ),
    inference(instantiation,[status(thm)],[c_353])).

cnf(c_821,plain,
    ( r1_partfun1(sK0,sK0)
    | ~ r1_partfun1(sK3,sK3)
    | sK0 != sK3 ),
    inference(instantiation,[status(thm)],[c_819])).

cnf(c_4,plain,
    ( r1_partfun1(X0,X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_337,plain,
    ( r1_partfun1(X0_41,X0_41)
    | ~ v1_funct_1(X0_41)
    | ~ v1_funct_1(X1_41)
    | ~ v1_relat_1(X1_41)
    | ~ v1_relat_1(X0_41) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_341,plain,
    ( r1_partfun1(X0_41,X0_41)
    | ~ v1_funct_1(X0_41)
    | ~ v1_relat_1(X0_41)
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_337])).

cnf(c_342,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_337])).

cnf(c_340,plain,
    ( ~ v1_funct_1(X0_41)
    | ~ v1_relat_1(X0_41)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_337])).

cnf(c_410,plain,
    ( ~ v1_relat_1(X0_41)
    | ~ v1_funct_1(X0_41)
    | r1_partfun1(X0_41,X0_41) ),
    inference(global_propositional_subsumption,[status(thm)],[c_341,c_342,c_340])).

cnf(c_411,plain,
    ( r1_partfun1(X0_41,X0_41)
    | ~ v1_funct_1(X0_41)
    | ~ v1_relat_1(X0_41) ),
    inference(renaming,[status(thm)],[c_410])).

cnf(c_781,plain,
    ( r1_partfun1(sK3,sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_411])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_339,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(k2_zfmisc_1(X1_41,X2_41)))
    | v1_relat_1(X0_41) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_757,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_339])).

cnf(c_7,negated_conjecture,
    ( ~ r1_partfun1(sK1,sK2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_8,negated_conjecture,
    ( r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_9,negated_conjecture,
    ( r1_partfun1(sK1,sK3) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_14,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_16,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f31])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1418,c_1181,c_1016,c_1008,c_942,c_932,c_922,c_840,c_821,c_781,c_757,c_7,c_8,c_9,c_10,c_12,c_13,c_14,c_15,c_16])).


%------------------------------------------------------------------------------
