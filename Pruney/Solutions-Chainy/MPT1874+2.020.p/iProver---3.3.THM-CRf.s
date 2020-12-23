%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:26:31 EST 2020

% Result     : Theorem 3.80s
% Output     : CNFRefutation 3.80s
% Verified   : 
% Statistics : Number of formulae       :  174 (1085 expanded)
%              Number of clauses        :   89 ( 277 expanded)
%              Number of leaves         :   24 ( 308 expanded)
%              Depth                    :   22
%              Number of atoms          :  573 (5033 expanded)
%              Number of equality atoms :  188 (1083 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,X1)
                 => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) = k6_domain_1(u1_struct_0(X0),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tex_2(X1,X0)
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( r2_hidden(X2,X1)
                   => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) = k6_domain_1(u1_struct_0(X0),X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) != k6_domain_1(u1_struct_0(X0),X2)
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) != k6_domain_1(u1_struct_0(X0),X2)
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) != k6_domain_1(u1_struct_0(X0),X2)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK5))) != k6_domain_1(u1_struct_0(X0),sK5)
        & r2_hidden(sK5,X1)
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) != k6_domain_1(u1_struct_0(X0),X2)
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( k9_subset_1(u1_struct_0(X0),sK4,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) != k6_domain_1(u1_struct_0(X0),X2)
            & r2_hidden(X2,sK4)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & v2_tex_2(sK4,X0)
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) != k6_domain_1(u1_struct_0(X0),X2)
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k9_subset_1(u1_struct_0(sK3),X1,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X2))) != k6_domain_1(u1_struct_0(sK3),X2)
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(sK3)) )
          & v2_tex_2(X1,sK3)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) != k6_domain_1(u1_struct_0(sK3),sK5)
    & r2_hidden(sK5,sK4)
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & v2_tex_2(sK4,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f38,f51,f50,f49])).

fof(f84,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f52])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f86,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f52])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f7])).

fof(f89,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f58,f59])).

fof(f90,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f57,f89])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f56,f90])).

fof(f92,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f55,f91])).

fof(f93,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f54,f92])).

fof(f94,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f53,f93])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f74,f94])).

fof(f87,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,X3)
                            & v4_pre_topc(X3,X0) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,X3)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X2))
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X2))
                & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f43])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X2))
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X2))
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f76,f94])).

fof(f83,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f85,plain,(
    v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f26])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
     => ( ~ r2_hidden(sK0(X0,X1,X2),X2)
        & r2_hidden(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ( ~ r2_hidden(sK0(X0,X1,X2),X2)
            & r2_hidden(sK0(X0,X1,X2),X1)
            & m1_subset_1(sK0(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f40])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r2_hidden(sK0(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f88,plain,(
    k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) != k6_domain_1(u1_struct_0(sK3),sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r1_tarski(X2,X1)
                 => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f45])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1))) != sK2(X0,X1)
        & r1_tarski(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1))) != sK2(X0,X1)
                & r1_tarski(sK2(X0,X1),X1)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f46,f47])).

fof(f77,plain,(
    ! [X0,X3,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
      | ~ r1_tarski(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f82,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f81,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_3450,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_11,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_3457,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3974,plain,
    ( r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3450,c_3457])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_210,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_259,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_0,c_210])).

cnf(c_3449,plain,
    ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_259])).

cnf(c_6536,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,X0) = k9_subset_1(u1_struct_0(sK3),X0,sK4) ),
    inference(superposition,[status(thm)],[c_3974,c_3449])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_261,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_210])).

cnf(c_3447,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_261])).

cnf(c_5824,plain,
    ( k9_subset_1(u1_struct_0(sK3),X0,sK4) = k3_xboole_0(X0,sK4) ),
    inference(superposition,[status(thm)],[c_3974,c_3447])).

cnf(c_6539,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,X0) = k3_xboole_0(X0,sK4) ),
    inference(light_normalisation,[status(thm)],[c_6536,c_5824])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_3452,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_domain_1(X1,X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_3454,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_domain_1(X1,X0)
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5163,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_domain_1(u1_struct_0(sK3),sK5)
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3452,c_3454])).

cnf(c_22,negated_conjecture,
    ( r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_3453,plain,
    ( r2_hidden(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_15,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = k9_subset_1(u1_struct_0(X1),X0,sK1(X1,X0,X2)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_500,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = k9_subset_1(u1_struct_0(X1),X0,sK1(X1,X0,X2))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_26])).

cnf(c_501,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ r2_hidden(X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = k9_subset_1(u1_struct_0(sK3),X0,sK1(sK3,X0,X1)) ),
    inference(unflattening,[status(thm)],[c_500])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_515,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ r2_hidden(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = k9_subset_1(u1_struct_0(sK3),X0,sK1(sK3,X0,X1)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_501,c_12])).

cnf(c_3441,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k9_subset_1(u1_struct_0(sK3),X1,sK1(sK3,X1,X0))
    | v2_tex_2(X1,sK3) != iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_515])).

cnf(c_3971,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k9_subset_1(u1_struct_0(sK3),sK4,sK1(sK3,sK4,X0))
    | v2_tex_2(sK4,sK3) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3450,c_3441])).

cnf(c_32,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_695,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k9_subset_1(u1_struct_0(sK3),X1,sK1(sK3,X1,X0))
    | sK4 != X1
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_515])).

cnf(c_696,plain,
    ( ~ r2_hidden(X0,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k9_subset_1(u1_struct_0(sK3),sK4,sK1(sK3,sK4,X0)) ),
    inference(unflattening,[status(thm)],[c_695])).

cnf(c_697,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k9_subset_1(u1_struct_0(sK3),sK4,sK1(sK3,sK4,X0))
    | r2_hidden(X0,sK4) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_696])).

cnf(c_4295,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k9_subset_1(u1_struct_0(sK3),sK4,sK1(sK3,sK4,X0))
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3971,c_32,c_697])).

cnf(c_4299,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k9_subset_1(u1_struct_0(sK3),sK4,sK1(sK3,sK4,sK5)) ),
    inference(superposition,[status(thm)],[c_3453,c_4295])).

cnf(c_5170,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,sK1(sK3,sK4,sK5)) = k6_domain_1(u1_struct_0(sK3),sK5)
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5163,c_4299])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_3455,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4701,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3450,c_3455])).

cnf(c_4991,plain,
    ( v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3453,c_4701])).

cnf(c_6356,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,sK1(sK3,sK4,sK5)) = k6_domain_1(u1_struct_0(sK3),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5170,c_4991])).

cnf(c_12949,plain,
    ( k3_xboole_0(sK1(sK3,sK4,sK5),sK4) = k6_domain_1(u1_struct_0(sK3),sK5) ),
    inference(superposition,[status(thm)],[c_6539,c_6356])).

cnf(c_8,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK0(X2,X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_3460,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK0(X2,X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_7,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK0(X2,X0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_3461,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK0(X2,X0,X1),X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5404,plain,
    ( r1_tarski(X0,X0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3460,c_3461])).

cnf(c_5673,plain,
    ( r1_tarski(sK4,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3450,c_5404])).

cnf(c_5825,plain,
    ( k9_subset_1(sK4,X0,sK4) = k3_xboole_0(X0,sK4) ),
    inference(superposition,[status(thm)],[c_5673,c_3447])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_260,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_210])).

cnf(c_3448,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_260])).

cnf(c_5123,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k9_subset_1(X1,X2,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3448,c_3457])).

cnf(c_6463,plain,
    ( r1_tarski(k3_xboole_0(X0,sK4),sK4) = iProver_top
    | r1_tarski(sK4,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5825,c_5123])).

cnf(c_14127,plain,
    ( r1_tarski(k3_xboole_0(X0,sK4),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6463,c_5673])).

cnf(c_14134,plain,
    ( r1_tarski(k6_domain_1(u1_struct_0(sK3),sK5),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_12949,c_14127])).

cnf(c_21,negated_conjecture,
    ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) != k6_domain_1(u1_struct_0(sK3),sK5) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_12933,plain,
    ( k3_xboole_0(k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5)),sK4) != k6_domain_1(u1_struct_0(sK3),sK5) ),
    inference(demodulation,[status(thm)],[c_6539,c_21])).

cnf(c_3458,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_20,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ r1_tarski(X2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_369,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ r1_tarski(X2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_27])).

cnf(c_370,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ r1_tarski(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1 ),
    inference(unflattening,[status(thm)],[c_369])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_374,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ r1_tarski(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_370,c_28,c_26])).

cnf(c_375,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ r1_tarski(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1 ),
    inference(renaming,[status(thm)],[c_374])).

cnf(c_3446,plain,
    ( k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1
    | v2_tex_2(X0,sK3) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_375])).

cnf(c_4166,plain,
    ( k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1
    | v2_tex_2(X0,sK3) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3458,c_3446])).

cnf(c_5470,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X0)) = X0
    | v2_tex_2(sK4,sK3) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top
    | r1_tarski(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3450,c_4166])).

cnf(c_33,plain,
    ( v2_tex_2(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5495,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X0)) = X0
    | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top
    | r1_tarski(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5470,c_33])).

cnf(c_6466,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k9_subset_1(u1_struct_0(sK3),X0,X1))) = k9_subset_1(u1_struct_0(sK3),X0,X1)
    | r1_tarski(X1,u1_struct_0(sK3)) != iProver_top
    | r1_tarski(k9_subset_1(u1_struct_0(sK3),X0,X1),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5123,c_5495])).

cnf(c_6911,plain,
    ( k3_xboole_0(k2_pre_topc(sK3,k9_subset_1(u1_struct_0(sK3),X0,X1)),sK4) = k9_subset_1(u1_struct_0(sK3),X0,X1)
    | r1_tarski(X1,u1_struct_0(sK3)) != iProver_top
    | r1_tarski(k9_subset_1(u1_struct_0(sK3),X0,X1),sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6466,c_6539])).

cnf(c_6915,plain,
    ( k3_xboole_0(k2_pre_topc(sK3,k9_subset_1(u1_struct_0(sK3),sK4,sK1(sK3,sK4,sK5))),sK4) = k9_subset_1(u1_struct_0(sK3),sK4,sK1(sK3,sK4,sK5))
    | r1_tarski(sK1(sK3,sK4,sK5),u1_struct_0(sK3)) != iProver_top
    | r1_tarski(k6_domain_1(u1_struct_0(sK3),sK5),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6356,c_6911])).

cnf(c_6920,plain,
    ( k3_xboole_0(k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5)),sK4) = k6_domain_1(u1_struct_0(sK3),sK5)
    | r1_tarski(sK1(sK3,sK4,sK5),u1_struct_0(sK3)) != iProver_top
    | r1_tarski(k6_domain_1(u1_struct_0(sK3),sK5),sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6915,c_6356])).

cnf(c_3611,plain,
    ( r1_tarski(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_4143,plain,
    ( r1_tarski(sK1(sK3,sK4,sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(sK1(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_3611])).

cnf(c_4153,plain,
    ( r1_tarski(sK1(sK3,sK4,sK5),u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(sK1(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4143])).

cnf(c_16,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_477,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_26])).

cnf(c_478,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ r2_hidden(X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK1(sK3,X0,X1),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unflattening,[status(thm)],[c_477])).

cnf(c_492,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ r2_hidden(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK1(sK3,X0,X1),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_478,c_12])).

cnf(c_927,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK1(sK3,X0,X1),k1_zfmisc_1(u1_struct_0(sK3)))
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_492,c_22])).

cnf(c_928,plain,
    ( ~ v2_tex_2(sK4,sK3)
    | m1_subset_1(sK1(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unflattening,[status(thm)],[c_927])).

cnf(c_929,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | m1_subset_1(sK1(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_928])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14134,c_12933,c_6920,c_4153,c_929,c_33,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:42:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.80/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.80/1.00  
% 3.80/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.80/1.00  
% 3.80/1.00  ------  iProver source info
% 3.80/1.00  
% 3.80/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.80/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.80/1.00  git: non_committed_changes: false
% 3.80/1.00  git: last_make_outside_of_git: false
% 3.80/1.00  
% 3.80/1.00  ------ 
% 3.80/1.00  
% 3.80/1.00  ------ Input Options
% 3.80/1.00  
% 3.80/1.00  --out_options                           all
% 3.80/1.00  --tptp_safe_out                         true
% 3.80/1.00  --problem_path                          ""
% 3.80/1.00  --include_path                          ""
% 3.80/1.00  --clausifier                            res/vclausify_rel
% 3.80/1.00  --clausifier_options                    ""
% 3.80/1.00  --stdin                                 false
% 3.80/1.00  --stats_out                             all
% 3.80/1.00  
% 3.80/1.00  ------ General Options
% 3.80/1.00  
% 3.80/1.00  --fof                                   false
% 3.80/1.00  --time_out_real                         305.
% 3.80/1.00  --time_out_virtual                      -1.
% 3.80/1.00  --symbol_type_check                     false
% 3.80/1.00  --clausify_out                          false
% 3.80/1.00  --sig_cnt_out                           false
% 3.80/1.00  --trig_cnt_out                          false
% 3.80/1.00  --trig_cnt_out_tolerance                1.
% 3.80/1.00  --trig_cnt_out_sk_spl                   false
% 3.80/1.00  --abstr_cl_out                          false
% 3.80/1.00  
% 3.80/1.00  ------ Global Options
% 3.80/1.00  
% 3.80/1.00  --schedule                              default
% 3.80/1.00  --add_important_lit                     false
% 3.80/1.00  --prop_solver_per_cl                    1000
% 3.80/1.00  --min_unsat_core                        false
% 3.80/1.00  --soft_assumptions                      false
% 3.80/1.00  --soft_lemma_size                       3
% 3.80/1.00  --prop_impl_unit_size                   0
% 3.80/1.00  --prop_impl_unit                        []
% 3.80/1.00  --share_sel_clauses                     true
% 3.80/1.00  --reset_solvers                         false
% 3.80/1.00  --bc_imp_inh                            [conj_cone]
% 3.80/1.00  --conj_cone_tolerance                   3.
% 3.80/1.00  --extra_neg_conj                        none
% 3.80/1.00  --large_theory_mode                     true
% 3.80/1.00  --prolific_symb_bound                   200
% 3.80/1.00  --lt_threshold                          2000
% 3.80/1.00  --clause_weak_htbl                      true
% 3.80/1.00  --gc_record_bc_elim                     false
% 3.80/1.00  
% 3.80/1.00  ------ Preprocessing Options
% 3.80/1.00  
% 3.80/1.00  --preprocessing_flag                    true
% 3.80/1.00  --time_out_prep_mult                    0.1
% 3.80/1.00  --splitting_mode                        input
% 3.80/1.00  --splitting_grd                         true
% 3.80/1.00  --splitting_cvd                         false
% 3.80/1.00  --splitting_cvd_svl                     false
% 3.80/1.00  --splitting_nvd                         32
% 3.80/1.00  --sub_typing                            true
% 3.80/1.00  --prep_gs_sim                           true
% 3.80/1.00  --prep_unflatten                        true
% 3.80/1.00  --prep_res_sim                          true
% 3.80/1.00  --prep_upred                            true
% 3.80/1.00  --prep_sem_filter                       exhaustive
% 3.80/1.00  --prep_sem_filter_out                   false
% 3.80/1.00  --pred_elim                             true
% 3.80/1.00  --res_sim_input                         true
% 3.80/1.00  --eq_ax_congr_red                       true
% 3.80/1.00  --pure_diseq_elim                       true
% 3.80/1.00  --brand_transform                       false
% 3.80/1.00  --non_eq_to_eq                          false
% 3.80/1.00  --prep_def_merge                        true
% 3.80/1.00  --prep_def_merge_prop_impl              false
% 3.80/1.00  --prep_def_merge_mbd                    true
% 3.80/1.00  --prep_def_merge_tr_red                 false
% 3.80/1.00  --prep_def_merge_tr_cl                  false
% 3.80/1.00  --smt_preprocessing                     true
% 3.80/1.00  --smt_ac_axioms                         fast
% 3.80/1.00  --preprocessed_out                      false
% 3.80/1.00  --preprocessed_stats                    false
% 3.80/1.00  
% 3.80/1.00  ------ Abstraction refinement Options
% 3.80/1.00  
% 3.80/1.00  --abstr_ref                             []
% 3.80/1.00  --abstr_ref_prep                        false
% 3.80/1.00  --abstr_ref_until_sat                   false
% 3.80/1.00  --abstr_ref_sig_restrict                funpre
% 3.80/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.80/1.00  --abstr_ref_under                       []
% 3.80/1.00  
% 3.80/1.00  ------ SAT Options
% 3.80/1.00  
% 3.80/1.00  --sat_mode                              false
% 3.80/1.00  --sat_fm_restart_options                ""
% 3.80/1.00  --sat_gr_def                            false
% 3.80/1.00  --sat_epr_types                         true
% 3.80/1.00  --sat_non_cyclic_types                  false
% 3.80/1.00  --sat_finite_models                     false
% 3.80/1.00  --sat_fm_lemmas                         false
% 3.80/1.00  --sat_fm_prep                           false
% 3.80/1.00  --sat_fm_uc_incr                        true
% 3.80/1.00  --sat_out_model                         small
% 3.80/1.00  --sat_out_clauses                       false
% 3.80/1.00  
% 3.80/1.00  ------ QBF Options
% 3.80/1.00  
% 3.80/1.00  --qbf_mode                              false
% 3.80/1.00  --qbf_elim_univ                         false
% 3.80/1.00  --qbf_dom_inst                          none
% 3.80/1.00  --qbf_dom_pre_inst                      false
% 3.80/1.00  --qbf_sk_in                             false
% 3.80/1.00  --qbf_pred_elim                         true
% 3.80/1.00  --qbf_split                             512
% 3.80/1.00  
% 3.80/1.00  ------ BMC1 Options
% 3.80/1.00  
% 3.80/1.00  --bmc1_incremental                      false
% 3.80/1.00  --bmc1_axioms                           reachable_all
% 3.80/1.00  --bmc1_min_bound                        0
% 3.80/1.00  --bmc1_max_bound                        -1
% 3.80/1.00  --bmc1_max_bound_default                -1
% 3.80/1.00  --bmc1_symbol_reachability              true
% 3.80/1.00  --bmc1_property_lemmas                  false
% 3.80/1.00  --bmc1_k_induction                      false
% 3.80/1.00  --bmc1_non_equiv_states                 false
% 3.80/1.00  --bmc1_deadlock                         false
% 3.80/1.00  --bmc1_ucm                              false
% 3.80/1.00  --bmc1_add_unsat_core                   none
% 3.80/1.00  --bmc1_unsat_core_children              false
% 3.80/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.80/1.00  --bmc1_out_stat                         full
% 3.80/1.00  --bmc1_ground_init                      false
% 3.80/1.00  --bmc1_pre_inst_next_state              false
% 3.80/1.00  --bmc1_pre_inst_state                   false
% 3.80/1.00  --bmc1_pre_inst_reach_state             false
% 3.80/1.00  --bmc1_out_unsat_core                   false
% 3.80/1.00  --bmc1_aig_witness_out                  false
% 3.80/1.00  --bmc1_verbose                          false
% 3.80/1.00  --bmc1_dump_clauses_tptp                false
% 3.80/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.80/1.00  --bmc1_dump_file                        -
% 3.80/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.80/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.80/1.00  --bmc1_ucm_extend_mode                  1
% 3.80/1.00  --bmc1_ucm_init_mode                    2
% 3.80/1.00  --bmc1_ucm_cone_mode                    none
% 3.80/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.80/1.00  --bmc1_ucm_relax_model                  4
% 3.80/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.80/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.80/1.00  --bmc1_ucm_layered_model                none
% 3.80/1.00  --bmc1_ucm_max_lemma_size               10
% 3.80/1.00  
% 3.80/1.00  ------ AIG Options
% 3.80/1.00  
% 3.80/1.00  --aig_mode                              false
% 3.80/1.00  
% 3.80/1.00  ------ Instantiation Options
% 3.80/1.00  
% 3.80/1.00  --instantiation_flag                    true
% 3.80/1.00  --inst_sos_flag                         true
% 3.80/1.00  --inst_sos_phase                        true
% 3.80/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.80/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.80/1.00  --inst_lit_sel_side                     num_symb
% 3.80/1.00  --inst_solver_per_active                1400
% 3.80/1.00  --inst_solver_calls_frac                1.
% 3.80/1.00  --inst_passive_queue_type               priority_queues
% 3.80/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.80/1.00  --inst_passive_queues_freq              [25;2]
% 3.80/1.00  --inst_dismatching                      true
% 3.80/1.00  --inst_eager_unprocessed_to_passive     true
% 3.80/1.00  --inst_prop_sim_given                   true
% 3.80/1.00  --inst_prop_sim_new                     false
% 3.80/1.00  --inst_subs_new                         false
% 3.80/1.00  --inst_eq_res_simp                      false
% 3.80/1.00  --inst_subs_given                       false
% 3.80/1.00  --inst_orphan_elimination               true
% 3.80/1.00  --inst_learning_loop_flag               true
% 3.80/1.00  --inst_learning_start                   3000
% 3.80/1.00  --inst_learning_factor                  2
% 3.80/1.00  --inst_start_prop_sim_after_learn       3
% 3.80/1.00  --inst_sel_renew                        solver
% 3.80/1.00  --inst_lit_activity_flag                true
% 3.80/1.00  --inst_restr_to_given                   false
% 3.80/1.00  --inst_activity_threshold               500
% 3.80/1.00  --inst_out_proof                        true
% 3.80/1.00  
% 3.80/1.00  ------ Resolution Options
% 3.80/1.00  
% 3.80/1.00  --resolution_flag                       true
% 3.80/1.00  --res_lit_sel                           adaptive
% 3.80/1.00  --res_lit_sel_side                      none
% 3.80/1.00  --res_ordering                          kbo
% 3.80/1.00  --res_to_prop_solver                    active
% 3.80/1.00  --res_prop_simpl_new                    false
% 3.80/1.00  --res_prop_simpl_given                  true
% 3.80/1.00  --res_passive_queue_type                priority_queues
% 3.80/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.80/1.00  --res_passive_queues_freq               [15;5]
% 3.80/1.00  --res_forward_subs                      full
% 3.80/1.00  --res_backward_subs                     full
% 3.80/1.00  --res_forward_subs_resolution           true
% 3.80/1.00  --res_backward_subs_resolution          true
% 3.80/1.00  --res_orphan_elimination                true
% 3.80/1.00  --res_time_limit                        2.
% 3.80/1.00  --res_out_proof                         true
% 3.80/1.00  
% 3.80/1.00  ------ Superposition Options
% 3.80/1.00  
% 3.80/1.00  --superposition_flag                    true
% 3.80/1.00  --sup_passive_queue_type                priority_queues
% 3.80/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.80/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.80/1.00  --demod_completeness_check              fast
% 3.80/1.00  --demod_use_ground                      true
% 3.80/1.00  --sup_to_prop_solver                    passive
% 3.80/1.00  --sup_prop_simpl_new                    true
% 3.80/1.00  --sup_prop_simpl_given                  true
% 3.80/1.00  --sup_fun_splitting                     true
% 3.80/1.00  --sup_smt_interval                      50000
% 3.80/1.00  
% 3.80/1.00  ------ Superposition Simplification Setup
% 3.80/1.00  
% 3.80/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.80/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.80/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.80/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.80/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.80/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.80/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.80/1.00  --sup_immed_triv                        [TrivRules]
% 3.80/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.80/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.80/1.00  --sup_immed_bw_main                     []
% 3.80/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.80/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.80/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.80/1.00  --sup_input_bw                          []
% 3.80/1.00  
% 3.80/1.00  ------ Combination Options
% 3.80/1.00  
% 3.80/1.00  --comb_res_mult                         3
% 3.80/1.00  --comb_sup_mult                         2
% 3.80/1.00  --comb_inst_mult                        10
% 3.80/1.00  
% 3.80/1.00  ------ Debug Options
% 3.80/1.00  
% 3.80/1.00  --dbg_backtrace                         false
% 3.80/1.00  --dbg_dump_prop_clauses                 false
% 3.80/1.00  --dbg_dump_prop_clauses_file            -
% 3.80/1.00  --dbg_out_stat                          false
% 3.80/1.00  ------ Parsing...
% 3.80/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.80/1.00  
% 3.80/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.80/1.00  
% 3.80/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.80/1.00  
% 3.80/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.80/1.00  ------ Proving...
% 3.80/1.00  ------ Problem Properties 
% 3.80/1.00  
% 3.80/1.00  
% 3.80/1.00  clauses                                 26
% 3.80/1.00  conjectures                             5
% 3.80/1.00  EPR                                     6
% 3.80/1.00  Horn                                    19
% 3.80/1.00  unary                                   5
% 3.80/1.00  binary                                  5
% 3.80/1.00  lits                                    70
% 3.80/1.00  lits eq                                 7
% 3.80/1.00  fd_pure                                 0
% 3.80/1.00  fd_pseudo                               0
% 3.80/1.00  fd_cond                                 0
% 3.80/1.00  fd_pseudo_cond                          0
% 3.80/1.00  AC symbols                              0
% 3.80/1.00  
% 3.80/1.00  ------ Schedule dynamic 5 is on 
% 3.80/1.00  
% 3.80/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.80/1.00  
% 3.80/1.00  
% 3.80/1.00  ------ 
% 3.80/1.00  Current options:
% 3.80/1.00  ------ 
% 3.80/1.00  
% 3.80/1.00  ------ Input Options
% 3.80/1.00  
% 3.80/1.00  --out_options                           all
% 3.80/1.00  --tptp_safe_out                         true
% 3.80/1.00  --problem_path                          ""
% 3.80/1.00  --include_path                          ""
% 3.80/1.00  --clausifier                            res/vclausify_rel
% 3.80/1.00  --clausifier_options                    ""
% 3.80/1.00  --stdin                                 false
% 3.80/1.00  --stats_out                             all
% 3.80/1.00  
% 3.80/1.00  ------ General Options
% 3.80/1.00  
% 3.80/1.00  --fof                                   false
% 3.80/1.00  --time_out_real                         305.
% 3.80/1.00  --time_out_virtual                      -1.
% 3.80/1.00  --symbol_type_check                     false
% 3.80/1.00  --clausify_out                          false
% 3.80/1.00  --sig_cnt_out                           false
% 3.80/1.00  --trig_cnt_out                          false
% 3.80/1.00  --trig_cnt_out_tolerance                1.
% 3.80/1.00  --trig_cnt_out_sk_spl                   false
% 3.80/1.00  --abstr_cl_out                          false
% 3.80/1.00  
% 3.80/1.00  ------ Global Options
% 3.80/1.00  
% 3.80/1.00  --schedule                              default
% 3.80/1.00  --add_important_lit                     false
% 3.80/1.00  --prop_solver_per_cl                    1000
% 3.80/1.00  --min_unsat_core                        false
% 3.80/1.00  --soft_assumptions                      false
% 3.80/1.00  --soft_lemma_size                       3
% 3.80/1.00  --prop_impl_unit_size                   0
% 3.80/1.00  --prop_impl_unit                        []
% 3.80/1.00  --share_sel_clauses                     true
% 3.80/1.00  --reset_solvers                         false
% 3.80/1.00  --bc_imp_inh                            [conj_cone]
% 3.80/1.00  --conj_cone_tolerance                   3.
% 3.80/1.00  --extra_neg_conj                        none
% 3.80/1.00  --large_theory_mode                     true
% 3.80/1.00  --prolific_symb_bound                   200
% 3.80/1.00  --lt_threshold                          2000
% 3.80/1.00  --clause_weak_htbl                      true
% 3.80/1.00  --gc_record_bc_elim                     false
% 3.80/1.00  
% 3.80/1.00  ------ Preprocessing Options
% 3.80/1.00  
% 3.80/1.00  --preprocessing_flag                    true
% 3.80/1.00  --time_out_prep_mult                    0.1
% 3.80/1.00  --splitting_mode                        input
% 3.80/1.00  --splitting_grd                         true
% 3.80/1.00  --splitting_cvd                         false
% 3.80/1.00  --splitting_cvd_svl                     false
% 3.80/1.00  --splitting_nvd                         32
% 3.80/1.00  --sub_typing                            true
% 3.80/1.00  --prep_gs_sim                           true
% 3.80/1.00  --prep_unflatten                        true
% 3.80/1.00  --prep_res_sim                          true
% 3.80/1.00  --prep_upred                            true
% 3.80/1.00  --prep_sem_filter                       exhaustive
% 3.80/1.00  --prep_sem_filter_out                   false
% 3.80/1.00  --pred_elim                             true
% 3.80/1.00  --res_sim_input                         true
% 3.80/1.00  --eq_ax_congr_red                       true
% 3.80/1.00  --pure_diseq_elim                       true
% 3.80/1.00  --brand_transform                       false
% 3.80/1.00  --non_eq_to_eq                          false
% 3.80/1.00  --prep_def_merge                        true
% 3.80/1.00  --prep_def_merge_prop_impl              false
% 3.80/1.00  --prep_def_merge_mbd                    true
% 3.80/1.00  --prep_def_merge_tr_red                 false
% 3.80/1.00  --prep_def_merge_tr_cl                  false
% 3.80/1.00  --smt_preprocessing                     true
% 3.80/1.00  --smt_ac_axioms                         fast
% 3.80/1.00  --preprocessed_out                      false
% 3.80/1.00  --preprocessed_stats                    false
% 3.80/1.00  
% 3.80/1.00  ------ Abstraction refinement Options
% 3.80/1.00  
% 3.80/1.00  --abstr_ref                             []
% 3.80/1.00  --abstr_ref_prep                        false
% 3.80/1.00  --abstr_ref_until_sat                   false
% 3.80/1.00  --abstr_ref_sig_restrict                funpre
% 3.80/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.80/1.00  --abstr_ref_under                       []
% 3.80/1.00  
% 3.80/1.00  ------ SAT Options
% 3.80/1.00  
% 3.80/1.00  --sat_mode                              false
% 3.80/1.00  --sat_fm_restart_options                ""
% 3.80/1.00  --sat_gr_def                            false
% 3.80/1.00  --sat_epr_types                         true
% 3.80/1.00  --sat_non_cyclic_types                  false
% 3.80/1.00  --sat_finite_models                     false
% 3.80/1.00  --sat_fm_lemmas                         false
% 3.80/1.00  --sat_fm_prep                           false
% 3.80/1.00  --sat_fm_uc_incr                        true
% 3.80/1.00  --sat_out_model                         small
% 3.80/1.00  --sat_out_clauses                       false
% 3.80/1.00  
% 3.80/1.00  ------ QBF Options
% 3.80/1.00  
% 3.80/1.00  --qbf_mode                              false
% 3.80/1.00  --qbf_elim_univ                         false
% 3.80/1.00  --qbf_dom_inst                          none
% 3.80/1.00  --qbf_dom_pre_inst                      false
% 3.80/1.00  --qbf_sk_in                             false
% 3.80/1.00  --qbf_pred_elim                         true
% 3.80/1.00  --qbf_split                             512
% 3.80/1.00  
% 3.80/1.00  ------ BMC1 Options
% 3.80/1.00  
% 3.80/1.00  --bmc1_incremental                      false
% 3.80/1.00  --bmc1_axioms                           reachable_all
% 3.80/1.00  --bmc1_min_bound                        0
% 3.80/1.00  --bmc1_max_bound                        -1
% 3.80/1.00  --bmc1_max_bound_default                -1
% 3.80/1.00  --bmc1_symbol_reachability              true
% 3.80/1.00  --bmc1_property_lemmas                  false
% 3.80/1.00  --bmc1_k_induction                      false
% 3.80/1.00  --bmc1_non_equiv_states                 false
% 3.80/1.00  --bmc1_deadlock                         false
% 3.80/1.00  --bmc1_ucm                              false
% 3.80/1.00  --bmc1_add_unsat_core                   none
% 3.80/1.00  --bmc1_unsat_core_children              false
% 3.80/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.80/1.00  --bmc1_out_stat                         full
% 3.80/1.00  --bmc1_ground_init                      false
% 3.80/1.00  --bmc1_pre_inst_next_state              false
% 3.80/1.00  --bmc1_pre_inst_state                   false
% 3.80/1.00  --bmc1_pre_inst_reach_state             false
% 3.80/1.00  --bmc1_out_unsat_core                   false
% 3.80/1.00  --bmc1_aig_witness_out                  false
% 3.80/1.00  --bmc1_verbose                          false
% 3.80/1.00  --bmc1_dump_clauses_tptp                false
% 3.80/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.80/1.00  --bmc1_dump_file                        -
% 3.80/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.80/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.80/1.00  --bmc1_ucm_extend_mode                  1
% 3.80/1.00  --bmc1_ucm_init_mode                    2
% 3.80/1.00  --bmc1_ucm_cone_mode                    none
% 3.80/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.80/1.00  --bmc1_ucm_relax_model                  4
% 3.80/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.80/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.80/1.00  --bmc1_ucm_layered_model                none
% 3.80/1.00  --bmc1_ucm_max_lemma_size               10
% 3.80/1.00  
% 3.80/1.00  ------ AIG Options
% 3.80/1.00  
% 3.80/1.00  --aig_mode                              false
% 3.80/1.00  
% 3.80/1.00  ------ Instantiation Options
% 3.80/1.00  
% 3.80/1.00  --instantiation_flag                    true
% 3.80/1.00  --inst_sos_flag                         true
% 3.80/1.00  --inst_sos_phase                        true
% 3.80/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.80/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.80/1.00  --inst_lit_sel_side                     none
% 3.80/1.00  --inst_solver_per_active                1400
% 3.80/1.00  --inst_solver_calls_frac                1.
% 3.80/1.00  --inst_passive_queue_type               priority_queues
% 3.80/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.80/1.00  --inst_passive_queues_freq              [25;2]
% 3.80/1.00  --inst_dismatching                      true
% 3.80/1.00  --inst_eager_unprocessed_to_passive     true
% 3.80/1.00  --inst_prop_sim_given                   true
% 3.80/1.00  --inst_prop_sim_new                     false
% 3.80/1.00  --inst_subs_new                         false
% 3.80/1.00  --inst_eq_res_simp                      false
% 3.80/1.00  --inst_subs_given                       false
% 3.80/1.00  --inst_orphan_elimination               true
% 3.80/1.00  --inst_learning_loop_flag               true
% 3.80/1.00  --inst_learning_start                   3000
% 3.80/1.00  --inst_learning_factor                  2
% 3.80/1.00  --inst_start_prop_sim_after_learn       3
% 3.80/1.00  --inst_sel_renew                        solver
% 3.80/1.00  --inst_lit_activity_flag                true
% 3.80/1.00  --inst_restr_to_given                   false
% 3.80/1.00  --inst_activity_threshold               500
% 3.80/1.00  --inst_out_proof                        true
% 3.80/1.00  
% 3.80/1.00  ------ Resolution Options
% 3.80/1.00  
% 3.80/1.00  --resolution_flag                       false
% 3.80/1.00  --res_lit_sel                           adaptive
% 3.80/1.00  --res_lit_sel_side                      none
% 3.80/1.00  --res_ordering                          kbo
% 3.80/1.00  --res_to_prop_solver                    active
% 3.80/1.00  --res_prop_simpl_new                    false
% 3.80/1.00  --res_prop_simpl_given                  true
% 3.80/1.00  --res_passive_queue_type                priority_queues
% 3.80/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.80/1.00  --res_passive_queues_freq               [15;5]
% 3.80/1.00  --res_forward_subs                      full
% 3.80/1.00  --res_backward_subs                     full
% 3.80/1.00  --res_forward_subs_resolution           true
% 3.80/1.00  --res_backward_subs_resolution          true
% 3.80/1.00  --res_orphan_elimination                true
% 3.80/1.00  --res_time_limit                        2.
% 3.80/1.00  --res_out_proof                         true
% 3.80/1.00  
% 3.80/1.00  ------ Superposition Options
% 3.80/1.00  
% 3.80/1.00  --superposition_flag                    true
% 3.80/1.00  --sup_passive_queue_type                priority_queues
% 3.80/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.80/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.80/1.00  --demod_completeness_check              fast
% 3.80/1.00  --demod_use_ground                      true
% 3.80/1.00  --sup_to_prop_solver                    passive
% 3.80/1.00  --sup_prop_simpl_new                    true
% 3.80/1.00  --sup_prop_simpl_given                  true
% 3.80/1.00  --sup_fun_splitting                     true
% 3.80/1.00  --sup_smt_interval                      50000
% 3.80/1.00  
% 3.80/1.00  ------ Superposition Simplification Setup
% 3.80/1.00  
% 3.80/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.80/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.80/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.80/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.80/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.80/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.80/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.80/1.00  --sup_immed_triv                        [TrivRules]
% 3.80/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.80/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.80/1.00  --sup_immed_bw_main                     []
% 3.80/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.80/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.80/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.80/1.00  --sup_input_bw                          []
% 3.80/1.00  
% 3.80/1.00  ------ Combination Options
% 3.80/1.00  
% 3.80/1.00  --comb_res_mult                         3
% 3.80/1.00  --comb_sup_mult                         2
% 3.80/1.00  --comb_inst_mult                        10
% 3.80/1.00  
% 3.80/1.00  ------ Debug Options
% 3.80/1.00  
% 3.80/1.00  --dbg_backtrace                         false
% 3.80/1.00  --dbg_dump_prop_clauses                 false
% 3.80/1.00  --dbg_dump_prop_clauses_file            -
% 3.80/1.00  --dbg_out_stat                          false
% 3.80/1.00  
% 3.80/1.00  
% 3.80/1.00  
% 3.80/1.00  
% 3.80/1.00  ------ Proving...
% 3.80/1.00  
% 3.80/1.00  
% 3.80/1.00  % SZS status Theorem for theBenchmark.p
% 3.80/1.00  
% 3.80/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.80/1.00  
% 3.80/1.00  fof(f19,conjecture,(
% 3.80/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) = k6_domain_1(u1_struct_0(X0),X2))))))),
% 3.80/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/1.00  
% 3.80/1.00  fof(f20,negated_conjecture,(
% 3.80/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) = k6_domain_1(u1_struct_0(X0),X2))))))),
% 3.80/1.00    inference(negated_conjecture,[],[f19])).
% 3.80/1.00  
% 3.80/1.00  fof(f37,plain,(
% 3.80/1.00    ? [X0] : (? [X1] : ((? [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) != k6_domain_1(u1_struct_0(X0),X2) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.80/1.00    inference(ennf_transformation,[],[f20])).
% 3.80/1.00  
% 3.80/1.00  fof(f38,plain,(
% 3.80/1.00    ? [X0] : (? [X1] : (? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) != k6_domain_1(u1_struct_0(X0),X2) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.80/1.00    inference(flattening,[],[f37])).
% 3.80/1.00  
% 3.80/1.00  fof(f51,plain,(
% 3.80/1.00    ( ! [X0,X1] : (? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) != k6_domain_1(u1_struct_0(X0),X2) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK5))) != k6_domain_1(u1_struct_0(X0),sK5) & r2_hidden(sK5,X1) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 3.80/1.00    introduced(choice_axiom,[])).
% 3.80/1.00  
% 3.80/1.00  fof(f50,plain,(
% 3.80/1.00    ( ! [X0] : (? [X1] : (? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) != k6_domain_1(u1_struct_0(X0),X2) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (k9_subset_1(u1_struct_0(X0),sK4,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) != k6_domain_1(u1_struct_0(X0),X2) & r2_hidden(X2,sK4) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(sK4,X0) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.80/1.00    introduced(choice_axiom,[])).
% 3.80/1.00  
% 3.80/1.00  fof(f49,plain,(
% 3.80/1.00    ? [X0] : (? [X1] : (? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) != k6_domain_1(u1_struct_0(X0),X2) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k9_subset_1(u1_struct_0(sK3),X1,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X2))) != k6_domain_1(u1_struct_0(sK3),X2) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK3))) & v2_tex_2(X1,sK3) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 3.80/1.00    introduced(choice_axiom,[])).
% 3.80/1.00  
% 3.80/1.00  fof(f52,plain,(
% 3.80/1.00    ((k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) != k6_domain_1(u1_struct_0(sK3),sK5) & r2_hidden(sK5,sK4) & m1_subset_1(sK5,u1_struct_0(sK3))) & v2_tex_2(sK4,sK3) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 3.80/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f38,f51,f50,f49])).
% 3.80/1.00  
% 3.80/1.00  fof(f84,plain,(
% 3.80/1.00    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 3.80/1.00    inference(cnf_transformation,[],[f52])).
% 3.80/1.00  
% 3.80/1.00  fof(f13,axiom,(
% 3.80/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.80/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/1.00  
% 3.80/1.00  fof(f42,plain,(
% 3.80/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.80/1.00    inference(nnf_transformation,[],[f13])).
% 3.80/1.00  
% 3.80/1.00  fof(f70,plain,(
% 3.80/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.80/1.00    inference(cnf_transformation,[],[f42])).
% 3.80/1.00  
% 3.80/1.00  fof(f8,axiom,(
% 3.80/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 3.80/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/1.00  
% 3.80/1.00  fof(f22,plain,(
% 3.80/1.00    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.80/1.00    inference(ennf_transformation,[],[f8])).
% 3.80/1.00  
% 3.80/1.00  fof(f60,plain,(
% 3.80/1.00    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.80/1.00    inference(cnf_transformation,[],[f22])).
% 3.80/1.00  
% 3.80/1.00  fof(f71,plain,(
% 3.80/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.80/1.00    inference(cnf_transformation,[],[f42])).
% 3.80/1.00  
% 3.80/1.00  fof(f11,axiom,(
% 3.80/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 3.80/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/1.00  
% 3.80/1.00  fof(f25,plain,(
% 3.80/1.00    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.80/1.00    inference(ennf_transformation,[],[f11])).
% 3.80/1.00  
% 3.80/1.00  fof(f66,plain,(
% 3.80/1.00    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.80/1.00    inference(cnf_transformation,[],[f25])).
% 3.80/1.00  
% 3.80/1.00  fof(f86,plain,(
% 3.80/1.00    m1_subset_1(sK5,u1_struct_0(sK3))),
% 3.80/1.00    inference(cnf_transformation,[],[f52])).
% 3.80/1.00  
% 3.80/1.00  fof(f16,axiom,(
% 3.80/1.00    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 3.80/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/1.00  
% 3.80/1.00  fof(f31,plain,(
% 3.80/1.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 3.80/1.00    inference(ennf_transformation,[],[f16])).
% 3.80/1.00  
% 3.80/1.00  fof(f32,plain,(
% 3.80/1.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 3.80/1.00    inference(flattening,[],[f31])).
% 3.80/1.00  
% 3.80/1.00  fof(f74,plain,(
% 3.80/1.00    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.80/1.00    inference(cnf_transformation,[],[f32])).
% 3.80/1.00  
% 3.80/1.00  fof(f1,axiom,(
% 3.80/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.80/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/1.00  
% 3.80/1.00  fof(f53,plain,(
% 3.80/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.80/1.00    inference(cnf_transformation,[],[f1])).
% 3.80/1.00  
% 3.80/1.00  fof(f2,axiom,(
% 3.80/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.80/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/1.00  
% 3.80/1.00  fof(f54,plain,(
% 3.80/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.80/1.00    inference(cnf_transformation,[],[f2])).
% 3.80/1.00  
% 3.80/1.00  fof(f3,axiom,(
% 3.80/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.80/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/1.00  
% 3.80/1.00  fof(f55,plain,(
% 3.80/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.80/1.00    inference(cnf_transformation,[],[f3])).
% 3.80/1.00  
% 3.80/1.00  fof(f4,axiom,(
% 3.80/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.80/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/1.00  
% 3.80/1.00  fof(f56,plain,(
% 3.80/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.80/1.00    inference(cnf_transformation,[],[f4])).
% 3.80/1.00  
% 3.80/1.00  fof(f5,axiom,(
% 3.80/1.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.80/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/1.00  
% 3.80/1.00  fof(f57,plain,(
% 3.80/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.80/1.00    inference(cnf_transformation,[],[f5])).
% 3.80/1.00  
% 3.80/1.00  fof(f6,axiom,(
% 3.80/1.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.80/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/1.00  
% 3.80/1.00  fof(f58,plain,(
% 3.80/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.80/1.00    inference(cnf_transformation,[],[f6])).
% 3.80/1.00  
% 3.80/1.00  fof(f7,axiom,(
% 3.80/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.80/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/1.00  
% 3.80/1.00  fof(f59,plain,(
% 3.80/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.80/1.00    inference(cnf_transformation,[],[f7])).
% 3.80/1.00  
% 3.80/1.00  fof(f89,plain,(
% 3.80/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.80/1.00    inference(definition_unfolding,[],[f58,f59])).
% 3.80/1.00  
% 3.80/1.00  fof(f90,plain,(
% 3.80/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.80/1.00    inference(definition_unfolding,[],[f57,f89])).
% 3.80/1.00  
% 3.80/1.00  fof(f91,plain,(
% 3.80/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.80/1.00    inference(definition_unfolding,[],[f56,f90])).
% 3.80/1.00  
% 3.80/1.00  fof(f92,plain,(
% 3.80/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.80/1.00    inference(definition_unfolding,[],[f55,f91])).
% 3.80/1.00  
% 3.80/1.00  fof(f93,plain,(
% 3.80/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.80/1.00    inference(definition_unfolding,[],[f54,f92])).
% 3.80/1.00  
% 3.80/1.00  fof(f94,plain,(
% 3.80/1.00    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.80/1.00    inference(definition_unfolding,[],[f53,f93])).
% 3.80/1.00  
% 3.80/1.00  fof(f95,plain,(
% 3.80/1.00    ( ! [X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.80/1.00    inference(definition_unfolding,[],[f74,f94])).
% 3.80/1.00  
% 3.80/1.00  fof(f87,plain,(
% 3.80/1.00    r2_hidden(sK5,sK4)),
% 3.80/1.00    inference(cnf_transformation,[],[f52])).
% 3.80/1.00  
% 3.80/1.00  fof(f17,axiom,(
% 3.80/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,X3) & v4_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 3.80/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/1.00  
% 3.80/1.00  fof(f21,plain,(
% 3.80/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,X3)) & r2_hidden(X2,X1))))))),
% 3.80/1.00    inference(pure_predicate_removal,[],[f17])).
% 3.80/1.00  
% 3.80/1.00  fof(f33,plain,(
% 3.80/1.00    ! [X0] : (! [X1] : ((! [X2] : ((? [X3] : (k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v2_tex_2(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.80/1.00    inference(ennf_transformation,[],[f21])).
% 3.80/1.00  
% 3.80/1.00  fof(f34,plain,(
% 3.80/1.00    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.80/1.00    inference(flattening,[],[f33])).
% 3.80/1.00  
% 3.80/1.00  fof(f43,plain,(
% 3.80/1.00    ! [X2,X1,X0] : (? [X3] : (k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.80/1.00    introduced(choice_axiom,[])).
% 3.80/1.00  
% 3.80/1.00  fof(f44,plain,(
% 3.80/1.00    ! [X0] : (! [X1] : (! [X2] : ((k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.80/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f43])).
% 3.80/1.00  
% 3.80/1.00  fof(f76,plain,(
% 3.80/1.00    ( ! [X2,X0,X1] : (k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X2)) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.80/1.00    inference(cnf_transformation,[],[f44])).
% 3.80/1.00  
% 3.80/1.00  fof(f96,plain,(
% 3.80/1.00    ( ! [X2,X0,X1] : (k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X2)) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.80/1.00    inference(definition_unfolding,[],[f76,f94])).
% 3.80/1.00  
% 3.80/1.00  fof(f83,plain,(
% 3.80/1.00    l1_pre_topc(sK3)),
% 3.80/1.00    inference(cnf_transformation,[],[f52])).
% 3.80/1.00  
% 3.80/1.00  fof(f14,axiom,(
% 3.80/1.00    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.80/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/1.00  
% 3.80/1.00  fof(f28,plain,(
% 3.80/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.80/1.00    inference(ennf_transformation,[],[f14])).
% 3.80/1.00  
% 3.80/1.00  fof(f29,plain,(
% 3.80/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.80/1.00    inference(flattening,[],[f28])).
% 3.80/1.00  
% 3.80/1.00  fof(f72,plain,(
% 3.80/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.80/1.00    inference(cnf_transformation,[],[f29])).
% 3.80/1.00  
% 3.80/1.00  fof(f85,plain,(
% 3.80/1.00    v2_tex_2(sK4,sK3)),
% 3.80/1.00    inference(cnf_transformation,[],[f52])).
% 3.80/1.00  
% 3.80/1.00  fof(f15,axiom,(
% 3.80/1.00    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.80/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/1.00  
% 3.80/1.00  fof(f30,plain,(
% 3.80/1.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.80/1.00    inference(ennf_transformation,[],[f15])).
% 3.80/1.00  
% 3.80/1.00  fof(f73,plain,(
% 3.80/1.00    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.80/1.00    inference(cnf_transformation,[],[f30])).
% 3.80/1.00  
% 3.80/1.00  fof(f12,axiom,(
% 3.80/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 3.80/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/1.00  
% 3.80/1.00  fof(f26,plain,(
% 3.80/1.00    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.80/1.00    inference(ennf_transformation,[],[f12])).
% 3.80/1.00  
% 3.80/1.00  fof(f27,plain,(
% 3.80/1.00    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.80/1.00    inference(flattening,[],[f26])).
% 3.80/1.00  
% 3.80/1.00  fof(f40,plain,(
% 3.80/1.00    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) => (~r2_hidden(sK0(X0,X1,X2),X2) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),X0)))),
% 3.80/1.00    introduced(choice_axiom,[])).
% 3.80/1.00  
% 3.80/1.00  fof(f41,plain,(
% 3.80/1.00    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | (~r2_hidden(sK0(X0,X1,X2),X2) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.80/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f40])).
% 3.80/1.00  
% 3.80/1.00  fof(f68,plain,(
% 3.80/1.00    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | r2_hidden(sK0(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.80/1.00    inference(cnf_transformation,[],[f41])).
% 3.80/1.00  
% 3.80/1.00  fof(f69,plain,(
% 3.80/1.00    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r2_hidden(sK0(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.80/1.00    inference(cnf_transformation,[],[f41])).
% 3.80/1.00  
% 3.80/1.00  fof(f10,axiom,(
% 3.80/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.80/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/1.00  
% 3.80/1.00  fof(f24,plain,(
% 3.80/1.00    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.80/1.00    inference(ennf_transformation,[],[f10])).
% 3.80/1.00  
% 3.80/1.00  fof(f65,plain,(
% 3.80/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.80/1.00    inference(cnf_transformation,[],[f24])).
% 3.80/1.00  
% 3.80/1.00  fof(f88,plain,(
% 3.80/1.00    k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) != k6_domain_1(u1_struct_0(sK3),sK5)),
% 3.80/1.00    inference(cnf_transformation,[],[f52])).
% 3.80/1.00  
% 3.80/1.00  fof(f18,axiom,(
% 3.80/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2)))))),
% 3.80/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/1.00  
% 3.80/1.00  fof(f35,plain,(
% 3.80/1.00    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.80/1.00    inference(ennf_transformation,[],[f18])).
% 3.80/1.00  
% 3.80/1.00  fof(f36,plain,(
% 3.80/1.00    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.80/1.00    inference(flattening,[],[f35])).
% 3.80/1.00  
% 3.80/1.00  fof(f45,plain,(
% 3.80/1.00    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.80/1.00    inference(nnf_transformation,[],[f36])).
% 3.80/1.00  
% 3.80/1.00  fof(f46,plain,(
% 3.80/1.00    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.80/1.00    inference(rectify,[],[f45])).
% 3.80/1.00  
% 3.80/1.00  fof(f47,plain,(
% 3.80/1.00    ! [X1,X0] : (? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1))) != sK2(X0,X1) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.80/1.00    introduced(choice_axiom,[])).
% 3.80/1.00  
% 3.80/1.00  fof(f48,plain,(
% 3.80/1.00    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1))) != sK2(X0,X1) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.80/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f46,f47])).
% 3.80/1.00  
% 3.80/1.00  fof(f77,plain,(
% 3.80/1.00    ( ! [X0,X3,X1] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.80/1.00    inference(cnf_transformation,[],[f48])).
% 3.80/1.00  
% 3.80/1.00  fof(f82,plain,(
% 3.80/1.00    v2_pre_topc(sK3)),
% 3.80/1.00    inference(cnf_transformation,[],[f52])).
% 3.80/1.00  
% 3.80/1.00  fof(f81,plain,(
% 3.80/1.00    ~v2_struct_0(sK3)),
% 3.80/1.00    inference(cnf_transformation,[],[f52])).
% 3.80/1.00  
% 3.80/1.00  fof(f75,plain,(
% 3.80/1.00    ( ! [X2,X0,X1] : (m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.80/1.00    inference(cnf_transformation,[],[f44])).
% 3.80/1.00  
% 3.80/1.00  cnf(c_25,negated_conjecture,
% 3.80/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.80/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_3450,plain,
% 3.80/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.80/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_11,plain,
% 3.80/1.00      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.80/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_3457,plain,
% 3.80/1.00      ( r1_tarski(X0,X1) = iProver_top
% 3.80/1.00      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 3.80/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_3974,plain,
% 3.80/1.00      ( r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
% 3.80/1.00      inference(superposition,[status(thm)],[c_3450,c_3457]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_0,plain,
% 3.80/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.80/1.00      | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
% 3.80/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_10,plain,
% 3.80/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.80/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_210,plain,
% 3.80/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.80/1.00      inference(prop_impl,[status(thm)],[c_10]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_259,plain,
% 3.80/1.00      ( ~ r1_tarski(X0,X1)
% 3.80/1.00      | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
% 3.80/1.00      inference(bin_hyper_res,[status(thm)],[c_0,c_210]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_3449,plain,
% 3.80/1.00      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
% 3.80/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.80/1.00      inference(predicate_to_equality,[status(thm)],[c_259]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_6536,plain,
% 3.80/1.00      ( k9_subset_1(u1_struct_0(sK3),sK4,X0) = k9_subset_1(u1_struct_0(sK3),X0,sK4) ),
% 3.80/1.00      inference(superposition,[status(thm)],[c_3974,c_3449]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_6,plain,
% 3.80/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.80/1.00      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 3.80/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_261,plain,
% 3.80/1.00      ( ~ r1_tarski(X0,X1) | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 3.80/1.00      inference(bin_hyper_res,[status(thm)],[c_6,c_210]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_3447,plain,
% 3.80/1.00      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
% 3.80/1.00      | r1_tarski(X2,X0) != iProver_top ),
% 3.80/1.00      inference(predicate_to_equality,[status(thm)],[c_261]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_5824,plain,
% 3.80/1.00      ( k9_subset_1(u1_struct_0(sK3),X0,sK4) = k3_xboole_0(X0,sK4) ),
% 3.80/1.00      inference(superposition,[status(thm)],[c_3974,c_3447]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_6539,plain,
% 3.80/1.00      ( k9_subset_1(u1_struct_0(sK3),sK4,X0) = k3_xboole_0(X0,sK4) ),
% 3.80/1.00      inference(light_normalisation,[status(thm)],[c_6536,c_5824]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_23,negated_conjecture,
% 3.80/1.00      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 3.80/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_3452,plain,
% 3.80/1.00      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 3.80/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_14,plain,
% 3.80/1.00      ( ~ m1_subset_1(X0,X1)
% 3.80/1.00      | v1_xboole_0(X1)
% 3.80/1.00      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_domain_1(X1,X0) ),
% 3.80/1.00      inference(cnf_transformation,[],[f95]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_3454,plain,
% 3.80/1.00      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_domain_1(X1,X0)
% 3.80/1.00      | m1_subset_1(X0,X1) != iProver_top
% 3.80/1.00      | v1_xboole_0(X1) = iProver_top ),
% 3.80/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_5163,plain,
% 3.80/1.00      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_domain_1(u1_struct_0(sK3),sK5)
% 3.80/1.00      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.80/1.00      inference(superposition,[status(thm)],[c_3452,c_3454]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_22,negated_conjecture,
% 3.80/1.00      ( r2_hidden(sK5,sK4) ),
% 3.80/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_3453,plain,
% 3.80/1.00      ( r2_hidden(sK5,sK4) = iProver_top ),
% 3.80/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_15,plain,
% 3.80/1.00      ( ~ v2_tex_2(X0,X1)
% 3.80/1.00      | ~ r2_hidden(X2,X0)
% 3.80/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.80/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.80/1.00      | ~ l1_pre_topc(X1)
% 3.80/1.00      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = k9_subset_1(u1_struct_0(X1),X0,sK1(X1,X0,X2)) ),
% 3.80/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_26,negated_conjecture,
% 3.80/1.00      ( l1_pre_topc(sK3) ),
% 3.80/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_500,plain,
% 3.80/1.00      ( ~ v2_tex_2(X0,X1)
% 3.80/1.00      | ~ r2_hidden(X2,X0)
% 3.80/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.80/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.80/1.00      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = k9_subset_1(u1_struct_0(X1),X0,sK1(X1,X0,X2))
% 3.80/1.00      | sK3 != X1 ),
% 3.80/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_26]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_501,plain,
% 3.80/1.00      ( ~ v2_tex_2(X0,sK3)
% 3.80/1.00      | ~ r2_hidden(X1,X0)
% 3.80/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.80/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.80/1.00      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = k9_subset_1(u1_struct_0(sK3),X0,sK1(sK3,X0,X1)) ),
% 3.80/1.00      inference(unflattening,[status(thm)],[c_500]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_12,plain,
% 3.80/1.00      ( ~ r2_hidden(X0,X1)
% 3.80/1.00      | m1_subset_1(X0,X2)
% 3.80/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 3.80/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_515,plain,
% 3.80/1.00      ( ~ v2_tex_2(X0,sK3)
% 3.80/1.00      | ~ r2_hidden(X1,X0)
% 3.80/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.80/1.00      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = k9_subset_1(u1_struct_0(sK3),X0,sK1(sK3,X0,X1)) ),
% 3.80/1.00      inference(forward_subsumption_resolution,
% 3.80/1.00                [status(thm)],
% 3.80/1.00                [c_501,c_12]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_3441,plain,
% 3.80/1.00      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k9_subset_1(u1_struct_0(sK3),X1,sK1(sK3,X1,X0))
% 3.80/1.00      | v2_tex_2(X1,sK3) != iProver_top
% 3.80/1.00      | r2_hidden(X0,X1) != iProver_top
% 3.80/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 3.80/1.00      inference(predicate_to_equality,[status(thm)],[c_515]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_3971,plain,
% 3.80/1.00      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k9_subset_1(u1_struct_0(sK3),sK4,sK1(sK3,sK4,X0))
% 3.80/1.00      | v2_tex_2(sK4,sK3) != iProver_top
% 3.80/1.00      | r2_hidden(X0,sK4) != iProver_top ),
% 3.80/1.00      inference(superposition,[status(thm)],[c_3450,c_3441]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_32,plain,
% 3.80/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.80/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_24,negated_conjecture,
% 3.80/1.00      ( v2_tex_2(sK4,sK3) ),
% 3.80/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_695,plain,
% 3.80/1.00      ( ~ r2_hidden(X0,X1)
% 3.80/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.80/1.00      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k9_subset_1(u1_struct_0(sK3),X1,sK1(sK3,X1,X0))
% 3.80/1.00      | sK4 != X1
% 3.80/1.00      | sK3 != sK3 ),
% 3.80/1.00      inference(resolution_lifted,[status(thm)],[c_24,c_515]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_696,plain,
% 3.80/1.00      ( ~ r2_hidden(X0,sK4)
% 3.80/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.80/1.00      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k9_subset_1(u1_struct_0(sK3),sK4,sK1(sK3,sK4,X0)) ),
% 3.80/1.00      inference(unflattening,[status(thm)],[c_695]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_697,plain,
% 3.80/1.00      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k9_subset_1(u1_struct_0(sK3),sK4,sK1(sK3,sK4,X0))
% 3.80/1.00      | r2_hidden(X0,sK4) != iProver_top
% 3.80/1.00      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 3.80/1.00      inference(predicate_to_equality,[status(thm)],[c_696]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_4295,plain,
% 3.80/1.00      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k9_subset_1(u1_struct_0(sK3),sK4,sK1(sK3,sK4,X0))
% 3.80/1.00      | r2_hidden(X0,sK4) != iProver_top ),
% 3.80/1.00      inference(global_propositional_subsumption,
% 3.80/1.00                [status(thm)],
% 3.80/1.00                [c_3971,c_32,c_697]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_4299,plain,
% 3.80/1.00      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k9_subset_1(u1_struct_0(sK3),sK4,sK1(sK3,sK4,sK5)) ),
% 3.80/1.00      inference(superposition,[status(thm)],[c_3453,c_4295]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_5170,plain,
% 3.80/1.00      ( k9_subset_1(u1_struct_0(sK3),sK4,sK1(sK3,sK4,sK5)) = k6_domain_1(u1_struct_0(sK3),sK5)
% 3.80/1.00      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.80/1.00      inference(demodulation,[status(thm)],[c_5163,c_4299]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_13,plain,
% 3.80/1.00      ( ~ r2_hidden(X0,X1)
% 3.80/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 3.80/1.00      | ~ v1_xboole_0(X2) ),
% 3.80/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_3455,plain,
% 3.80/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.80/1.00      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 3.80/1.00      | v1_xboole_0(X2) != iProver_top ),
% 3.80/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_4701,plain,
% 3.80/1.00      ( r2_hidden(X0,sK4) != iProver_top
% 3.80/1.00      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 3.80/1.00      inference(superposition,[status(thm)],[c_3450,c_3455]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_4991,plain,
% 3.80/1.00      ( v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 3.80/1.00      inference(superposition,[status(thm)],[c_3453,c_4701]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_6356,plain,
% 3.80/1.00      ( k9_subset_1(u1_struct_0(sK3),sK4,sK1(sK3,sK4,sK5)) = k6_domain_1(u1_struct_0(sK3),sK5) ),
% 3.80/1.00      inference(global_propositional_subsumption,
% 3.80/1.00                [status(thm)],
% 3.80/1.00                [c_5170,c_4991]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_12949,plain,
% 3.80/1.00      ( k3_xboole_0(sK1(sK3,sK4,sK5),sK4) = k6_domain_1(u1_struct_0(sK3),sK5) ),
% 3.80/1.00      inference(superposition,[status(thm)],[c_6539,c_6356]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_8,plain,
% 3.80/1.00      ( r1_tarski(X0,X1)
% 3.80/1.00      | r2_hidden(sK0(X2,X0,X1),X0)
% 3.80/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 3.80/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(X2)) ),
% 3.80/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_3460,plain,
% 3.80/1.00      ( r1_tarski(X0,X1) = iProver_top
% 3.80/1.00      | r2_hidden(sK0(X2,X0,X1),X0) = iProver_top
% 3.80/1.00      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 3.80/1.00      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 3.80/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_7,plain,
% 3.80/1.00      ( r1_tarski(X0,X1)
% 3.80/1.00      | ~ r2_hidden(sK0(X2,X0,X1),X1)
% 3.80/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 3.80/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(X2)) ),
% 3.80/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_3461,plain,
% 3.80/1.00      ( r1_tarski(X0,X1) = iProver_top
% 3.80/1.00      | r2_hidden(sK0(X2,X0,X1),X1) != iProver_top
% 3.80/1.00      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 3.80/1.00      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 3.80/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_5404,plain,
% 3.80/1.00      ( r1_tarski(X0,X0) = iProver_top
% 3.80/1.00      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 3.80/1.00      inference(superposition,[status(thm)],[c_3460,c_3461]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_5673,plain,
% 3.80/1.00      ( r1_tarski(sK4,sK4) = iProver_top ),
% 3.80/1.00      inference(superposition,[status(thm)],[c_3450,c_5404]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_5825,plain,
% 3.80/1.00      ( k9_subset_1(sK4,X0,sK4) = k3_xboole_0(X0,sK4) ),
% 3.80/1.00      inference(superposition,[status(thm)],[c_5673,c_3447]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_5,plain,
% 3.80/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.80/1.00      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 3.80/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_260,plain,
% 3.80/1.00      ( ~ r1_tarski(X0,X1)
% 3.80/1.00      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 3.80/1.00      inference(bin_hyper_res,[status(thm)],[c_5,c_210]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_3448,plain,
% 3.80/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.80/1.00      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 3.80/1.00      inference(predicate_to_equality,[status(thm)],[c_260]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_5123,plain,
% 3.80/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.80/1.00      | r1_tarski(k9_subset_1(X1,X2,X0),X1) = iProver_top ),
% 3.80/1.00      inference(superposition,[status(thm)],[c_3448,c_3457]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_6463,plain,
% 3.80/1.00      ( r1_tarski(k3_xboole_0(X0,sK4),sK4) = iProver_top
% 3.80/1.00      | r1_tarski(sK4,sK4) != iProver_top ),
% 3.80/1.00      inference(superposition,[status(thm)],[c_5825,c_5123]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_14127,plain,
% 3.80/1.00      ( r1_tarski(k3_xboole_0(X0,sK4),sK4) = iProver_top ),
% 3.80/1.00      inference(global_propositional_subsumption,
% 3.80/1.00                [status(thm)],
% 3.80/1.00                [c_6463,c_5673]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_14134,plain,
% 3.80/1.00      ( r1_tarski(k6_domain_1(u1_struct_0(sK3),sK5),sK4) = iProver_top ),
% 3.80/1.00      inference(superposition,[status(thm)],[c_12949,c_14127]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_21,negated_conjecture,
% 3.80/1.00      ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) != k6_domain_1(u1_struct_0(sK3),sK5) ),
% 3.80/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_12933,plain,
% 3.80/1.00      ( k3_xboole_0(k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5)),sK4) != k6_domain_1(u1_struct_0(sK3),sK5) ),
% 3.80/1.00      inference(demodulation,[status(thm)],[c_6539,c_21]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_3458,plain,
% 3.80/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.80/1.00      | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 3.80/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_20,plain,
% 3.80/1.00      ( ~ v2_tex_2(X0,X1)
% 3.80/1.00      | ~ r1_tarski(X2,X0)
% 3.80/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.80/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.80/1.00      | v2_struct_0(X1)
% 3.80/1.00      | ~ v2_pre_topc(X1)
% 3.80/1.00      | ~ l1_pre_topc(X1)
% 3.80/1.00      | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2 ),
% 3.80/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_27,negated_conjecture,
% 3.80/1.00      ( v2_pre_topc(sK3) ),
% 3.80/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_369,plain,
% 3.80/1.00      ( ~ v2_tex_2(X0,X1)
% 3.80/1.00      | ~ r1_tarski(X2,X0)
% 3.80/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.80/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.80/1.00      | v2_struct_0(X1)
% 3.80/1.00      | ~ l1_pre_topc(X1)
% 3.80/1.00      | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2
% 3.80/1.00      | sK3 != X1 ),
% 3.80/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_27]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_370,plain,
% 3.80/1.00      ( ~ v2_tex_2(X0,sK3)
% 3.80/1.00      | ~ r1_tarski(X1,X0)
% 3.80/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.80/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.80/1.00      | v2_struct_0(sK3)
% 3.80/1.00      | ~ l1_pre_topc(sK3)
% 3.80/1.00      | k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1 ),
% 3.80/1.00      inference(unflattening,[status(thm)],[c_369]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_28,negated_conjecture,
% 3.80/1.00      ( ~ v2_struct_0(sK3) ),
% 3.80/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_374,plain,
% 3.80/1.00      ( ~ v2_tex_2(X0,sK3)
% 3.80/1.00      | ~ r1_tarski(X1,X0)
% 3.80/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.80/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.80/1.00      | k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1 ),
% 3.80/1.00      inference(global_propositional_subsumption,
% 3.80/1.00                [status(thm)],
% 3.80/1.00                [c_370,c_28,c_26]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_375,plain,
% 3.80/1.00      ( ~ v2_tex_2(X0,sK3)
% 3.80/1.00      | ~ r1_tarski(X1,X0)
% 3.80/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.80/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.80/1.00      | k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1 ),
% 3.80/1.00      inference(renaming,[status(thm)],[c_374]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_3446,plain,
% 3.80/1.00      ( k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1
% 3.80/1.00      | v2_tex_2(X0,sK3) != iProver_top
% 3.80/1.00      | r1_tarski(X1,X0) != iProver_top
% 3.80/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.80/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 3.80/1.00      inference(predicate_to_equality,[status(thm)],[c_375]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_4166,plain,
% 3.80/1.00      ( k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1
% 3.80/1.00      | v2_tex_2(X0,sK3) != iProver_top
% 3.80/1.00      | r1_tarski(X1,X0) != iProver_top
% 3.80/1.00      | r1_tarski(X1,u1_struct_0(sK3)) != iProver_top
% 3.80/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 3.80/1.00      inference(superposition,[status(thm)],[c_3458,c_3446]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_5470,plain,
% 3.80/1.00      ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X0)) = X0
% 3.80/1.00      | v2_tex_2(sK4,sK3) != iProver_top
% 3.80/1.00      | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top
% 3.80/1.00      | r1_tarski(X0,sK4) != iProver_top ),
% 3.80/1.00      inference(superposition,[status(thm)],[c_3450,c_4166]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_33,plain,
% 3.80/1.00      ( v2_tex_2(sK4,sK3) = iProver_top ),
% 3.80/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_5495,plain,
% 3.80/1.00      ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X0)) = X0
% 3.80/1.00      | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top
% 3.80/1.00      | r1_tarski(X0,sK4) != iProver_top ),
% 3.80/1.00      inference(global_propositional_subsumption,
% 3.80/1.00                [status(thm)],
% 3.80/1.00                [c_5470,c_33]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_6466,plain,
% 3.80/1.00      ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k9_subset_1(u1_struct_0(sK3),X0,X1))) = k9_subset_1(u1_struct_0(sK3),X0,X1)
% 3.80/1.00      | r1_tarski(X1,u1_struct_0(sK3)) != iProver_top
% 3.80/1.00      | r1_tarski(k9_subset_1(u1_struct_0(sK3),X0,X1),sK4) != iProver_top ),
% 3.80/1.00      inference(superposition,[status(thm)],[c_5123,c_5495]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_6911,plain,
% 3.80/1.00      ( k3_xboole_0(k2_pre_topc(sK3,k9_subset_1(u1_struct_0(sK3),X0,X1)),sK4) = k9_subset_1(u1_struct_0(sK3),X0,X1)
% 3.80/1.00      | r1_tarski(X1,u1_struct_0(sK3)) != iProver_top
% 3.80/1.00      | r1_tarski(k9_subset_1(u1_struct_0(sK3),X0,X1),sK4) != iProver_top ),
% 3.80/1.00      inference(demodulation,[status(thm)],[c_6466,c_6539]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_6915,plain,
% 3.80/1.00      ( k3_xboole_0(k2_pre_topc(sK3,k9_subset_1(u1_struct_0(sK3),sK4,sK1(sK3,sK4,sK5))),sK4) = k9_subset_1(u1_struct_0(sK3),sK4,sK1(sK3,sK4,sK5))
% 3.80/1.00      | r1_tarski(sK1(sK3,sK4,sK5),u1_struct_0(sK3)) != iProver_top
% 3.80/1.00      | r1_tarski(k6_domain_1(u1_struct_0(sK3),sK5),sK4) != iProver_top ),
% 3.80/1.00      inference(superposition,[status(thm)],[c_6356,c_6911]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_6920,plain,
% 3.80/1.00      ( k3_xboole_0(k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5)),sK4) = k6_domain_1(u1_struct_0(sK3),sK5)
% 3.80/1.00      | r1_tarski(sK1(sK3,sK4,sK5),u1_struct_0(sK3)) != iProver_top
% 3.80/1.00      | r1_tarski(k6_domain_1(u1_struct_0(sK3),sK5),sK4) != iProver_top ),
% 3.80/1.00      inference(light_normalisation,[status(thm)],[c_6915,c_6356]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_3611,plain,
% 3.80/1.00      ( r1_tarski(X0,u1_struct_0(sK3))
% 3.80/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.80/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_4143,plain,
% 3.80/1.00      ( r1_tarski(sK1(sK3,sK4,sK5),u1_struct_0(sK3))
% 3.80/1.00      | ~ m1_subset_1(sK1(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.80/1.00      inference(instantiation,[status(thm)],[c_3611]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_4153,plain,
% 3.80/1.00      ( r1_tarski(sK1(sK3,sK4,sK5),u1_struct_0(sK3)) = iProver_top
% 3.80/1.00      | m1_subset_1(sK1(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 3.80/1.00      inference(predicate_to_equality,[status(thm)],[c_4143]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_16,plain,
% 3.80/1.00      ( ~ v2_tex_2(X0,X1)
% 3.80/1.00      | ~ r2_hidden(X2,X0)
% 3.80/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.80/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.80/1.00      | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 3.80/1.00      | ~ l1_pre_topc(X1) ),
% 3.80/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_477,plain,
% 3.80/1.00      ( ~ v2_tex_2(X0,X1)
% 3.80/1.00      | ~ r2_hidden(X2,X0)
% 3.80/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.80/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.80/1.00      | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 3.80/1.00      | sK3 != X1 ),
% 3.80/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_26]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_478,plain,
% 3.80/1.00      ( ~ v2_tex_2(X0,sK3)
% 3.80/1.00      | ~ r2_hidden(X1,X0)
% 3.80/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.80/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.80/1.00      | m1_subset_1(sK1(sK3,X0,X1),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.80/1.00      inference(unflattening,[status(thm)],[c_477]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_492,plain,
% 3.80/1.00      ( ~ v2_tex_2(X0,sK3)
% 3.80/1.00      | ~ r2_hidden(X1,X0)
% 3.80/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.80/1.00      | m1_subset_1(sK1(sK3,X0,X1),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.80/1.00      inference(forward_subsumption_resolution,
% 3.80/1.00                [status(thm)],
% 3.80/1.00                [c_478,c_12]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_927,plain,
% 3.80/1.00      ( ~ v2_tex_2(X0,sK3)
% 3.80/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.80/1.00      | m1_subset_1(sK1(sK3,X0,X1),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.80/1.00      | sK5 != X1
% 3.80/1.00      | sK4 != X0 ),
% 3.80/1.00      inference(resolution_lifted,[status(thm)],[c_492,c_22]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_928,plain,
% 3.80/1.00      ( ~ v2_tex_2(sK4,sK3)
% 3.80/1.00      | m1_subset_1(sK1(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.80/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.80/1.00      inference(unflattening,[status(thm)],[c_927]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_929,plain,
% 3.80/1.00      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.80/1.00      | m1_subset_1(sK1(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 3.80/1.00      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 3.80/1.00      inference(predicate_to_equality,[status(thm)],[c_928]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(contradiction,plain,
% 3.80/1.00      ( $false ),
% 3.80/1.00      inference(minisat,
% 3.80/1.00                [status(thm)],
% 3.80/1.00                [c_14134,c_12933,c_6920,c_4153,c_929,c_33,c_32]) ).
% 3.80/1.00  
% 3.80/1.00  
% 3.80/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.80/1.00  
% 3.80/1.00  ------                               Statistics
% 3.80/1.00  
% 3.80/1.00  ------ General
% 3.80/1.00  
% 3.80/1.00  abstr_ref_over_cycles:                  0
% 3.80/1.00  abstr_ref_under_cycles:                 0
% 3.80/1.00  gc_basic_clause_elim:                   0
% 3.80/1.00  forced_gc_time:                         0
% 3.80/1.00  parsing_time:                           0.008
% 3.80/1.00  unif_index_cands_time:                  0.
% 3.80/1.00  unif_index_add_time:                    0.
% 3.80/1.00  orderings_time:                         0.
% 3.80/1.00  out_proof_time:                         0.012
% 3.80/1.00  total_time:                             0.488
% 3.80/1.00  num_of_symbols:                         52
% 3.80/1.00  num_of_terms:                           16095
% 3.80/1.00  
% 3.80/1.00  ------ Preprocessing
% 3.80/1.00  
% 3.80/1.00  num_of_splits:                          0
% 3.80/1.00  num_of_split_atoms:                     0
% 3.80/1.00  num_of_reused_defs:                     0
% 3.80/1.00  num_eq_ax_congr_red:                    56
% 3.80/1.00  num_of_sem_filtered_clauses:            1
% 3.80/1.00  num_of_subtypes:                        0
% 3.80/1.00  monotx_restored_types:                  0
% 3.80/1.00  sat_num_of_epr_types:                   0
% 3.80/1.00  sat_num_of_non_cyclic_types:            0
% 3.80/1.00  sat_guarded_non_collapsed_types:        0
% 3.80/1.00  num_pure_diseq_elim:                    0
% 3.80/1.00  simp_replaced_by:                       0
% 3.80/1.00  res_preprocessed:                       134
% 3.80/1.00  prep_upred:                             0
% 3.80/1.00  prep_unflattend:                        104
% 3.80/1.00  smt_new_axioms:                         0
% 3.80/1.00  pred_elim_cands:                        5
% 3.80/1.00  pred_elim:                              3
% 3.80/1.00  pred_elim_cl:                           3
% 3.80/1.00  pred_elim_cycles:                       9
% 3.80/1.00  merged_defs:                            8
% 3.80/1.00  merged_defs_ncl:                        0
% 3.80/1.00  bin_hyper_res:                          11
% 3.80/1.00  prep_cycles:                            4
% 3.80/1.00  pred_elim_time:                         0.026
% 3.80/1.00  splitting_time:                         0.
% 3.80/1.00  sem_filter_time:                        0.
% 3.80/1.00  monotx_time:                            0.
% 3.80/1.00  subtype_inf_time:                       0.
% 3.80/1.00  
% 3.80/1.00  ------ Problem properties
% 3.80/1.00  
% 3.80/1.00  clauses:                                26
% 3.80/1.00  conjectures:                            5
% 3.80/1.00  epr:                                    6
% 3.80/1.00  horn:                                   19
% 3.80/1.00  ground:                                 5
% 3.80/1.00  unary:                                  5
% 3.80/1.00  binary:                                 5
% 3.80/1.00  lits:                                   70
% 3.80/1.00  lits_eq:                                7
% 3.80/1.00  fd_pure:                                0
% 3.80/1.00  fd_pseudo:                              0
% 3.80/1.00  fd_cond:                                0
% 3.80/1.00  fd_pseudo_cond:                         0
% 3.80/1.00  ac_symbols:                             0
% 3.80/1.00  
% 3.80/1.00  ------ Propositional Solver
% 3.80/1.00  
% 3.80/1.00  prop_solver_calls:                      31
% 3.80/1.00  prop_fast_solver_calls:                 1952
% 3.80/1.00  smt_solver_calls:                       0
% 3.80/1.00  smt_fast_solver_calls:                  0
% 3.80/1.00  prop_num_of_clauses:                    6741
% 3.80/1.00  prop_preprocess_simplified:             12855
% 3.80/1.00  prop_fo_subsumed:                       62
% 3.80/1.00  prop_solver_time:                       0.
% 3.80/1.00  smt_solver_time:                        0.
% 3.80/1.00  smt_fast_solver_time:                   0.
% 3.80/1.00  prop_fast_solver_time:                  0.
% 3.80/1.00  prop_unsat_core_time:                   0.
% 3.80/1.00  
% 3.80/1.00  ------ QBF
% 3.80/1.00  
% 3.80/1.00  qbf_q_res:                              0
% 3.80/1.00  qbf_num_tautologies:                    0
% 3.80/1.00  qbf_prep_cycles:                        0
% 3.80/1.00  
% 3.80/1.00  ------ BMC1
% 3.80/1.00  
% 3.80/1.00  bmc1_current_bound:                     -1
% 3.80/1.00  bmc1_last_solved_bound:                 -1
% 3.80/1.00  bmc1_unsat_core_size:                   -1
% 3.80/1.00  bmc1_unsat_core_parents_size:           -1
% 3.80/1.00  bmc1_merge_next_fun:                    0
% 3.80/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.80/1.00  
% 3.80/1.00  ------ Instantiation
% 3.80/1.00  
% 3.80/1.00  inst_num_of_clauses:                    1571
% 3.80/1.00  inst_num_in_passive:                    261
% 3.80/1.00  inst_num_in_active:                     721
% 3.80/1.00  inst_num_in_unprocessed:                589
% 3.80/1.00  inst_num_of_loops:                      830
% 3.80/1.00  inst_num_of_learning_restarts:          0
% 3.80/1.00  inst_num_moves_active_passive:          105
% 3.80/1.00  inst_lit_activity:                      0
% 3.80/1.00  inst_lit_activity_moves:                0
% 3.80/1.00  inst_num_tautologies:                   0
% 3.80/1.00  inst_num_prop_implied:                  0
% 3.80/1.00  inst_num_existing_simplified:           0
% 3.80/1.00  inst_num_eq_res_simplified:             0
% 3.80/1.00  inst_num_child_elim:                    0
% 3.80/1.00  inst_num_of_dismatching_blockings:      531
% 3.80/1.00  inst_num_of_non_proper_insts:           1426
% 3.80/1.00  inst_num_of_duplicates:                 0
% 3.80/1.00  inst_inst_num_from_inst_to_res:         0
% 3.80/1.00  inst_dismatching_checking_time:         0.
% 3.80/1.00  
% 3.80/1.00  ------ Resolution
% 3.80/1.00  
% 3.80/1.00  res_num_of_clauses:                     0
% 3.80/1.00  res_num_in_passive:                     0
% 3.80/1.00  res_num_in_active:                      0
% 3.80/1.00  res_num_of_loops:                       138
% 3.80/1.00  res_forward_subset_subsumed:            110
% 3.80/1.00  res_backward_subset_subsumed:           0
% 3.80/1.00  res_forward_subsumed:                   0
% 3.80/1.00  res_backward_subsumed:                  0
% 3.80/1.00  res_forward_subsumption_resolution:     2
% 3.80/1.00  res_backward_subsumption_resolution:    0
% 3.80/1.00  res_clause_to_clause_subsumption:       3481
% 3.80/1.00  res_orphan_elimination:                 0
% 3.80/1.00  res_tautology_del:                      116
% 3.80/1.00  res_num_eq_res_simplified:              0
% 3.80/1.00  res_num_sel_changes:                    0
% 3.80/1.00  res_moves_from_active_to_pass:          0
% 3.80/1.00  
% 3.80/1.00  ------ Superposition
% 3.80/1.00  
% 3.80/1.00  sup_time_total:                         0.
% 3.80/1.00  sup_time_generating:                    0.
% 3.80/1.00  sup_time_sim_full:                      0.
% 3.80/1.00  sup_time_sim_immed:                     0.
% 3.80/1.00  
% 3.80/1.00  sup_num_of_clauses:                     475
% 3.80/1.00  sup_num_in_active:                      150
% 3.80/1.00  sup_num_in_passive:                     325
% 3.80/1.00  sup_num_of_loops:                       165
% 3.80/1.00  sup_fw_superposition:                   389
% 3.80/1.00  sup_bw_superposition:                   301
% 3.80/1.00  sup_immediate_simplified:               142
% 3.80/1.00  sup_given_eliminated:                   0
% 3.80/1.00  comparisons_done:                       0
% 3.80/1.00  comparisons_avoided:                    0
% 3.80/1.00  
% 3.80/1.00  ------ Simplifications
% 3.80/1.00  
% 3.80/1.00  
% 3.80/1.00  sim_fw_subset_subsumed:                 85
% 3.80/1.00  sim_bw_subset_subsumed:                 10
% 3.80/1.00  sim_fw_subsumed:                        21
% 3.80/1.00  sim_bw_subsumed:                        9
% 3.80/1.00  sim_fw_subsumption_res:                 0
% 3.80/1.00  sim_bw_subsumption_res:                 0
% 3.80/1.00  sim_tautology_del:                      30
% 3.80/1.00  sim_eq_tautology_del:                   2
% 3.80/1.00  sim_eq_res_simp:                        0
% 3.80/1.00  sim_fw_demodulated:                     18
% 3.80/1.00  sim_bw_demodulated:                     6
% 3.80/1.00  sim_light_normalised:                   22
% 3.80/1.00  sim_joinable_taut:                      0
% 3.80/1.00  sim_joinable_simp:                      0
% 3.80/1.00  sim_ac_normalised:                      0
% 3.80/1.00  sim_smt_subsumption:                    0
% 3.80/1.00  
%------------------------------------------------------------------------------
