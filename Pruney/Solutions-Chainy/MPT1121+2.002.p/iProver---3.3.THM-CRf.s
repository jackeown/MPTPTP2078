%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:37 EST 2020

% Result     : Theorem 3.21s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 764 expanded)
%              Number of clauses        :  100 ( 224 expanded)
%              Number of leaves         :   18 ( 186 expanded)
%              Depth                    :   17
%              Number of atoms          :  744 (4642 expanded)
%              Number of equality atoms :  124 ( 989 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   18 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ? [X2] :
              ( k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),X2)
              & ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( r2_hidden(X3,X2)
                  <=> ( r1_tarski(X1,X3)
                      & v4_pre_topc(X3,X0) ) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),X2)
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r1_tarski(X1,X3)
                      & v4_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),X2)
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r1_tarski(X1,X3)
                      & v4_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),X2)
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r1_tarski(X1,X3)
                      | ~ v4_pre_topc(X3,X0) )
                    & ( ( r1_tarski(X1,X3)
                        & v4_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),X2)
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r1_tarski(X1,X3)
                      | ~ v4_pre_topc(X3,X0) )
                    & ( ( r1_tarski(X1,X3)
                        & v4_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),X2)
          & ! [X3] :
              ( ( ( r2_hidden(X3,X2)
                  | ~ r1_tarski(X1,X3)
                  | ~ v4_pre_topc(X3,X0) )
                & ( ( r1_tarski(X1,X3)
                    & v4_pre_topc(X3,X0) )
                  | ~ r2_hidden(X3,X2) ) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),sK3(X0,X1))
        & ! [X3] :
            ( ( ( r2_hidden(X3,sK3(X0,X1))
                | ~ r1_tarski(X1,X3)
                | ~ v4_pre_topc(X3,X0) )
              & ( ( r1_tarski(X1,X3)
                  & v4_pre_topc(X3,X0) )
                | ~ r2_hidden(X3,sK3(X0,X1)) ) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),sK3(X0,X1))
            & ! [X3] :
                ( ( ( r2_hidden(X3,sK3(X0,X1))
                    | ~ r1_tarski(X1,X3)
                    | ~ v4_pre_topc(X3,X0) )
                  & ( ( r1_tarski(X1,X3)
                      & v4_pre_topc(X3,X0) )
                    | ~ r2_hidden(X3,sK3(X0,X1)) ) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( v4_pre_topc(X3,X0)
      | ~ r2_hidden(X3,sK3(X0,X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f9,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( ( k2_pre_topc(X0,X1) = X1
                  & v2_pre_topc(X0) )
               => v4_pre_topc(X1,X0) )
              & ( v4_pre_topc(X1,X0)
               => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( ~ v4_pre_topc(X1,X0)
              & k2_pre_topc(X0,X1) = X1
              & v2_pre_topc(X0) )
            | ( k2_pre_topc(X0,X1) != X1
              & v4_pre_topc(X1,X0) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( ~ v4_pre_topc(X1,X0)
              & k2_pre_topc(X0,X1) = X1
              & v2_pre_topc(X0) )
            | ( k2_pre_topc(X0,X1) != X1
              & v4_pre_topc(X1,X0) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ( ~ v4_pre_topc(X1,X0)
              & k2_pre_topc(X0,X1) = X1
              & v2_pre_topc(X0) )
            | ( k2_pre_topc(X0,X1) != X1
              & v4_pre_topc(X1,X0) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ( ~ v4_pre_topc(sK5,X0)
            & k2_pre_topc(X0,sK5) = sK5
            & v2_pre_topc(X0) )
          | ( k2_pre_topc(X0,sK5) != sK5
            & v4_pre_topc(sK5,X0) ) )
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ( ~ v4_pre_topc(X1,X0)
                & k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
              | ( k2_pre_topc(X0,X1) != X1
                & v4_pre_topc(X1,X0) ) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ( ~ v4_pre_topc(X1,sK4)
              & k2_pre_topc(sK4,X1) = X1
              & v2_pre_topc(sK4) )
            | ( k2_pre_topc(sK4,X1) != X1
              & v4_pre_topc(X1,sK4) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) )
      & l1_pre_topc(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ( ( ~ v4_pre_topc(sK5,sK4)
        & k2_pre_topc(sK4,sK5) = sK5
        & v2_pre_topc(sK4) )
      | ( k2_pre_topc(sK4,sK5) != sK5
        & v4_pre_topc(sK5,sK4) ) )
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    & l1_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f24,f40,f39])).

fof(f66,plain,
    ( v2_pre_topc(sK4)
    | v4_pre_topc(sK5,sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f64,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v4_pre_topc(X2,X0) ) )
           => v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
          | ? [X2] :
              ( ~ v4_pre_topc(X2,X0)
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
          | ? [X2] :
              ( ~ v4_pre_topc(X2,X0)
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v4_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK1(X0,X1),X0)
        & r2_hidden(sK1(X0,X1),X1)
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
          | ( ~ v4_pre_topc(sK1(X0,X1),X0)
            & r2_hidden(sK1(X0,X1),X1)
            & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f29])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
      | ~ v4_pre_topc(sK1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f71,plain,
    ( ~ v4_pre_topc(sK5,sK4)
    | k2_pre_topc(sK4,sK5) != sK5 ),
    inference(cnf_transformation,[],[f41])).

fof(f65,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f68,plain,
    ( k2_pre_topc(sK4,sK5) = sK5
    | v4_pre_topc(sK5,sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f73,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f12])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
     => ( ~ r2_hidden(sK0(X0,X1,X2),X2)
        & r2_hidden(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ( ~ r2_hidden(sK0(X0,X1,X2),X2)
            & r2_hidden(sK0(X0,X1,X2),X1)
            & m1_subset_1(sK0(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f27])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r2_hidden(sK0(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( r2_hidden(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( ( r1_tarski(X1,X3)
                        & v4_pre_topc(X3,X0) )
                     => r2_hidden(X2,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( r2_hidden(X2,X3)
                    | ~ r1_tarski(X1,X3)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ r2_hidden(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( r2_hidden(X2,X3)
                    | ~ r1_tarski(X1,X3)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ r2_hidden(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r1_tarski(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r1_tarski(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ r2_hidden(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r1_tarski(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( r2_hidden(X2,X4)
                      | ~ r1_tarski(X1,X4)
                      | ~ v4_pre_topc(X4,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ r2_hidden(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X2,X3)
          & r1_tarski(X1,X3)
          & v4_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(X2,sK2(X0,X1,X2))
        & r1_tarski(X1,sK2(X0,X1,X2))
        & v4_pre_topc(sK2(X0,X1,X2),X0)
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ( ~ r2_hidden(X2,sK2(X0,X1,X2))
                    & r1_tarski(X1,sK2(X0,X1,X2))
                    & v4_pre_topc(sK2(X0,X1,X2),X0)
                    & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( r2_hidden(X2,X4)
                      | ~ r1_tarski(X1,X4)
                      | ~ v4_pre_topc(X4,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ r2_hidden(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X2,X4)
      | ~ r1_tarski(X1,X4)
      | ~ v4_pre_topc(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ r2_hidden(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),sK3(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
      | r2_hidden(sK1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
      | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_968,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_6047,plain,
    ( k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)) != X1
    | sK5 != X1
    | sK5 = k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)) ),
    inference(instantiation,[status(thm)],[c_968])).

cnf(c_6048,plain,
    ( k6_setfam_1(u1_struct_0(sK4),sK3(sK4,sK5)) != sK5
    | sK5 = k6_setfam_1(u1_struct_0(sK4),sK3(sK4,sK5))
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_6047])).

cnf(c_976,plain,
    ( ~ v4_pre_topc(X0,X1)
    | v4_pre_topc(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1777,plain,
    ( ~ v4_pre_topc(X0,X1)
    | v4_pre_topc(sK5,sK4)
    | sK4 != X1
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_976])).

cnf(c_2640,plain,
    ( ~ v4_pre_topc(X0,sK4)
    | v4_pre_topc(sK5,sK4)
    | sK4 != sK4
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_1777])).

cnf(c_3656,plain,
    ( ~ v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)),sK4)
    | v4_pre_topc(sK5,sK4)
    | sK4 != sK4
    | sK5 != k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)) ),
    inference(instantiation,[status(thm)],[c_2640])).

cnf(c_3668,plain,
    ( ~ v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),sK3(sK4,sK5)),sK4)
    | v4_pre_topc(sK5,sK4)
    | sK4 != sK4
    | sK5 != k6_setfam_1(u1_struct_0(sK4),sK3(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_3656])).

cnf(c_967,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2999,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_967])).

cnf(c_19,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,sK3(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_27,negated_conjecture,
    ( v4_pre_topc(sK5,sK4)
    | v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_459,plain,
    ( v4_pre_topc(X0,X1)
    | v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,sK3(X1,X2))
    | ~ l1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_27])).

cnf(c_460,plain,
    ( v4_pre_topc(X0,sK4)
    | v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X0,sK3(sK4,X1))
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_459])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_464,plain,
    ( ~ r2_hidden(X0,sK3(sK4,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v4_pre_topc(sK5,sK4)
    | v4_pre_topc(X0,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_460,c_29])).

cnf(c_465,plain,
    ( v4_pre_topc(X0,sK4)
    | v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X0,sK3(sK4,X1)) ),
    inference(renaming,[status(thm)],[c_464])).

cnf(c_2791,plain,
    ( v4_pre_topc(sK1(sK4,sK3(sK4,X0)),sK4)
    | v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK1(sK4,sK3(sK4,X0)),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK1(sK4,sK3(sK4,X0)),sK3(sK4,X0)) ),
    inference(instantiation,[status(thm)],[c_465])).

cnf(c_2793,plain,
    ( v4_pre_topc(sK1(sK4,sK3(sK4,sK5)),sK4)
    | v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(sK1(sK4,sK3(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK1(sK4,sK3(sK4,sK5)),sK3(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_2791])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK3(X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_438,plain,
    ( v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK3(X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_27])).

cnf(c_439,plain,
    ( v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK3(sK4,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_438])).

cnf(c_443,plain,
    ( m1_subset_1(sK3(sK4,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v4_pre_topc(sK5,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_439,c_29])).

cnf(c_444,plain,
    ( v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK3(sK4,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
    inference(renaming,[status(thm)],[c_443])).

cnf(c_1529,plain,
    ( v4_pre_topc(sK5,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK3(sK4,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_444])).

cnf(c_8,plain,
    ( ~ v4_pre_topc(sK1(X0,X1),X0)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_414,plain,
    ( ~ v4_pre_topc(sK1(X0,X1),X0)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
    | v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_27])).

cnf(c_415,plain,
    ( ~ v4_pre_topc(sK1(sK4,X0),sK4)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4)
    | v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_414])).

cnf(c_419,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | v4_pre_topc(sK5,sK4)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4)
    | ~ v4_pre_topc(sK1(sK4,X0),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_415,c_29])).

cnf(c_420,plain,
    ( ~ v4_pre_topc(sK1(sK4,X0),sK4)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4)
    | v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
    inference(renaming,[status(thm)],[c_419])).

cnf(c_1530,plain,
    ( v4_pre_topc(sK1(sK4,X0),sK4) != iProver_top
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4) = iProver_top
    | v4_pre_topc(sK5,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_420])).

cnf(c_22,negated_conjecture,
    ( ~ v4_pre_topc(sK5,sK4)
    | k2_pre_topc(sK4,sK5) != sK5 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_36,plain,
    ( k2_pre_topc(sK4,sK5) != sK5
    | v4_pre_topc(sK5,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_421,plain,
    ( v4_pre_topc(sK1(sK4,X0),sK4) != iProver_top
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4) = iProver_top
    | v4_pre_topc(sK5,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_420])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1533,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_616,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_29])).

cnf(c_617,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(X0,k2_pre_topc(sK4,X0)) ),
    inference(unflattening,[status(thm)],[c_616])).

cnf(c_1523,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK4,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_617])).

cnf(c_1628,plain,
    ( r1_tarski(sK5,k2_pre_topc(sK4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1533,c_1523])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1541,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1828,plain,
    ( k2_pre_topc(sK4,sK5) = sK5
    | r1_tarski(k2_pre_topc(sK4,sK5),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1628,c_1541])).

cnf(c_25,negated_conjecture,
    ( v4_pre_topc(sK5,sK4)
    | k2_pre_topc(sK4,sK5) = sK5 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_93,plain,
    ( r1_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_619,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(sK5,k2_pre_topc(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_617])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_709,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_29])).

cnf(c_710,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(k2_pre_topc(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(unflattening,[status(thm)],[c_709])).

cnf(c_712,plain,
    ( m1_subset_1(k2_pre_topc(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_710])).

cnf(c_1584,plain,
    ( ~ r1_tarski(k2_pre_topc(sK4,sK5),sK5)
    | ~ r1_tarski(sK5,k2_pre_topc(sK4,sK5))
    | k2_pre_topc(sK4,sK5) = sK5 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK0(X1,X0,X2),X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1608,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK4,sK5),k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(X0))
    | ~ r2_hidden(sK0(X0,k2_pre_topc(sK4,sK5),sK5),sK5)
    | r1_tarski(k2_pre_topc(sK4,sK5),sK5) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1682,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK0(u1_struct_0(sK4),k2_pre_topc(sK4,sK5),sK5),sK5)
    | r1_tarski(k2_pre_topc(sK4,sK5),sK5) ),
    inference(instantiation,[status(thm)],[c_1608])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r2_hidden(sK0(X1,X0,X2),X0)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1609,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK4,sK5),k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(X0))
    | r2_hidden(sK0(X0,k2_pre_topc(sK4,sK5),sK5),k2_pre_topc(sK4,sK5))
    | r1_tarski(k2_pre_topc(sK4,sK5),sK5) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1690,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(sK0(u1_struct_0(sK4),k2_pre_topc(sK4,sK5),sK5),k2_pre_topc(sK4,sK5))
    | r1_tarski(k2_pre_topc(sK4,sK5),sK5) ),
    inference(instantiation,[status(thm)],[c_1609])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1590,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X1,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1926,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK0(u1_struct_0(sK4),k2_pre_topc(sK4,sK5),sK5),k2_pre_topc(sK4,sK5))
    | r2_hidden(sK0(u1_struct_0(sK4),k2_pre_topc(sK4,sK5),sK5),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1590])).

cnf(c_15,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X3,X0)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ r2_hidden(X3,u1_struct_0(X1))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_628,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X3,X0)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ r2_hidden(X3,u1_struct_0(X1))
    | ~ r1_tarski(X2,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_29])).

cnf(c_629,plain,
    ( ~ v4_pre_topc(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(X2,X0)
    | ~ r2_hidden(X2,k2_pre_topc(sK4,X1))
    | ~ r2_hidden(X2,u1_struct_0(sK4))
    | ~ r1_tarski(X1,X0) ),
    inference(unflattening,[status(thm)],[c_628])).

cnf(c_2262,plain,
    ( ~ v4_pre_topc(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(sK0(u1_struct_0(sK4),k2_pre_topc(sK4,sK5),sK5),X0)
    | ~ r2_hidden(sK0(u1_struct_0(sK4),k2_pre_topc(sK4,sK5),sK5),k2_pre_topc(sK4,X1))
    | ~ r2_hidden(sK0(u1_struct_0(sK4),k2_pre_topc(sK4,sK5),sK5),u1_struct_0(sK4))
    | ~ r1_tarski(X1,X0) ),
    inference(instantiation,[status(thm)],[c_629])).

cnf(c_2264,plain,
    ( ~ v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK0(u1_struct_0(sK4),k2_pre_topc(sK4,sK5),sK5),k2_pre_topc(sK4,sK5))
    | ~ r2_hidden(sK0(u1_struct_0(sK4),k2_pre_topc(sK4,sK5),sK5),u1_struct_0(sK4))
    | r2_hidden(sK0(u1_struct_0(sK4),k2_pre_topc(sK4,sK5),sK5),sK5)
    | ~ r1_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_2262])).

cnf(c_2311,plain,
    ( k2_pre_topc(sK4,sK5) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1828,c_28,c_25,c_93,c_619,c_712,c_1584,c_1682,c_1690,c_1926,c_2264])).

cnf(c_2423,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4) = iProver_top
    | v4_pre_topc(sK1(sK4,X0),sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1530,c_28,c_25,c_36,c_93,c_421,c_619,c_712,c_1584,c_1682,c_1690,c_1926,c_2264])).

cnf(c_2424,plain,
    ( v4_pre_topc(sK1(sK4,X0),sK4) != iProver_top
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2423])).

cnf(c_2430,plain,
    ( v4_pre_topc(sK1(sK4,sK3(sK4,X0)),sK4) != iProver_top
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)),sK4) = iProver_top
    | v4_pre_topc(sK5,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1529,c_2424])).

cnf(c_2432,plain,
    ( ~ v4_pre_topc(sK1(sK4,sK3(sK4,X0)),sK4)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)),sK4)
    | v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2430])).

cnf(c_2434,plain,
    ( ~ v4_pre_topc(sK1(sK4,sK3(sK4,sK5)),sK4)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),sK3(sK4,sK5)),sK4)
    | v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_2432])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k6_setfam_1(u1_struct_0(X1),sK3(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_535,plain,
    ( v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k6_setfam_1(u1_struct_0(X1),sK3(X1,X0)) = k2_pre_topc(X1,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_27])).

cnf(c_536,plain,
    ( v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4)
    | k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)) = k2_pre_topc(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_535])).

cnf(c_540,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v4_pre_topc(sK5,sK4)
    | k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)) = k2_pre_topc(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_536,c_29])).

cnf(c_541,plain,
    ( v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)) = k2_pre_topc(sK4,X0) ),
    inference(renaming,[status(thm)],[c_540])).

cnf(c_1525,plain,
    ( k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)) = k2_pre_topc(sK4,X0)
    | v4_pre_topc(sK5,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_541])).

cnf(c_2020,plain,
    ( k6_setfam_1(u1_struct_0(sK4),sK3(sK4,sK5)) = k2_pre_topc(sK4,sK5)
    | v4_pre_topc(sK5,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1533,c_1525])).

cnf(c_2313,plain,
    ( k6_setfam_1(u1_struct_0(sK4),sK3(sK4,sK5)) = sK5
    | v4_pre_topc(sK5,sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2311,c_2020])).

cnf(c_9,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | r2_hidden(sK1(X0,X1),X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_390,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
    | v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | r2_hidden(sK1(X0,X1),X1)
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_27])).

cnf(c_391,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4)
    | v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | r2_hidden(sK1(sK4,X0),X0)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_390])).

cnf(c_395,plain,
    ( r2_hidden(sK1(sK4,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | v4_pre_topc(sK5,sK4)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_391,c_29])).

cnf(c_396,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4)
    | v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | r2_hidden(sK1(sK4,X0),X0) ),
    inference(renaming,[status(thm)],[c_395])).

cnf(c_1531,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4) = iProver_top
    | v4_pre_topc(sK5,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
    | r2_hidden(sK1(sK4,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_396])).

cnf(c_2079,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)),sK4) = iProver_top
    | v4_pre_topc(sK5,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(sK1(sK4,sK3(sK4,X0)),sK3(sK4,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1529,c_1531])).

cnf(c_2081,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)),sK4)
    | v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(sK1(sK4,sK3(sK4,X0)),sK3(sK4,X0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2079])).

cnf(c_2083,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),sK3(sK4,sK5)),sK4)
    | v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(sK1(sK4,sK3(sK4,sK5)),sK3(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_2081])).

cnf(c_10,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_366,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
    | v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_27])).

cnf(c_367,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4)
    | v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | m1_subset_1(sK1(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_366])).

cnf(c_371,plain,
    ( m1_subset_1(sK1(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | v4_pre_topc(sK5,sK4)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_367,c_29])).

cnf(c_372,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4)
    | v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | m1_subset_1(sK1(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(renaming,[status(thm)],[c_371])).

cnf(c_1782,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)),sK4)
    | v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(sK3(sK4,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | m1_subset_1(sK1(sK4,sK3(sK4,X0)),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_372])).

cnf(c_1784,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),sK3(sK4,sK5)),sK4)
    | v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(sK3(sK4,sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | m1_subset_1(sK1(sK4,sK3(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_1782])).

cnf(c_446,plain,
    ( v4_pre_topc(sK5,sK4)
    | m1_subset_1(sK3(sK4,sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_444])).

cnf(c_97,plain,
    ( ~ r1_tarski(sK5,sK5)
    | sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6048,c_3668,c_2999,c_2793,c_2434,c_2313,c_2311,c_2083,c_1784,c_446,c_97,c_93,c_36,c_22,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n002.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:54:51 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.21/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/0.98  
% 3.21/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.21/0.98  
% 3.21/0.98  ------  iProver source info
% 3.21/0.98  
% 3.21/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.21/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.21/0.98  git: non_committed_changes: false
% 3.21/0.98  git: last_make_outside_of_git: false
% 3.21/0.98  
% 3.21/0.98  ------ 
% 3.21/0.98  
% 3.21/0.98  ------ Input Options
% 3.21/0.98  
% 3.21/0.98  --out_options                           all
% 3.21/0.98  --tptp_safe_out                         true
% 3.21/0.98  --problem_path                          ""
% 3.21/0.98  --include_path                          ""
% 3.21/0.98  --clausifier                            res/vclausify_rel
% 3.21/0.98  --clausifier_options                    ""
% 3.21/0.98  --stdin                                 false
% 3.21/0.98  --stats_out                             all
% 3.21/0.98  
% 3.21/0.98  ------ General Options
% 3.21/0.98  
% 3.21/0.98  --fof                                   false
% 3.21/0.98  --time_out_real                         305.
% 3.21/0.98  --time_out_virtual                      -1.
% 3.21/0.98  --symbol_type_check                     false
% 3.21/0.98  --clausify_out                          false
% 3.21/0.98  --sig_cnt_out                           false
% 3.21/0.98  --trig_cnt_out                          false
% 3.21/0.98  --trig_cnt_out_tolerance                1.
% 3.21/0.98  --trig_cnt_out_sk_spl                   false
% 3.21/0.98  --abstr_cl_out                          false
% 3.21/0.98  
% 3.21/0.98  ------ Global Options
% 3.21/0.98  
% 3.21/0.98  --schedule                              default
% 3.21/0.98  --add_important_lit                     false
% 3.21/0.98  --prop_solver_per_cl                    1000
% 3.21/0.98  --min_unsat_core                        false
% 3.21/0.98  --soft_assumptions                      false
% 3.21/0.98  --soft_lemma_size                       3
% 3.21/0.98  --prop_impl_unit_size                   0
% 3.21/0.98  --prop_impl_unit                        []
% 3.21/0.98  --share_sel_clauses                     true
% 3.21/0.98  --reset_solvers                         false
% 3.21/0.98  --bc_imp_inh                            [conj_cone]
% 3.21/0.98  --conj_cone_tolerance                   3.
% 3.21/0.98  --extra_neg_conj                        none
% 3.21/0.98  --large_theory_mode                     true
% 3.21/0.98  --prolific_symb_bound                   200
% 3.21/0.98  --lt_threshold                          2000
% 3.21/0.98  --clause_weak_htbl                      true
% 3.21/0.98  --gc_record_bc_elim                     false
% 3.21/0.98  
% 3.21/0.98  ------ Preprocessing Options
% 3.21/0.98  
% 3.21/0.98  --preprocessing_flag                    true
% 3.21/0.98  --time_out_prep_mult                    0.1
% 3.21/0.98  --splitting_mode                        input
% 3.21/0.98  --splitting_grd                         true
% 3.21/0.98  --splitting_cvd                         false
% 3.21/0.98  --splitting_cvd_svl                     false
% 3.21/0.98  --splitting_nvd                         32
% 3.21/0.98  --sub_typing                            true
% 3.21/0.98  --prep_gs_sim                           true
% 3.21/0.98  --prep_unflatten                        true
% 3.21/0.98  --prep_res_sim                          true
% 3.21/0.98  --prep_upred                            true
% 3.21/0.98  --prep_sem_filter                       exhaustive
% 3.21/0.98  --prep_sem_filter_out                   false
% 3.21/0.98  --pred_elim                             true
% 3.21/0.98  --res_sim_input                         true
% 3.21/0.98  --eq_ax_congr_red                       true
% 3.21/0.98  --pure_diseq_elim                       true
% 3.21/0.98  --brand_transform                       false
% 3.21/0.98  --non_eq_to_eq                          false
% 3.21/0.98  --prep_def_merge                        true
% 3.21/0.98  --prep_def_merge_prop_impl              false
% 3.21/0.98  --prep_def_merge_mbd                    true
% 3.21/0.98  --prep_def_merge_tr_red                 false
% 3.21/0.98  --prep_def_merge_tr_cl                  false
% 3.21/0.98  --smt_preprocessing                     true
% 3.21/0.98  --smt_ac_axioms                         fast
% 3.21/0.98  --preprocessed_out                      false
% 3.21/0.98  --preprocessed_stats                    false
% 3.21/0.98  
% 3.21/0.98  ------ Abstraction refinement Options
% 3.21/0.98  
% 3.21/0.98  --abstr_ref                             []
% 3.21/0.98  --abstr_ref_prep                        false
% 3.21/0.98  --abstr_ref_until_sat                   false
% 3.21/0.98  --abstr_ref_sig_restrict                funpre
% 3.21/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.21/0.98  --abstr_ref_under                       []
% 3.21/0.98  
% 3.21/0.98  ------ SAT Options
% 3.21/0.98  
% 3.21/0.98  --sat_mode                              false
% 3.21/0.98  --sat_fm_restart_options                ""
% 3.21/0.98  --sat_gr_def                            false
% 3.21/0.98  --sat_epr_types                         true
% 3.21/0.98  --sat_non_cyclic_types                  false
% 3.21/0.98  --sat_finite_models                     false
% 3.21/0.98  --sat_fm_lemmas                         false
% 3.21/0.98  --sat_fm_prep                           false
% 3.21/0.98  --sat_fm_uc_incr                        true
% 3.21/0.98  --sat_out_model                         small
% 3.21/0.98  --sat_out_clauses                       false
% 3.21/0.98  
% 3.21/0.98  ------ QBF Options
% 3.21/0.98  
% 3.21/0.98  --qbf_mode                              false
% 3.21/0.98  --qbf_elim_univ                         false
% 3.21/0.98  --qbf_dom_inst                          none
% 3.21/0.98  --qbf_dom_pre_inst                      false
% 3.21/0.98  --qbf_sk_in                             false
% 3.21/0.98  --qbf_pred_elim                         true
% 3.21/0.98  --qbf_split                             512
% 3.21/0.98  
% 3.21/0.98  ------ BMC1 Options
% 3.21/0.98  
% 3.21/0.98  --bmc1_incremental                      false
% 3.21/0.98  --bmc1_axioms                           reachable_all
% 3.21/0.98  --bmc1_min_bound                        0
% 3.21/0.98  --bmc1_max_bound                        -1
% 3.21/0.98  --bmc1_max_bound_default                -1
% 3.21/0.98  --bmc1_symbol_reachability              true
% 3.21/0.98  --bmc1_property_lemmas                  false
% 3.21/0.98  --bmc1_k_induction                      false
% 3.21/0.98  --bmc1_non_equiv_states                 false
% 3.21/0.98  --bmc1_deadlock                         false
% 3.21/0.98  --bmc1_ucm                              false
% 3.21/0.98  --bmc1_add_unsat_core                   none
% 3.21/0.98  --bmc1_unsat_core_children              false
% 3.21/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.21/0.98  --bmc1_out_stat                         full
% 3.21/0.98  --bmc1_ground_init                      false
% 3.21/0.98  --bmc1_pre_inst_next_state              false
% 3.21/0.98  --bmc1_pre_inst_state                   false
% 3.21/0.98  --bmc1_pre_inst_reach_state             false
% 3.21/0.98  --bmc1_out_unsat_core                   false
% 3.21/0.98  --bmc1_aig_witness_out                  false
% 3.21/0.98  --bmc1_verbose                          false
% 3.21/0.98  --bmc1_dump_clauses_tptp                false
% 3.21/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.21/0.98  --bmc1_dump_file                        -
% 3.21/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.21/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.21/0.98  --bmc1_ucm_extend_mode                  1
% 3.21/0.98  --bmc1_ucm_init_mode                    2
% 3.21/0.98  --bmc1_ucm_cone_mode                    none
% 3.21/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.21/0.98  --bmc1_ucm_relax_model                  4
% 3.21/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.21/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.21/0.98  --bmc1_ucm_layered_model                none
% 3.21/0.98  --bmc1_ucm_max_lemma_size               10
% 3.21/0.98  
% 3.21/0.98  ------ AIG Options
% 3.21/0.98  
% 3.21/0.98  --aig_mode                              false
% 3.21/0.98  
% 3.21/0.98  ------ Instantiation Options
% 3.21/0.98  
% 3.21/0.98  --instantiation_flag                    true
% 3.21/0.98  --inst_sos_flag                         true
% 3.21/0.98  --inst_sos_phase                        true
% 3.21/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.21/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.21/0.98  --inst_lit_sel_side                     num_symb
% 3.21/0.98  --inst_solver_per_active                1400
% 3.21/0.98  --inst_solver_calls_frac                1.
% 3.21/0.98  --inst_passive_queue_type               priority_queues
% 3.21/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.21/0.98  --inst_passive_queues_freq              [25;2]
% 3.21/0.98  --inst_dismatching                      true
% 3.21/0.98  --inst_eager_unprocessed_to_passive     true
% 3.21/0.98  --inst_prop_sim_given                   true
% 3.21/0.98  --inst_prop_sim_new                     false
% 3.21/0.98  --inst_subs_new                         false
% 3.21/0.98  --inst_eq_res_simp                      false
% 3.21/0.98  --inst_subs_given                       false
% 3.21/0.98  --inst_orphan_elimination               true
% 3.21/0.98  --inst_learning_loop_flag               true
% 3.21/0.98  --inst_learning_start                   3000
% 3.21/0.98  --inst_learning_factor                  2
% 3.21/0.98  --inst_start_prop_sim_after_learn       3
% 3.21/0.98  --inst_sel_renew                        solver
% 3.21/0.98  --inst_lit_activity_flag                true
% 3.21/0.98  --inst_restr_to_given                   false
% 3.21/0.98  --inst_activity_threshold               500
% 3.21/0.98  --inst_out_proof                        true
% 3.21/0.98  
% 3.21/0.98  ------ Resolution Options
% 3.21/0.98  
% 3.21/0.98  --resolution_flag                       true
% 3.21/0.98  --res_lit_sel                           adaptive
% 3.21/0.98  --res_lit_sel_side                      none
% 3.21/0.98  --res_ordering                          kbo
% 3.21/0.98  --res_to_prop_solver                    active
% 3.21/0.98  --res_prop_simpl_new                    false
% 3.21/0.98  --res_prop_simpl_given                  true
% 3.21/0.98  --res_passive_queue_type                priority_queues
% 3.21/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.21/0.98  --res_passive_queues_freq               [15;5]
% 3.21/0.98  --res_forward_subs                      full
% 3.21/0.98  --res_backward_subs                     full
% 3.21/0.98  --res_forward_subs_resolution           true
% 3.21/0.98  --res_backward_subs_resolution          true
% 3.21/0.98  --res_orphan_elimination                true
% 3.21/0.98  --res_time_limit                        2.
% 3.21/0.98  --res_out_proof                         true
% 3.21/0.98  
% 3.21/0.98  ------ Superposition Options
% 3.21/0.98  
% 3.21/0.98  --superposition_flag                    true
% 3.21/0.98  --sup_passive_queue_type                priority_queues
% 3.21/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.21/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.21/0.98  --demod_completeness_check              fast
% 3.21/0.98  --demod_use_ground                      true
% 3.21/0.98  --sup_to_prop_solver                    passive
% 3.21/0.98  --sup_prop_simpl_new                    true
% 3.21/0.98  --sup_prop_simpl_given                  true
% 3.21/0.98  --sup_fun_splitting                     true
% 3.21/0.98  --sup_smt_interval                      50000
% 3.21/0.98  
% 3.21/0.98  ------ Superposition Simplification Setup
% 3.21/0.98  
% 3.21/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.21/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.21/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.21/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.21/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.21/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.21/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.21/0.98  --sup_immed_triv                        [TrivRules]
% 3.21/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.21/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.21/0.98  --sup_immed_bw_main                     []
% 3.21/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.21/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.21/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.21/0.98  --sup_input_bw                          []
% 3.21/0.98  
% 3.21/0.98  ------ Combination Options
% 3.21/0.98  
% 3.21/0.98  --comb_res_mult                         3
% 3.21/0.98  --comb_sup_mult                         2
% 3.21/0.98  --comb_inst_mult                        10
% 3.21/0.98  
% 3.21/0.98  ------ Debug Options
% 3.21/0.98  
% 3.21/0.98  --dbg_backtrace                         false
% 3.21/0.98  --dbg_dump_prop_clauses                 false
% 3.21/0.98  --dbg_dump_prop_clauses_file            -
% 3.21/0.98  --dbg_out_stat                          false
% 3.21/0.98  ------ Parsing...
% 3.21/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.21/0.98  
% 3.21/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.21/0.98  
% 3.21/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.21/0.98  
% 3.21/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.21/0.98  ------ Proving...
% 3.21/0.98  ------ Problem Properties 
% 3.21/0.98  
% 3.21/0.98  
% 3.21/0.98  clauses                                 24
% 3.21/0.98  conjectures                             3
% 3.21/0.98  EPR                                     2
% 3.21/0.98  Horn                                    10
% 3.21/0.98  unary                                   2
% 3.21/0.98  binary                                  4
% 3.21/0.98  lits                                    85
% 3.21/0.98  lits eq                                 4
% 3.21/0.98  fd_pure                                 0
% 3.21/0.98  fd_pseudo                               0
% 3.21/0.98  fd_cond                                 0
% 3.21/0.98  fd_pseudo_cond                          1
% 3.21/0.98  AC symbols                              0
% 3.21/0.98  
% 3.21/0.98  ------ Schedule dynamic 5 is on 
% 3.21/0.98  
% 3.21/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.21/0.98  
% 3.21/0.98  
% 3.21/0.98  ------ 
% 3.21/0.98  Current options:
% 3.21/0.98  ------ 
% 3.21/0.98  
% 3.21/0.98  ------ Input Options
% 3.21/0.98  
% 3.21/0.98  --out_options                           all
% 3.21/0.98  --tptp_safe_out                         true
% 3.21/0.98  --problem_path                          ""
% 3.21/0.98  --include_path                          ""
% 3.21/0.98  --clausifier                            res/vclausify_rel
% 3.21/0.98  --clausifier_options                    ""
% 3.21/0.98  --stdin                                 false
% 3.21/0.98  --stats_out                             all
% 3.21/0.98  
% 3.21/0.98  ------ General Options
% 3.21/0.98  
% 3.21/0.98  --fof                                   false
% 3.21/0.98  --time_out_real                         305.
% 3.21/0.98  --time_out_virtual                      -1.
% 3.21/0.98  --symbol_type_check                     false
% 3.21/0.98  --clausify_out                          false
% 3.21/0.98  --sig_cnt_out                           false
% 3.21/0.98  --trig_cnt_out                          false
% 3.21/0.98  --trig_cnt_out_tolerance                1.
% 3.21/0.98  --trig_cnt_out_sk_spl                   false
% 3.21/0.98  --abstr_cl_out                          false
% 3.21/0.98  
% 3.21/0.98  ------ Global Options
% 3.21/0.98  
% 3.21/0.98  --schedule                              default
% 3.21/0.98  --add_important_lit                     false
% 3.21/0.98  --prop_solver_per_cl                    1000
% 3.21/0.98  --min_unsat_core                        false
% 3.21/0.98  --soft_assumptions                      false
% 3.21/0.98  --soft_lemma_size                       3
% 3.21/0.98  --prop_impl_unit_size                   0
% 3.21/0.98  --prop_impl_unit                        []
% 3.21/0.98  --share_sel_clauses                     true
% 3.21/0.98  --reset_solvers                         false
% 3.21/0.98  --bc_imp_inh                            [conj_cone]
% 3.21/0.98  --conj_cone_tolerance                   3.
% 3.21/0.98  --extra_neg_conj                        none
% 3.21/0.98  --large_theory_mode                     true
% 3.21/0.98  --prolific_symb_bound                   200
% 3.21/0.98  --lt_threshold                          2000
% 3.21/0.98  --clause_weak_htbl                      true
% 3.21/0.98  --gc_record_bc_elim                     false
% 3.21/0.98  
% 3.21/0.98  ------ Preprocessing Options
% 3.21/0.98  
% 3.21/0.98  --preprocessing_flag                    true
% 3.21/0.98  --time_out_prep_mult                    0.1
% 3.21/0.98  --splitting_mode                        input
% 3.21/0.98  --splitting_grd                         true
% 3.21/0.98  --splitting_cvd                         false
% 3.21/0.98  --splitting_cvd_svl                     false
% 3.21/0.98  --splitting_nvd                         32
% 3.21/0.98  --sub_typing                            true
% 3.21/0.98  --prep_gs_sim                           true
% 3.21/0.98  --prep_unflatten                        true
% 3.21/0.98  --prep_res_sim                          true
% 3.21/0.98  --prep_upred                            true
% 3.21/0.98  --prep_sem_filter                       exhaustive
% 3.21/0.98  --prep_sem_filter_out                   false
% 3.21/0.98  --pred_elim                             true
% 3.21/0.98  --res_sim_input                         true
% 3.21/0.98  --eq_ax_congr_red                       true
% 3.21/0.98  --pure_diseq_elim                       true
% 3.21/0.98  --brand_transform                       false
% 3.21/0.98  --non_eq_to_eq                          false
% 3.21/0.98  --prep_def_merge                        true
% 3.21/0.98  --prep_def_merge_prop_impl              false
% 3.21/0.98  --prep_def_merge_mbd                    true
% 3.21/0.98  --prep_def_merge_tr_red                 false
% 3.21/0.98  --prep_def_merge_tr_cl                  false
% 3.21/0.98  --smt_preprocessing                     true
% 3.21/0.98  --smt_ac_axioms                         fast
% 3.21/0.98  --preprocessed_out                      false
% 3.21/0.98  --preprocessed_stats                    false
% 3.21/0.98  
% 3.21/0.98  ------ Abstraction refinement Options
% 3.21/0.98  
% 3.21/0.98  --abstr_ref                             []
% 3.21/0.98  --abstr_ref_prep                        false
% 3.21/0.98  --abstr_ref_until_sat                   false
% 3.21/0.98  --abstr_ref_sig_restrict                funpre
% 3.21/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.21/0.98  --abstr_ref_under                       []
% 3.21/0.98  
% 3.21/0.98  ------ SAT Options
% 3.21/0.98  
% 3.21/0.98  --sat_mode                              false
% 3.21/0.98  --sat_fm_restart_options                ""
% 3.21/0.98  --sat_gr_def                            false
% 3.21/0.98  --sat_epr_types                         true
% 3.21/0.98  --sat_non_cyclic_types                  false
% 3.21/0.98  --sat_finite_models                     false
% 3.21/0.98  --sat_fm_lemmas                         false
% 3.21/0.98  --sat_fm_prep                           false
% 3.21/0.98  --sat_fm_uc_incr                        true
% 3.21/0.98  --sat_out_model                         small
% 3.21/0.98  --sat_out_clauses                       false
% 3.21/0.98  
% 3.21/0.98  ------ QBF Options
% 3.21/0.98  
% 3.21/0.98  --qbf_mode                              false
% 3.21/0.98  --qbf_elim_univ                         false
% 3.21/0.98  --qbf_dom_inst                          none
% 3.21/0.98  --qbf_dom_pre_inst                      false
% 3.21/0.98  --qbf_sk_in                             false
% 3.21/0.98  --qbf_pred_elim                         true
% 3.21/0.98  --qbf_split                             512
% 3.21/0.98  
% 3.21/0.98  ------ BMC1 Options
% 3.21/0.98  
% 3.21/0.98  --bmc1_incremental                      false
% 3.21/0.98  --bmc1_axioms                           reachable_all
% 3.21/0.98  --bmc1_min_bound                        0
% 3.21/0.98  --bmc1_max_bound                        -1
% 3.21/0.98  --bmc1_max_bound_default                -1
% 3.21/0.98  --bmc1_symbol_reachability              true
% 3.21/0.98  --bmc1_property_lemmas                  false
% 3.21/0.98  --bmc1_k_induction                      false
% 3.21/0.98  --bmc1_non_equiv_states                 false
% 3.21/0.98  --bmc1_deadlock                         false
% 3.21/0.98  --bmc1_ucm                              false
% 3.21/0.98  --bmc1_add_unsat_core                   none
% 3.21/0.98  --bmc1_unsat_core_children              false
% 3.21/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.21/0.98  --bmc1_out_stat                         full
% 3.21/0.98  --bmc1_ground_init                      false
% 3.21/0.98  --bmc1_pre_inst_next_state              false
% 3.21/0.98  --bmc1_pre_inst_state                   false
% 3.21/0.98  --bmc1_pre_inst_reach_state             false
% 3.21/0.98  --bmc1_out_unsat_core                   false
% 3.21/0.98  --bmc1_aig_witness_out                  false
% 3.21/0.98  --bmc1_verbose                          false
% 3.21/0.98  --bmc1_dump_clauses_tptp                false
% 3.21/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.21/0.98  --bmc1_dump_file                        -
% 3.21/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.21/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.21/0.98  --bmc1_ucm_extend_mode                  1
% 3.21/0.98  --bmc1_ucm_init_mode                    2
% 3.21/0.98  --bmc1_ucm_cone_mode                    none
% 3.21/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.21/0.98  --bmc1_ucm_relax_model                  4
% 3.21/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.21/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.21/0.98  --bmc1_ucm_layered_model                none
% 3.21/0.98  --bmc1_ucm_max_lemma_size               10
% 3.21/0.98  
% 3.21/0.98  ------ AIG Options
% 3.21/0.98  
% 3.21/0.98  --aig_mode                              false
% 3.21/0.98  
% 3.21/0.98  ------ Instantiation Options
% 3.21/0.98  
% 3.21/0.98  --instantiation_flag                    true
% 3.21/0.98  --inst_sos_flag                         true
% 3.21/0.98  --inst_sos_phase                        true
% 3.21/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.21/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.21/0.98  --inst_lit_sel_side                     none
% 3.21/0.98  --inst_solver_per_active                1400
% 3.21/0.98  --inst_solver_calls_frac                1.
% 3.21/0.98  --inst_passive_queue_type               priority_queues
% 3.21/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.21/0.98  --inst_passive_queues_freq              [25;2]
% 3.21/0.98  --inst_dismatching                      true
% 3.21/0.98  --inst_eager_unprocessed_to_passive     true
% 3.21/0.98  --inst_prop_sim_given                   true
% 3.21/0.98  --inst_prop_sim_new                     false
% 3.21/0.98  --inst_subs_new                         false
% 3.21/0.98  --inst_eq_res_simp                      false
% 3.21/0.98  --inst_subs_given                       false
% 3.21/0.98  --inst_orphan_elimination               true
% 3.21/0.98  --inst_learning_loop_flag               true
% 3.21/0.98  --inst_learning_start                   3000
% 3.21/0.98  --inst_learning_factor                  2
% 3.21/0.98  --inst_start_prop_sim_after_learn       3
% 3.21/0.98  --inst_sel_renew                        solver
% 3.21/0.98  --inst_lit_activity_flag                true
% 3.21/0.98  --inst_restr_to_given                   false
% 3.21/0.98  --inst_activity_threshold               500
% 3.21/0.98  --inst_out_proof                        true
% 3.21/0.98  
% 3.21/0.98  ------ Resolution Options
% 3.21/0.98  
% 3.21/0.98  --resolution_flag                       false
% 3.21/0.98  --res_lit_sel                           adaptive
% 3.21/0.98  --res_lit_sel_side                      none
% 3.21/0.98  --res_ordering                          kbo
% 3.21/0.98  --res_to_prop_solver                    active
% 3.21/0.98  --res_prop_simpl_new                    false
% 3.21/0.98  --res_prop_simpl_given                  true
% 3.21/0.98  --res_passive_queue_type                priority_queues
% 3.21/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.21/0.98  --res_passive_queues_freq               [15;5]
% 3.21/0.98  --res_forward_subs                      full
% 3.21/0.98  --res_backward_subs                     full
% 3.21/0.98  --res_forward_subs_resolution           true
% 3.21/0.98  --res_backward_subs_resolution          true
% 3.21/0.98  --res_orphan_elimination                true
% 3.21/0.98  --res_time_limit                        2.
% 3.21/0.98  --res_out_proof                         true
% 3.21/0.98  
% 3.21/0.98  ------ Superposition Options
% 3.21/0.98  
% 3.21/0.98  --superposition_flag                    true
% 3.21/0.98  --sup_passive_queue_type                priority_queues
% 3.21/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.21/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.21/0.98  --demod_completeness_check              fast
% 3.21/0.98  --demod_use_ground                      true
% 3.21/0.98  --sup_to_prop_solver                    passive
% 3.21/0.98  --sup_prop_simpl_new                    true
% 3.21/0.98  --sup_prop_simpl_given                  true
% 3.21/0.98  --sup_fun_splitting                     true
% 3.21/0.98  --sup_smt_interval                      50000
% 3.21/0.98  
% 3.21/0.98  ------ Superposition Simplification Setup
% 3.21/0.98  
% 3.21/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.21/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.21/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.21/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.21/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.21/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.21/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.21/0.98  --sup_immed_triv                        [TrivRules]
% 3.21/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.21/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.21/0.98  --sup_immed_bw_main                     []
% 3.21/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.21/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.21/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.21/0.98  --sup_input_bw                          []
% 3.21/0.98  
% 3.21/0.98  ------ Combination Options
% 3.21/0.98  
% 3.21/0.98  --comb_res_mult                         3
% 3.21/0.98  --comb_sup_mult                         2
% 3.21/0.98  --comb_inst_mult                        10
% 3.21/0.98  
% 3.21/0.98  ------ Debug Options
% 3.21/0.98  
% 3.21/0.98  --dbg_backtrace                         false
% 3.21/0.98  --dbg_dump_prop_clauses                 false
% 3.21/0.98  --dbg_dump_prop_clauses_file            -
% 3.21/0.98  --dbg_out_stat                          false
% 3.21/0.98  
% 3.21/0.98  
% 3.21/0.98  
% 3.21/0.98  
% 3.21/0.98  ------ Proving...
% 3.21/0.98  
% 3.21/0.98  
% 3.21/0.98  % SZS status Theorem for theBenchmark.p
% 3.21/0.98  
% 3.21/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.21/0.98  
% 3.21/0.98  fof(f7,axiom,(
% 3.21/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ? [X2] : (k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),X2) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r1_tarski(X1,X3) & v4_pre_topc(X3,X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))))),
% 3.21/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/0.98  
% 3.21/0.98  fof(f20,plain,(
% 3.21/0.98    ! [X0] : (! [X1] : (? [X2] : (k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),X2) & ! [X3] : ((r2_hidden(X3,X2) <=> (r1_tarski(X1,X3) & v4_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.21/0.98    inference(ennf_transformation,[],[f7])).
% 3.21/0.98  
% 3.21/0.98  fof(f21,plain,(
% 3.21/0.98    ! [X0] : (! [X1] : (? [X2] : (k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),X2) & ! [X3] : ((r2_hidden(X3,X2) <=> (r1_tarski(X1,X3) & v4_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.21/0.98    inference(flattening,[],[f20])).
% 3.21/0.98  
% 3.21/0.98  fof(f35,plain,(
% 3.21/0.98    ! [X0] : (! [X1] : (? [X2] : (k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),X2) & ! [X3] : (((r2_hidden(X3,X2) | (~r1_tarski(X1,X3) | ~v4_pre_topc(X3,X0))) & ((r1_tarski(X1,X3) & v4_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.21/0.98    inference(nnf_transformation,[],[f21])).
% 3.21/0.98  
% 3.21/0.98  fof(f36,plain,(
% 3.21/0.98    ! [X0] : (! [X1] : (? [X2] : (k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),X2) & ! [X3] : (((r2_hidden(X3,X2) | ~r1_tarski(X1,X3) | ~v4_pre_topc(X3,X0)) & ((r1_tarski(X1,X3) & v4_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.21/0.98    inference(flattening,[],[f35])).
% 3.21/0.98  
% 3.21/0.98  fof(f37,plain,(
% 3.21/0.98    ! [X1,X0] : (? [X2] : (k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),X2) & ! [X3] : (((r2_hidden(X3,X2) | ~r1_tarski(X1,X3) | ~v4_pre_topc(X3,X0)) & ((r1_tarski(X1,X3) & v4_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),sK3(X0,X1)) & ! [X3] : (((r2_hidden(X3,sK3(X0,X1)) | ~r1_tarski(X1,X3) | ~v4_pre_topc(X3,X0)) & ((r1_tarski(X1,X3) & v4_pre_topc(X3,X0)) | ~r2_hidden(X3,sK3(X0,X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 3.21/0.98    introduced(choice_axiom,[])).
% 3.21/0.98  
% 3.21/0.98  fof(f38,plain,(
% 3.21/0.98    ! [X0] : (! [X1] : ((k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),sK3(X0,X1)) & ! [X3] : (((r2_hidden(X3,sK3(X0,X1)) | ~r1_tarski(X1,X3) | ~v4_pre_topc(X3,X0)) & ((r1_tarski(X1,X3) & v4_pre_topc(X3,X0)) | ~r2_hidden(X3,sK3(X0,X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.21/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).
% 3.21/0.98  
% 3.21/0.98  fof(f59,plain,(
% 3.21/0.98    ( ! [X0,X3,X1] : (v4_pre_topc(X3,X0) | ~r2_hidden(X3,sK3(X0,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.21/0.98    inference(cnf_transformation,[],[f38])).
% 3.21/0.98  
% 3.21/0.98  fof(f9,conjecture,(
% 3.21/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 3.21/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/0.98  
% 3.21/0.98  fof(f10,negated_conjecture,(
% 3.21/0.98    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 3.21/0.98    inference(negated_conjecture,[],[f9])).
% 3.21/0.98  
% 3.21/0.98  fof(f23,plain,(
% 3.21/0.98    ? [X0] : (? [X1] : (((~v4_pre_topc(X1,X0) & (k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0))) | (k2_pre_topc(X0,X1) != X1 & v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.21/0.98    inference(ennf_transformation,[],[f10])).
% 3.21/0.98  
% 3.21/0.98  fof(f24,plain,(
% 3.21/0.98    ? [X0] : (? [X1] : (((~v4_pre_topc(X1,X0) & k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) | (k2_pre_topc(X0,X1) != X1 & v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.21/0.98    inference(flattening,[],[f23])).
% 3.21/0.98  
% 3.21/0.98  fof(f40,plain,(
% 3.21/0.98    ( ! [X0] : (? [X1] : (((~v4_pre_topc(X1,X0) & k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) | (k2_pre_topc(X0,X1) != X1 & v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (((~v4_pre_topc(sK5,X0) & k2_pre_topc(X0,sK5) = sK5 & v2_pre_topc(X0)) | (k2_pre_topc(X0,sK5) != sK5 & v4_pre_topc(sK5,X0))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.21/0.98    introduced(choice_axiom,[])).
% 3.21/0.98  
% 3.21/0.98  fof(f39,plain,(
% 3.21/0.98    ? [X0] : (? [X1] : (((~v4_pre_topc(X1,X0) & k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) | (k2_pre_topc(X0,X1) != X1 & v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (((~v4_pre_topc(X1,sK4) & k2_pre_topc(sK4,X1) = X1 & v2_pre_topc(sK4)) | (k2_pre_topc(sK4,X1) != X1 & v4_pre_topc(X1,sK4))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))) & l1_pre_topc(sK4))),
% 3.21/0.98    introduced(choice_axiom,[])).
% 3.21/0.98  
% 3.21/0.98  fof(f41,plain,(
% 3.21/0.98    (((~v4_pre_topc(sK5,sK4) & k2_pre_topc(sK4,sK5) = sK5 & v2_pre_topc(sK4)) | (k2_pre_topc(sK4,sK5) != sK5 & v4_pre_topc(sK5,sK4))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))) & l1_pre_topc(sK4)),
% 3.21/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f24,f40,f39])).
% 3.21/0.98  
% 3.21/0.98  fof(f66,plain,(
% 3.21/0.98    v2_pre_topc(sK4) | v4_pre_topc(sK5,sK4)),
% 3.21/0.98    inference(cnf_transformation,[],[f41])).
% 3.21/0.98  
% 3.21/0.98  fof(f64,plain,(
% 3.21/0.98    l1_pre_topc(sK4)),
% 3.21/0.98    inference(cnf_transformation,[],[f41])).
% 3.21/0.98  
% 3.21/0.98  fof(f58,plain,(
% 3.21/0.98    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.21/0.98    inference(cnf_transformation,[],[f38])).
% 3.21/0.98  
% 3.21/0.98  fof(f5,axiom,(
% 3.21/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,X1) => v4_pre_topc(X2,X0))) => v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0))))),
% 3.21/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/0.98  
% 3.21/0.98  fof(f16,plain,(
% 3.21/0.98    ! [X0] : (! [X1] : ((v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) | ? [X2] : ((~v4_pre_topc(X2,X0) & r2_hidden(X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.21/0.98    inference(ennf_transformation,[],[f5])).
% 3.21/0.98  
% 3.21/0.98  fof(f17,plain,(
% 3.21/0.98    ! [X0] : (! [X1] : (v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) | ? [X2] : (~v4_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.21/0.98    inference(flattening,[],[f16])).
% 3.21/0.98  
% 3.21/0.98  fof(f29,plain,(
% 3.21/0.98    ! [X1,X0] : (? [X2] : (~v4_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v4_pre_topc(sK1(X0,X1),X0) & r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.21/0.98    introduced(choice_axiom,[])).
% 3.21/0.98  
% 3.21/0.98  fof(f30,plain,(
% 3.21/0.98    ! [X0] : (! [X1] : (v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) | (~v4_pre_topc(sK1(X0,X1),X0) & r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.21/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f29])).
% 3.21/0.98  
% 3.21/0.98  fof(f52,plain,(
% 3.21/0.98    ( ! [X0,X1] : (v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(sK1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.21/0.98    inference(cnf_transformation,[],[f30])).
% 3.21/0.98  
% 3.21/0.98  fof(f71,plain,(
% 3.21/0.98    ~v4_pre_topc(sK5,sK4) | k2_pre_topc(sK4,sK5) != sK5),
% 3.21/0.98    inference(cnf_transformation,[],[f41])).
% 3.21/0.98  
% 3.21/0.98  fof(f65,plain,(
% 3.21/0.98    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))),
% 3.21/0.98    inference(cnf_transformation,[],[f41])).
% 3.21/0.98  
% 3.21/0.98  fof(f8,axiom,(
% 3.21/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 3.21/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/0.98  
% 3.21/0.98  fof(f22,plain,(
% 3.21/0.98    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.21/0.98    inference(ennf_transformation,[],[f8])).
% 3.21/0.98  
% 3.21/0.98  fof(f63,plain,(
% 3.21/0.98    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.21/0.98    inference(cnf_transformation,[],[f22])).
% 3.21/0.98  
% 3.21/0.98  fof(f1,axiom,(
% 3.21/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.21/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/0.98  
% 3.21/0.98  fof(f25,plain,(
% 3.21/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.21/0.98    inference(nnf_transformation,[],[f1])).
% 3.21/0.98  
% 3.21/0.98  fof(f26,plain,(
% 3.21/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.21/0.98    inference(flattening,[],[f25])).
% 3.21/0.98  
% 3.21/0.98  fof(f44,plain,(
% 3.21/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.21/0.98    inference(cnf_transformation,[],[f26])).
% 3.21/0.98  
% 3.21/0.98  fof(f68,plain,(
% 3.21/0.98    k2_pre_topc(sK4,sK5) = sK5 | v4_pre_topc(sK5,sK4)),
% 3.21/0.98    inference(cnf_transformation,[],[f41])).
% 3.21/0.98  
% 3.21/0.98  fof(f42,plain,(
% 3.21/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.21/0.98    inference(cnf_transformation,[],[f26])).
% 3.21/0.98  
% 3.21/0.98  fof(f73,plain,(
% 3.21/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.21/0.98    inference(equality_resolution,[],[f42])).
% 3.21/0.98  
% 3.21/0.98  fof(f4,axiom,(
% 3.21/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.21/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/0.98  
% 3.21/0.98  fof(f14,plain,(
% 3.21/0.98    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.21/0.98    inference(ennf_transformation,[],[f4])).
% 3.21/0.98  
% 3.21/0.98  fof(f15,plain,(
% 3.21/0.98    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.21/0.98    inference(flattening,[],[f14])).
% 3.21/0.98  
% 3.21/0.98  fof(f49,plain,(
% 3.21/0.98    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.21/0.98    inference(cnf_transformation,[],[f15])).
% 3.21/0.98  
% 3.21/0.98  fof(f3,axiom,(
% 3.21/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 3.21/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/0.98  
% 3.21/0.98  fof(f12,plain,(
% 3.21/0.98    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.21/0.98    inference(ennf_transformation,[],[f3])).
% 3.21/0.98  
% 3.21/0.98  fof(f13,plain,(
% 3.21/0.98    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.21/0.98    inference(flattening,[],[f12])).
% 3.21/0.98  
% 3.21/0.98  fof(f27,plain,(
% 3.21/0.98    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) => (~r2_hidden(sK0(X0,X1,X2),X2) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),X0)))),
% 3.21/0.98    introduced(choice_axiom,[])).
% 3.21/0.98  
% 3.21/0.98  fof(f28,plain,(
% 3.21/0.98    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | (~r2_hidden(sK0(X0,X1,X2),X2) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.21/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f27])).
% 3.21/0.98  
% 3.21/0.98  fof(f48,plain,(
% 3.21/0.98    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r2_hidden(sK0(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.21/0.98    inference(cnf_transformation,[],[f28])).
% 3.21/0.98  
% 3.21/0.98  fof(f47,plain,(
% 3.21/0.98    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | r2_hidden(sK0(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.21/0.98    inference(cnf_transformation,[],[f28])).
% 3.21/0.98  
% 3.21/0.98  fof(f2,axiom,(
% 3.21/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.21/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/0.98  
% 3.21/0.98  fof(f11,plain,(
% 3.21/0.98    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.21/0.98    inference(ennf_transformation,[],[f2])).
% 3.21/0.98  
% 3.21/0.98  fof(f45,plain,(
% 3.21/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.21/0.98    inference(cnf_transformation,[],[f11])).
% 3.21/0.98  
% 3.21/0.98  fof(f6,axiom,(
% 3.21/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (r2_hidden(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X3) & v4_pre_topc(X3,X0)) => r2_hidden(X2,X3)))))))),
% 3.21/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/0.98  
% 3.21/0.98  fof(f18,plain,(
% 3.21/0.98    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ! [X3] : ((r2_hidden(X2,X3) | (~r1_tarski(X1,X3) | ~v4_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.21/0.98    inference(ennf_transformation,[],[f6])).
% 3.21/0.98  
% 3.21/0.98  fof(f19,plain,(
% 3.21/0.98    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ! [X3] : (r2_hidden(X2,X3) | ~r1_tarski(X1,X3) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.21/0.98    inference(flattening,[],[f18])).
% 3.21/0.98  
% 3.21/0.98  fof(f31,plain,(
% 3.21/0.98    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ? [X3] : (~r2_hidden(X2,X3) & r1_tarski(X1,X3) & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (r2_hidden(X2,X3) | ~r1_tarski(X1,X3) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~r2_hidden(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.21/0.98    inference(nnf_transformation,[],[f19])).
% 3.21/0.98  
% 3.21/0.98  fof(f32,plain,(
% 3.21/0.98    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ? [X3] : (~r2_hidden(X2,X3) & r1_tarski(X1,X3) & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r2_hidden(X2,X4) | ~r1_tarski(X1,X4) | ~v4_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~r2_hidden(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.21/0.98    inference(rectify,[],[f31])).
% 3.21/0.98  
% 3.21/0.98  fof(f33,plain,(
% 3.21/0.98    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X2,X3) & r1_tarski(X1,X3) & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~r2_hidden(X2,sK2(X0,X1,X2)) & r1_tarski(X1,sK2(X0,X1,X2)) & v4_pre_topc(sK2(X0,X1,X2),X0) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.21/0.98    introduced(choice_axiom,[])).
% 3.21/0.98  
% 3.21/0.98  fof(f34,plain,(
% 3.21/0.98    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | (~r2_hidden(X2,sK2(X0,X1,X2)) & r1_tarski(X1,sK2(X0,X1,X2)) & v4_pre_topc(sK2(X0,X1,X2),X0) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r2_hidden(X2,X4) | ~r1_tarski(X1,X4) | ~v4_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~r2_hidden(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.21/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).
% 3.21/0.98  
% 3.21/0.98  fof(f53,plain,(
% 3.21/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X2,X4) | ~r1_tarski(X1,X4) | ~v4_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~r2_hidden(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.21/0.98    inference(cnf_transformation,[],[f34])).
% 3.21/0.98  
% 3.21/0.98  fof(f62,plain,(
% 3.21/0.98    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),sK3(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.21/0.98    inference(cnf_transformation,[],[f38])).
% 3.21/0.98  
% 3.21/0.98  fof(f51,plain,(
% 3.21/0.98    ( ! [X0,X1] : (v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) | r2_hidden(sK1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.21/0.98    inference(cnf_transformation,[],[f30])).
% 3.21/0.98  
% 3.21/0.98  fof(f50,plain,(
% 3.21/0.98    ( ! [X0,X1] : (v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.21/0.98    inference(cnf_transformation,[],[f30])).
% 3.21/0.98  
% 3.21/0.98  cnf(c_968,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_6047,plain,
% 3.21/0.98      ( k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)) != X1
% 3.21/0.98      | sK5 != X1
% 3.21/0.98      | sK5 = k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)) ),
% 3.21/0.98      inference(instantiation,[status(thm)],[c_968]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_6048,plain,
% 3.21/0.98      ( k6_setfam_1(u1_struct_0(sK4),sK3(sK4,sK5)) != sK5
% 3.21/0.98      | sK5 = k6_setfam_1(u1_struct_0(sK4),sK3(sK4,sK5))
% 3.21/0.98      | sK5 != sK5 ),
% 3.21/0.98      inference(instantiation,[status(thm)],[c_6047]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_976,plain,
% 3.21/0.98      ( ~ v4_pre_topc(X0,X1) | v4_pre_topc(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.21/0.98      theory(equality) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_1777,plain,
% 3.21/0.98      ( ~ v4_pre_topc(X0,X1)
% 3.21/0.98      | v4_pre_topc(sK5,sK4)
% 3.21/0.98      | sK4 != X1
% 3.21/0.98      | sK5 != X0 ),
% 3.21/0.98      inference(instantiation,[status(thm)],[c_976]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_2640,plain,
% 3.21/0.98      ( ~ v4_pre_topc(X0,sK4)
% 3.21/0.98      | v4_pre_topc(sK5,sK4)
% 3.21/0.98      | sK4 != sK4
% 3.21/0.98      | sK5 != X0 ),
% 3.21/0.98      inference(instantiation,[status(thm)],[c_1777]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_3656,plain,
% 3.21/0.98      ( ~ v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)),sK4)
% 3.21/0.98      | v4_pre_topc(sK5,sK4)
% 3.21/0.98      | sK4 != sK4
% 3.21/0.98      | sK5 != k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)) ),
% 3.21/0.98      inference(instantiation,[status(thm)],[c_2640]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_3668,plain,
% 3.21/0.98      ( ~ v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),sK3(sK4,sK5)),sK4)
% 3.21/0.98      | v4_pre_topc(sK5,sK4)
% 3.21/0.98      | sK4 != sK4
% 3.21/0.98      | sK5 != k6_setfam_1(u1_struct_0(sK4),sK3(sK4,sK5)) ),
% 3.21/0.98      inference(instantiation,[status(thm)],[c_3656]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_967,plain,( X0 = X0 ),theory(equality) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_2999,plain,
% 3.21/0.98      ( sK4 = sK4 ),
% 3.21/0.98      inference(instantiation,[status(thm)],[c_967]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_19,plain,
% 3.21/0.98      ( v4_pre_topc(X0,X1)
% 3.21/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.21/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.21/0.98      | ~ r2_hidden(X0,sK3(X1,X2))
% 3.21/0.98      | ~ v2_pre_topc(X1)
% 3.21/0.98      | ~ l1_pre_topc(X1) ),
% 3.21/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_27,negated_conjecture,
% 3.21/0.98      ( v4_pre_topc(sK5,sK4) | v2_pre_topc(sK4) ),
% 3.21/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_459,plain,
% 3.21/0.98      ( v4_pre_topc(X0,X1)
% 3.21/0.98      | v4_pre_topc(sK5,sK4)
% 3.21/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.21/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.21/0.98      | ~ r2_hidden(X0,sK3(X1,X2))
% 3.21/0.98      | ~ l1_pre_topc(X1)
% 3.21/0.98      | sK4 != X1 ),
% 3.21/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_27]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_460,plain,
% 3.21/0.98      ( v4_pre_topc(X0,sK4)
% 3.21/0.98      | v4_pre_topc(sK5,sK4)
% 3.21/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.21/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.21/0.98      | ~ r2_hidden(X0,sK3(sK4,X1))
% 3.21/0.98      | ~ l1_pre_topc(sK4) ),
% 3.21/0.98      inference(unflattening,[status(thm)],[c_459]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_29,negated_conjecture,
% 3.21/0.98      ( l1_pre_topc(sK4) ),
% 3.21/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_464,plain,
% 3.21/0.98      ( ~ r2_hidden(X0,sK3(sK4,X1))
% 3.21/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.21/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.21/0.98      | v4_pre_topc(sK5,sK4)
% 3.21/0.98      | v4_pre_topc(X0,sK4) ),
% 3.21/0.98      inference(global_propositional_subsumption,
% 3.21/0.98                [status(thm)],
% 3.21/0.98                [c_460,c_29]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_465,plain,
% 3.21/0.98      ( v4_pre_topc(X0,sK4)
% 3.21/0.98      | v4_pre_topc(sK5,sK4)
% 3.21/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.21/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.21/0.98      | ~ r2_hidden(X0,sK3(sK4,X1)) ),
% 3.21/0.98      inference(renaming,[status(thm)],[c_464]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_2791,plain,
% 3.21/0.98      ( v4_pre_topc(sK1(sK4,sK3(sK4,X0)),sK4)
% 3.21/0.98      | v4_pre_topc(sK5,sK4)
% 3.21/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.21/0.98      | ~ m1_subset_1(sK1(sK4,sK3(sK4,X0)),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.21/0.98      | ~ r2_hidden(sK1(sK4,sK3(sK4,X0)),sK3(sK4,X0)) ),
% 3.21/0.98      inference(instantiation,[status(thm)],[c_465]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_2793,plain,
% 3.21/0.98      ( v4_pre_topc(sK1(sK4,sK3(sK4,sK5)),sK4)
% 3.21/0.98      | v4_pre_topc(sK5,sK4)
% 3.21/0.98      | ~ m1_subset_1(sK1(sK4,sK3(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.21/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.21/0.98      | ~ r2_hidden(sK1(sK4,sK3(sK4,sK5)),sK3(sK4,sK5)) ),
% 3.21/0.98      inference(instantiation,[status(thm)],[c_2791]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_20,plain,
% 3.21/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.21/0.98      | m1_subset_1(sK3(X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.21/0.98      | ~ v2_pre_topc(X1)
% 3.21/0.98      | ~ l1_pre_topc(X1) ),
% 3.21/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_438,plain,
% 3.21/0.98      ( v4_pre_topc(sK5,sK4)
% 3.21/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.21/0.98      | m1_subset_1(sK3(X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.21/0.98      | ~ l1_pre_topc(X1)
% 3.21/0.98      | sK4 != X1 ),
% 3.21/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_27]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_439,plain,
% 3.21/0.98      ( v4_pre_topc(sK5,sK4)
% 3.21/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.21/0.98      | m1_subset_1(sK3(sK4,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 3.21/0.98      | ~ l1_pre_topc(sK4) ),
% 3.21/0.98      inference(unflattening,[status(thm)],[c_438]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_443,plain,
% 3.21/0.98      ( m1_subset_1(sK3(sK4,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 3.21/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.21/0.98      | v4_pre_topc(sK5,sK4) ),
% 3.21/0.98      inference(global_propositional_subsumption,
% 3.21/0.98                [status(thm)],
% 3.21/0.98                [c_439,c_29]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_444,plain,
% 3.21/0.98      ( v4_pre_topc(sK5,sK4)
% 3.21/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.21/0.98      | m1_subset_1(sK3(sK4,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
% 3.21/0.98      inference(renaming,[status(thm)],[c_443]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_1529,plain,
% 3.21/0.98      ( v4_pre_topc(sK5,sK4) = iProver_top
% 3.21/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.21/0.98      | m1_subset_1(sK3(sK4,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = iProver_top ),
% 3.21/0.98      inference(predicate_to_equality,[status(thm)],[c_444]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_8,plain,
% 3.21/0.98      ( ~ v4_pre_topc(sK1(X0,X1),X0)
% 3.21/0.98      | v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
% 3.21/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.21/0.98      | ~ v2_pre_topc(X0)
% 3.21/0.98      | ~ l1_pre_topc(X0) ),
% 3.21/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_414,plain,
% 3.21/0.98      ( ~ v4_pre_topc(sK1(X0,X1),X0)
% 3.21/0.98      | v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
% 3.21/0.98      | v4_pre_topc(sK5,sK4)
% 3.21/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.21/0.98      | ~ l1_pre_topc(X0)
% 3.21/0.98      | sK4 != X0 ),
% 3.21/0.98      inference(resolution_lifted,[status(thm)],[c_8,c_27]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_415,plain,
% 3.21/0.98      ( ~ v4_pre_topc(sK1(sK4,X0),sK4)
% 3.21/0.98      | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4)
% 3.21/0.98      | v4_pre_topc(sK5,sK4)
% 3.21/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 3.21/0.98      | ~ l1_pre_topc(sK4) ),
% 3.21/0.98      inference(unflattening,[status(thm)],[c_414]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_419,plain,
% 3.21/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 3.21/0.98      | v4_pre_topc(sK5,sK4)
% 3.21/0.98      | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4)
% 3.21/0.98      | ~ v4_pre_topc(sK1(sK4,X0),sK4) ),
% 3.21/0.98      inference(global_propositional_subsumption,
% 3.21/0.98                [status(thm)],
% 3.21/0.98                [c_415,c_29]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_420,plain,
% 3.21/0.98      ( ~ v4_pre_topc(sK1(sK4,X0),sK4)
% 3.21/0.98      | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4)
% 3.21/0.98      | v4_pre_topc(sK5,sK4)
% 3.21/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
% 3.21/0.98      inference(renaming,[status(thm)],[c_419]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_1530,plain,
% 3.21/0.98      ( v4_pre_topc(sK1(sK4,X0),sK4) != iProver_top
% 3.21/0.98      | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4) = iProver_top
% 3.21/0.98      | v4_pre_topc(sK5,sK4) = iProver_top
% 3.21/0.98      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top ),
% 3.21/0.98      inference(predicate_to_equality,[status(thm)],[c_420]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_22,negated_conjecture,
% 3.21/0.98      ( ~ v4_pre_topc(sK5,sK4) | k2_pre_topc(sK4,sK5) != sK5 ),
% 3.21/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_36,plain,
% 3.21/0.98      ( k2_pre_topc(sK4,sK5) != sK5
% 3.21/0.98      | v4_pre_topc(sK5,sK4) != iProver_top ),
% 3.21/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_421,plain,
% 3.21/0.98      ( v4_pre_topc(sK1(sK4,X0),sK4) != iProver_top
% 3.21/0.98      | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4) = iProver_top
% 3.21/0.98      | v4_pre_topc(sK5,sK4) = iProver_top
% 3.21/0.98      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top ),
% 3.21/0.98      inference(predicate_to_equality,[status(thm)],[c_420]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_28,negated_conjecture,
% 3.21/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 3.21/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_1533,plain,
% 3.21/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 3.21/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_21,plain,
% 3.21/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.21/0.98      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 3.21/0.98      | ~ l1_pre_topc(X1) ),
% 3.21/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_616,plain,
% 3.21/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.21/0.98      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 3.21/0.98      | sK4 != X1 ),
% 3.21/0.98      inference(resolution_lifted,[status(thm)],[c_21,c_29]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_617,plain,
% 3.21/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.21/0.98      | r1_tarski(X0,k2_pre_topc(sK4,X0)) ),
% 3.21/0.98      inference(unflattening,[status(thm)],[c_616]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_1523,plain,
% 3.21/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.21/0.98      | r1_tarski(X0,k2_pre_topc(sK4,X0)) = iProver_top ),
% 3.21/0.98      inference(predicate_to_equality,[status(thm)],[c_617]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_1628,plain,
% 3.21/0.98      ( r1_tarski(sK5,k2_pre_topc(sK4,sK5)) = iProver_top ),
% 3.21/0.98      inference(superposition,[status(thm)],[c_1533,c_1523]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_0,plain,
% 3.21/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.21/0.98      inference(cnf_transformation,[],[f44]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_1541,plain,
% 3.21/0.98      ( X0 = X1
% 3.21/0.98      | r1_tarski(X0,X1) != iProver_top
% 3.21/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 3.21/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_1828,plain,
% 3.21/0.98      ( k2_pre_topc(sK4,sK5) = sK5
% 3.21/0.98      | r1_tarski(k2_pre_topc(sK4,sK5),sK5) != iProver_top ),
% 3.21/0.98      inference(superposition,[status(thm)],[c_1628,c_1541]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_25,negated_conjecture,
% 3.21/0.98      ( v4_pre_topc(sK5,sK4) | k2_pre_topc(sK4,sK5) = sK5 ),
% 3.21/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_2,plain,
% 3.21/0.98      ( r1_tarski(X0,X0) ),
% 3.21/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_93,plain,
% 3.21/0.98      ( r1_tarski(sK5,sK5) ),
% 3.21/0.98      inference(instantiation,[status(thm)],[c_2]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_619,plain,
% 3.21/0.98      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.21/0.98      | r1_tarski(sK5,k2_pre_topc(sK4,sK5)) ),
% 3.21/0.98      inference(instantiation,[status(thm)],[c_617]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_7,plain,
% 3.21/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.21/0.98      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.21/0.98      | ~ l1_pre_topc(X1) ),
% 3.21/0.98      inference(cnf_transformation,[],[f49]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_709,plain,
% 3.21/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.21/0.98      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.21/0.98      | sK4 != X1 ),
% 3.21/0.98      inference(resolution_lifted,[status(thm)],[c_7,c_29]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_710,plain,
% 3.21/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.21/0.98      | m1_subset_1(k2_pre_topc(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 3.21/0.98      inference(unflattening,[status(thm)],[c_709]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_712,plain,
% 3.21/0.98      ( m1_subset_1(k2_pre_topc(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.21/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 3.21/0.98      inference(instantiation,[status(thm)],[c_710]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_1584,plain,
% 3.21/0.98      ( ~ r1_tarski(k2_pre_topc(sK4,sK5),sK5)
% 3.21/0.98      | ~ r1_tarski(sK5,k2_pre_topc(sK4,sK5))
% 3.21/0.98      | k2_pre_topc(sK4,sK5) = sK5 ),
% 3.21/0.98      inference(instantiation,[status(thm)],[c_0]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_4,plain,
% 3.21/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.21/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.21/0.98      | ~ r2_hidden(sK0(X1,X0,X2),X2)
% 3.21/0.98      | r1_tarski(X0,X2) ),
% 3.21/0.98      inference(cnf_transformation,[],[f48]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_1608,plain,
% 3.21/0.98      ( ~ m1_subset_1(k2_pre_topc(sK4,sK5),k1_zfmisc_1(X0))
% 3.21/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(X0))
% 3.21/0.98      | ~ r2_hidden(sK0(X0,k2_pre_topc(sK4,sK5),sK5),sK5)
% 3.21/0.98      | r1_tarski(k2_pre_topc(sK4,sK5),sK5) ),
% 3.21/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_1682,plain,
% 3.21/0.98      ( ~ m1_subset_1(k2_pre_topc(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.21/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.21/0.98      | ~ r2_hidden(sK0(u1_struct_0(sK4),k2_pre_topc(sK4,sK5),sK5),sK5)
% 3.21/0.98      | r1_tarski(k2_pre_topc(sK4,sK5),sK5) ),
% 3.21/0.98      inference(instantiation,[status(thm)],[c_1608]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_5,plain,
% 3.21/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.21/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.21/0.98      | r2_hidden(sK0(X1,X0,X2),X0)
% 3.21/0.98      | r1_tarski(X0,X2) ),
% 3.21/0.98      inference(cnf_transformation,[],[f47]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_1609,plain,
% 3.21/0.98      ( ~ m1_subset_1(k2_pre_topc(sK4,sK5),k1_zfmisc_1(X0))
% 3.21/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(X0))
% 3.21/0.98      | r2_hidden(sK0(X0,k2_pre_topc(sK4,sK5),sK5),k2_pre_topc(sK4,sK5))
% 3.21/0.98      | r1_tarski(k2_pre_topc(sK4,sK5),sK5) ),
% 3.21/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_1690,plain,
% 3.21/0.98      ( ~ m1_subset_1(k2_pre_topc(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.21/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.21/0.98      | r2_hidden(sK0(u1_struct_0(sK4),k2_pre_topc(sK4,sK5),sK5),k2_pre_topc(sK4,sK5))
% 3.21/0.98      | r1_tarski(k2_pre_topc(sK4,sK5),sK5) ),
% 3.21/0.98      inference(instantiation,[status(thm)],[c_1609]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_3,plain,
% 3.21/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.21/0.98      | ~ r2_hidden(X2,X0)
% 3.21/0.98      | r2_hidden(X2,X1) ),
% 3.21/0.98      inference(cnf_transformation,[],[f45]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_1590,plain,
% 3.21/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.21/0.98      | ~ r2_hidden(X1,X0)
% 3.21/0.98      | r2_hidden(X1,u1_struct_0(sK4)) ),
% 3.21/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_1926,plain,
% 3.21/0.98      ( ~ m1_subset_1(k2_pre_topc(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.21/0.98      | ~ r2_hidden(sK0(u1_struct_0(sK4),k2_pre_topc(sK4,sK5),sK5),k2_pre_topc(sK4,sK5))
% 3.21/0.98      | r2_hidden(sK0(u1_struct_0(sK4),k2_pre_topc(sK4,sK5),sK5),u1_struct_0(sK4)) ),
% 3.21/0.98      inference(instantiation,[status(thm)],[c_1590]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_15,plain,
% 3.21/0.98      ( ~ v4_pre_topc(X0,X1)
% 3.21/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.21/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.21/0.98      | r2_hidden(X3,X0)
% 3.21/0.98      | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
% 3.21/0.98      | ~ r2_hidden(X3,u1_struct_0(X1))
% 3.21/0.98      | ~ r1_tarski(X2,X0)
% 3.21/0.98      | ~ l1_pre_topc(X1) ),
% 3.21/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_628,plain,
% 3.21/0.98      ( ~ v4_pre_topc(X0,X1)
% 3.21/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.21/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.21/0.98      | r2_hidden(X3,X0)
% 3.21/0.98      | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
% 3.21/0.98      | ~ r2_hidden(X3,u1_struct_0(X1))
% 3.21/0.98      | ~ r1_tarski(X2,X0)
% 3.21/0.98      | sK4 != X1 ),
% 3.21/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_29]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_629,plain,
% 3.21/0.98      ( ~ v4_pre_topc(X0,sK4)
% 3.21/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.21/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.21/0.98      | r2_hidden(X2,X0)
% 3.21/0.98      | ~ r2_hidden(X2,k2_pre_topc(sK4,X1))
% 3.21/0.98      | ~ r2_hidden(X2,u1_struct_0(sK4))
% 3.21/0.98      | ~ r1_tarski(X1,X0) ),
% 3.21/0.98      inference(unflattening,[status(thm)],[c_628]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_2262,plain,
% 3.21/0.98      ( ~ v4_pre_topc(X0,sK4)
% 3.21/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.21/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.21/0.98      | r2_hidden(sK0(u1_struct_0(sK4),k2_pre_topc(sK4,sK5),sK5),X0)
% 3.21/0.98      | ~ r2_hidden(sK0(u1_struct_0(sK4),k2_pre_topc(sK4,sK5),sK5),k2_pre_topc(sK4,X1))
% 3.21/0.98      | ~ r2_hidden(sK0(u1_struct_0(sK4),k2_pre_topc(sK4,sK5),sK5),u1_struct_0(sK4))
% 3.21/0.98      | ~ r1_tarski(X1,X0) ),
% 3.21/0.98      inference(instantiation,[status(thm)],[c_629]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_2264,plain,
% 3.21/0.98      ( ~ v4_pre_topc(sK5,sK4)
% 3.21/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.21/0.98      | ~ r2_hidden(sK0(u1_struct_0(sK4),k2_pre_topc(sK4,sK5),sK5),k2_pre_topc(sK4,sK5))
% 3.21/0.98      | ~ r2_hidden(sK0(u1_struct_0(sK4),k2_pre_topc(sK4,sK5),sK5),u1_struct_0(sK4))
% 3.21/0.98      | r2_hidden(sK0(u1_struct_0(sK4),k2_pre_topc(sK4,sK5),sK5),sK5)
% 3.21/0.98      | ~ r1_tarski(sK5,sK5) ),
% 3.21/0.98      inference(instantiation,[status(thm)],[c_2262]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_2311,plain,
% 3.21/0.98      ( k2_pre_topc(sK4,sK5) = sK5 ),
% 3.21/0.98      inference(global_propositional_subsumption,
% 3.21/0.98                [status(thm)],
% 3.21/0.98                [c_1828,c_28,c_25,c_93,c_619,c_712,c_1584,c_1682,c_1690,
% 3.21/0.98                 c_1926,c_2264]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_2423,plain,
% 3.21/0.98      ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4) = iProver_top
% 3.21/0.98      | v4_pre_topc(sK1(sK4,X0),sK4) != iProver_top
% 3.21/0.98      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top ),
% 3.21/0.98      inference(global_propositional_subsumption,
% 3.21/0.98                [status(thm)],
% 3.21/0.98                [c_1530,c_28,c_25,c_36,c_93,c_421,c_619,c_712,c_1584,
% 3.21/0.98                 c_1682,c_1690,c_1926,c_2264]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_2424,plain,
% 3.21/0.98      ( v4_pre_topc(sK1(sK4,X0),sK4) != iProver_top
% 3.21/0.98      | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4) = iProver_top
% 3.21/0.98      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top ),
% 3.21/0.98      inference(renaming,[status(thm)],[c_2423]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_2430,plain,
% 3.21/0.98      ( v4_pre_topc(sK1(sK4,sK3(sK4,X0)),sK4) != iProver_top
% 3.21/0.98      | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)),sK4) = iProver_top
% 3.21/0.98      | v4_pre_topc(sK5,sK4) = iProver_top
% 3.21/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 3.21/0.98      inference(superposition,[status(thm)],[c_1529,c_2424]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_2432,plain,
% 3.21/0.98      ( ~ v4_pre_topc(sK1(sK4,sK3(sK4,X0)),sK4)
% 3.21/0.98      | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)),sK4)
% 3.21/0.98      | v4_pre_topc(sK5,sK4)
% 3.21/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 3.21/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_2430]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_2434,plain,
% 3.21/0.98      ( ~ v4_pre_topc(sK1(sK4,sK3(sK4,sK5)),sK4)
% 3.21/0.98      | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),sK3(sK4,sK5)),sK4)
% 3.21/0.98      | v4_pre_topc(sK5,sK4)
% 3.21/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 3.21/0.98      inference(instantiation,[status(thm)],[c_2432]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_16,plain,
% 3.21/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.21/0.98      | ~ v2_pre_topc(X1)
% 3.21/0.98      | ~ l1_pre_topc(X1)
% 3.21/0.98      | k6_setfam_1(u1_struct_0(X1),sK3(X1,X0)) = k2_pre_topc(X1,X0) ),
% 3.21/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_535,plain,
% 3.21/0.98      ( v4_pre_topc(sK5,sK4)
% 3.21/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.21/0.98      | ~ l1_pre_topc(X1)
% 3.21/0.98      | k6_setfam_1(u1_struct_0(X1),sK3(X1,X0)) = k2_pre_topc(X1,X0)
% 3.21/0.98      | sK4 != X1 ),
% 3.21/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_27]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_536,plain,
% 3.21/0.98      ( v4_pre_topc(sK5,sK4)
% 3.21/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.21/0.98      | ~ l1_pre_topc(sK4)
% 3.21/0.98      | k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)) = k2_pre_topc(sK4,X0) ),
% 3.21/0.98      inference(unflattening,[status(thm)],[c_535]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_540,plain,
% 3.21/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.21/0.98      | v4_pre_topc(sK5,sK4)
% 3.21/0.98      | k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)) = k2_pre_topc(sK4,X0) ),
% 3.21/0.98      inference(global_propositional_subsumption,
% 3.21/0.98                [status(thm)],
% 3.21/0.98                [c_536,c_29]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_541,plain,
% 3.21/0.98      ( v4_pre_topc(sK5,sK4)
% 3.21/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.21/0.98      | k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)) = k2_pre_topc(sK4,X0) ),
% 3.21/0.98      inference(renaming,[status(thm)],[c_540]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_1525,plain,
% 3.21/0.98      ( k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)) = k2_pre_topc(sK4,X0)
% 3.21/0.98      | v4_pre_topc(sK5,sK4) = iProver_top
% 3.21/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 3.21/0.98      inference(predicate_to_equality,[status(thm)],[c_541]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_2020,plain,
% 3.21/0.98      ( k6_setfam_1(u1_struct_0(sK4),sK3(sK4,sK5)) = k2_pre_topc(sK4,sK5)
% 3.21/0.98      | v4_pre_topc(sK5,sK4) = iProver_top ),
% 3.21/0.98      inference(superposition,[status(thm)],[c_1533,c_1525]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_2313,plain,
% 3.21/0.98      ( k6_setfam_1(u1_struct_0(sK4),sK3(sK4,sK5)) = sK5
% 3.21/0.98      | v4_pre_topc(sK5,sK4) = iProver_top ),
% 3.21/0.98      inference(demodulation,[status(thm)],[c_2311,c_2020]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_9,plain,
% 3.21/0.98      ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
% 3.21/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.21/0.98      | r2_hidden(sK1(X0,X1),X1)
% 3.21/0.98      | ~ v2_pre_topc(X0)
% 3.21/0.98      | ~ l1_pre_topc(X0) ),
% 3.21/0.98      inference(cnf_transformation,[],[f51]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_390,plain,
% 3.21/0.98      ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
% 3.21/0.98      | v4_pre_topc(sK5,sK4)
% 3.21/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.21/0.98      | r2_hidden(sK1(X0,X1),X1)
% 3.21/0.98      | ~ l1_pre_topc(X0)
% 3.21/0.98      | sK4 != X0 ),
% 3.21/0.98      inference(resolution_lifted,[status(thm)],[c_9,c_27]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_391,plain,
% 3.21/0.98      ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4)
% 3.21/0.98      | v4_pre_topc(sK5,sK4)
% 3.21/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 3.21/0.98      | r2_hidden(sK1(sK4,X0),X0)
% 3.21/0.98      | ~ l1_pre_topc(sK4) ),
% 3.21/0.98      inference(unflattening,[status(thm)],[c_390]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_395,plain,
% 3.21/0.98      ( r2_hidden(sK1(sK4,X0),X0)
% 3.21/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 3.21/0.98      | v4_pre_topc(sK5,sK4)
% 3.21/0.98      | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4) ),
% 3.21/0.98      inference(global_propositional_subsumption,
% 3.21/0.98                [status(thm)],
% 3.21/0.98                [c_391,c_29]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_396,plain,
% 3.21/0.98      ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4)
% 3.21/0.98      | v4_pre_topc(sK5,sK4)
% 3.21/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 3.21/0.98      | r2_hidden(sK1(sK4,X0),X0) ),
% 3.21/0.98      inference(renaming,[status(thm)],[c_395]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_1531,plain,
% 3.21/0.98      ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4) = iProver_top
% 3.21/0.98      | v4_pre_topc(sK5,sK4) = iProver_top
% 3.21/0.98      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
% 3.21/0.98      | r2_hidden(sK1(sK4,X0),X0) = iProver_top ),
% 3.21/0.98      inference(predicate_to_equality,[status(thm)],[c_396]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_2079,plain,
% 3.21/0.98      ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)),sK4) = iProver_top
% 3.21/0.98      | v4_pre_topc(sK5,sK4) = iProver_top
% 3.21/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.21/0.98      | r2_hidden(sK1(sK4,sK3(sK4,X0)),sK3(sK4,X0)) = iProver_top ),
% 3.21/0.98      inference(superposition,[status(thm)],[c_1529,c_1531]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_2081,plain,
% 3.21/0.98      ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)),sK4)
% 3.21/0.98      | v4_pre_topc(sK5,sK4)
% 3.21/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.21/0.98      | r2_hidden(sK1(sK4,sK3(sK4,X0)),sK3(sK4,X0)) ),
% 3.21/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_2079]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_2083,plain,
% 3.21/0.98      ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),sK3(sK4,sK5)),sK4)
% 3.21/0.98      | v4_pre_topc(sK5,sK4)
% 3.21/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.21/0.98      | r2_hidden(sK1(sK4,sK3(sK4,sK5)),sK3(sK4,sK5)) ),
% 3.21/0.98      inference(instantiation,[status(thm)],[c_2081]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_10,plain,
% 3.21/0.98      ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
% 3.21/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.21/0.98      | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 3.21/0.98      | ~ v2_pre_topc(X0)
% 3.21/0.98      | ~ l1_pre_topc(X0) ),
% 3.21/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_366,plain,
% 3.21/0.98      ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
% 3.21/0.98      | v4_pre_topc(sK5,sK4)
% 3.21/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.21/0.98      | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 3.21/0.98      | ~ l1_pre_topc(X0)
% 3.21/0.98      | sK4 != X0 ),
% 3.21/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_27]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_367,plain,
% 3.21/0.98      ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4)
% 3.21/0.98      | v4_pre_topc(sK5,sK4)
% 3.21/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 3.21/0.98      | m1_subset_1(sK1(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.21/0.98      | ~ l1_pre_topc(sK4) ),
% 3.21/0.98      inference(unflattening,[status(thm)],[c_366]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_371,plain,
% 3.21/0.98      ( m1_subset_1(sK1(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.21/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 3.21/0.98      | v4_pre_topc(sK5,sK4)
% 3.21/0.98      | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4) ),
% 3.21/0.98      inference(global_propositional_subsumption,
% 3.21/0.98                [status(thm)],
% 3.21/0.98                [c_367,c_29]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_372,plain,
% 3.21/0.98      ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4)
% 3.21/0.98      | v4_pre_topc(sK5,sK4)
% 3.21/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 3.21/0.98      | m1_subset_1(sK1(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 3.21/0.98      inference(renaming,[status(thm)],[c_371]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_1782,plain,
% 3.21/0.98      ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)),sK4)
% 3.21/0.98      | v4_pre_topc(sK5,sK4)
% 3.21/0.98      | ~ m1_subset_1(sK3(sK4,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 3.21/0.98      | m1_subset_1(sK1(sK4,sK3(sK4,X0)),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 3.21/0.98      inference(instantiation,[status(thm)],[c_372]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_1784,plain,
% 3.21/0.98      ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),sK3(sK4,sK5)),sK4)
% 3.21/0.98      | v4_pre_topc(sK5,sK4)
% 3.21/0.98      | ~ m1_subset_1(sK3(sK4,sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 3.21/0.98      | m1_subset_1(sK1(sK4,sK3(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 3.21/0.98      inference(instantiation,[status(thm)],[c_1782]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_446,plain,
% 3.21/0.98      ( v4_pre_topc(sK5,sK4)
% 3.21/0.98      | m1_subset_1(sK3(sK4,sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 3.21/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 3.21/0.98      inference(instantiation,[status(thm)],[c_444]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_97,plain,
% 3.21/0.98      ( ~ r1_tarski(sK5,sK5) | sK5 = sK5 ),
% 3.21/0.98      inference(instantiation,[status(thm)],[c_0]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(contradiction,plain,
% 3.21/0.98      ( $false ),
% 3.21/0.98      inference(minisat,
% 3.21/0.98                [status(thm)],
% 3.21/0.98                [c_6048,c_3668,c_2999,c_2793,c_2434,c_2313,c_2311,c_2083,
% 3.21/0.98                 c_1784,c_446,c_97,c_93,c_36,c_22,c_28]) ).
% 3.21/0.98  
% 3.21/0.98  
% 3.21/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.21/0.98  
% 3.21/0.98  ------                               Statistics
% 3.21/0.98  
% 3.21/0.98  ------ General
% 3.21/0.98  
% 3.21/0.98  abstr_ref_over_cycles:                  0
% 3.21/0.98  abstr_ref_under_cycles:                 0
% 3.21/0.98  gc_basic_clause_elim:                   0
% 3.21/0.98  forced_gc_time:                         0
% 3.21/0.98  parsing_time:                           0.007
% 3.21/0.98  unif_index_cands_time:                  0.
% 3.21/0.98  unif_index_add_time:                    0.
% 3.21/0.98  orderings_time:                         0.
% 3.21/0.98  out_proof_time:                         0.011
% 3.21/0.98  total_time:                             0.203
% 3.21/0.98  num_of_symbols:                         47
% 3.21/0.98  num_of_terms:                           6180
% 3.21/0.98  
% 3.21/0.98  ------ Preprocessing
% 3.21/0.98  
% 3.21/0.98  num_of_splits:                          0
% 3.21/0.98  num_of_split_atoms:                     0
% 3.21/0.98  num_of_reused_defs:                     0
% 3.21/0.98  num_eq_ax_congr_red:                    27
% 3.21/0.98  num_of_sem_filtered_clauses:            1
% 3.21/0.98  num_of_subtypes:                        0
% 3.21/0.98  monotx_restored_types:                  0
% 3.21/0.98  sat_num_of_epr_types:                   0
% 3.21/0.98  sat_num_of_non_cyclic_types:            0
% 3.21/0.98  sat_guarded_non_collapsed_types:        0
% 3.21/0.98  num_pure_diseq_elim:                    0
% 3.21/0.98  simp_replaced_by:                       0
% 3.21/0.98  res_preprocessed:                       125
% 3.21/0.98  prep_upred:                             0
% 3.21/0.98  prep_unflattend:                        15
% 3.21/0.98  smt_new_axioms:                         0
% 3.21/0.98  pred_elim_cands:                        4
% 3.21/0.98  pred_elim:                              2
% 3.21/0.98  pred_elim_cl:                           2
% 3.21/0.98  pred_elim_cycles:                       4
% 3.21/0.98  merged_defs:                            8
% 3.21/0.98  merged_defs_ncl:                        0
% 3.21/0.98  bin_hyper_res:                          9
% 3.21/0.98  prep_cycles:                            4
% 3.21/0.98  pred_elim_time:                         0.007
% 3.21/0.98  splitting_time:                         0.
% 3.21/0.98  sem_filter_time:                        0.
% 3.21/0.98  monotx_time:                            0.
% 3.21/0.98  subtype_inf_time:                       0.
% 3.21/0.98  
% 3.21/0.98  ------ Problem properties
% 3.21/0.98  
% 3.21/0.98  clauses:                                24
% 3.21/0.98  conjectures:                            3
% 3.21/0.98  epr:                                    2
% 3.21/0.98  horn:                                   10
% 3.21/0.98  ground:                                 3
% 3.21/0.98  unary:                                  2
% 3.21/0.98  binary:                                 4
% 3.21/0.98  lits:                                   85
% 3.21/0.98  lits_eq:                                4
% 3.21/0.98  fd_pure:                                0
% 3.21/0.98  fd_pseudo:                              0
% 3.21/0.98  fd_cond:                                0
% 3.21/0.98  fd_pseudo_cond:                         1
% 3.21/0.98  ac_symbols:                             0
% 3.21/0.98  
% 3.21/0.98  ------ Propositional Solver
% 3.21/0.98  
% 3.21/0.98  prop_solver_calls:                      31
% 3.21/0.98  prop_fast_solver_calls:                 1321
% 3.21/0.98  smt_solver_calls:                       0
% 3.21/0.98  smt_fast_solver_calls:                  0
% 3.21/0.98  prop_num_of_clauses:                    2424
% 3.21/0.98  prop_preprocess_simplified:             6727
% 3.21/0.98  prop_fo_subsumed:                       23
% 3.21/0.98  prop_solver_time:                       0.
% 3.21/0.98  smt_solver_time:                        0.
% 3.21/0.98  smt_fast_solver_time:                   0.
% 3.21/0.98  prop_fast_solver_time:                  0.
% 3.21/0.98  prop_unsat_core_time:                   0.
% 3.21/0.98  
% 3.21/0.98  ------ QBF
% 3.21/0.98  
% 3.21/0.98  qbf_q_res:                              0
% 3.21/0.98  qbf_num_tautologies:                    0
% 3.21/0.98  qbf_prep_cycles:                        0
% 3.21/0.98  
% 3.21/0.98  ------ BMC1
% 3.21/0.98  
% 3.21/0.98  bmc1_current_bound:                     -1
% 3.21/0.98  bmc1_last_solved_bound:                 -1
% 3.21/0.98  bmc1_unsat_core_size:                   -1
% 3.21/0.98  bmc1_unsat_core_parents_size:           -1
% 3.21/0.98  bmc1_merge_next_fun:                    0
% 3.21/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.21/0.98  
% 3.21/0.98  ------ Instantiation
% 3.21/0.98  
% 3.21/0.98  inst_num_of_clauses:                    624
% 3.21/0.98  inst_num_in_passive:                    129
% 3.21/0.98  inst_num_in_active:                     392
% 3.21/0.98  inst_num_in_unprocessed:                102
% 3.21/0.98  inst_num_of_loops:                      472
% 3.21/0.98  inst_num_of_learning_restarts:          0
% 3.21/0.98  inst_num_moves_active_passive:          74
% 3.21/0.98  inst_lit_activity:                      0
% 3.21/0.98  inst_lit_activity_moves:                0
% 3.21/0.98  inst_num_tautologies:                   0
% 3.21/0.98  inst_num_prop_implied:                  0
% 3.21/0.98  inst_num_existing_simplified:           0
% 3.21/0.98  inst_num_eq_res_simplified:             0
% 3.21/0.98  inst_num_child_elim:                    0
% 3.21/0.98  inst_num_of_dismatching_blockings:      197
% 3.21/0.98  inst_num_of_non_proper_insts:           874
% 3.21/0.98  inst_num_of_duplicates:                 0
% 3.21/0.98  inst_inst_num_from_inst_to_res:         0
% 3.21/0.98  inst_dismatching_checking_time:         0.
% 3.21/0.98  
% 3.21/0.98  ------ Resolution
% 3.21/0.98  
% 3.21/0.98  res_num_of_clauses:                     0
% 3.21/0.98  res_num_in_passive:                     0
% 3.21/0.98  res_num_in_active:                      0
% 3.21/0.98  res_num_of_loops:                       129
% 3.21/0.98  res_forward_subset_subsumed:            52
% 3.21/0.98  res_backward_subset_subsumed:           0
% 3.21/0.98  res_forward_subsumed:                   0
% 3.21/0.98  res_backward_subsumed:                  0
% 3.21/0.98  res_forward_subsumption_resolution:     0
% 3.21/0.98  res_backward_subsumption_resolution:    0
% 3.21/0.98  res_clause_to_clause_subsumption:       1482
% 3.21/0.98  res_orphan_elimination:                 0
% 3.21/0.98  res_tautology_del:                      133
% 3.21/0.98  res_num_eq_res_simplified:              0
% 3.21/0.98  res_num_sel_changes:                    0
% 3.21/0.98  res_moves_from_active_to_pass:          0
% 3.21/0.98  
% 3.21/0.98  ------ Superposition
% 3.21/0.98  
% 3.21/0.98  sup_time_total:                         0.
% 3.21/0.98  sup_time_generating:                    0.
% 3.21/0.98  sup_time_sim_full:                      0.
% 3.21/0.98  sup_time_sim_immed:                     0.
% 3.21/0.98  
% 3.21/0.98  sup_num_of_clauses:                     200
% 3.21/0.98  sup_num_in_active:                      88
% 3.21/0.98  sup_num_in_passive:                     112
% 3.21/0.98  sup_num_of_loops:                       94
% 3.21/0.98  sup_fw_superposition:                   206
% 3.21/0.98  sup_bw_superposition:                   27
% 3.21/0.98  sup_immediate_simplified:               45
% 3.21/0.98  sup_given_eliminated:                   0
% 3.21/0.98  comparisons_done:                       0
% 3.21/0.98  comparisons_avoided:                    0
% 3.21/0.98  
% 3.21/0.98  ------ Simplifications
% 3.21/0.98  
% 3.21/0.98  
% 3.21/0.98  sim_fw_subset_subsumed:                 6
% 3.21/0.98  sim_bw_subset_subsumed:                 6
% 3.21/0.98  sim_fw_subsumed:                        12
% 3.21/0.98  sim_bw_subsumed:                        0
% 3.21/0.98  sim_fw_subsumption_res:                 0
% 3.21/0.98  sim_bw_subsumption_res:                 0
% 3.21/0.98  sim_tautology_del:                      4
% 3.21/0.98  sim_eq_tautology_del:                   25
% 3.21/0.98  sim_eq_res_simp:                        1
% 3.21/0.98  sim_fw_demodulated:                     0
% 3.21/0.98  sim_bw_demodulated:                     4
% 3.21/0.98  sim_light_normalised:                   34
% 3.21/0.98  sim_joinable_taut:                      0
% 3.21/0.98  sim_joinable_simp:                      0
% 3.21/0.98  sim_ac_normalised:                      0
% 3.21/0.98  sim_smt_subsumption:                    0
% 3.21/0.98  
%------------------------------------------------------------------------------
