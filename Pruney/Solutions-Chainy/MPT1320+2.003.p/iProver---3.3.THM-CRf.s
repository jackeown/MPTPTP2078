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
% DateTime   : Thu Dec  3 12:16:50 EST 2020

% Result     : Theorem 27.98s
% Output     : CNFRefutation 27.98s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 277 expanded)
%              Number of clauses        :   62 (  93 expanded)
%              Number of leaves         :   17 (  79 expanded)
%              Depth                    :   19
%              Number of atoms          :  464 (1273 expanded)
%              Number of equality atoms :  130 ( 161 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f22,plain,(
    ! [X3,X2,X0,X1] :
      ( ( k1_tops_2(X0,X1,X2) = X3
      <=> sP0(X1,X0,X2,X3) )
      | ~ sP1(X3,X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f27,plain,(
    ! [X3,X2,X0,X1] :
      ( ( ( k1_tops_2(X0,X1,X2) = X3
          | ~ sP0(X1,X0,X2,X3) )
        & ( sP0(X1,X0,X2,X3)
          | k1_tops_2(X0,X1,X2) != X3 ) )
      | ~ sP1(X3,X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_tops_2(X2,X3,X1) = X0
          | ~ sP0(X3,X2,X1,X0) )
        & ( sP0(X3,X2,X1,X0)
          | k1_tops_2(X2,X3,X1) != X0 ) )
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f27])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X3,X2,X1,X0)
      | k1_tops_2(X2,X3,X1) != X0
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f71,plain,(
    ! [X2,X3,X1] :
      ( sP0(X3,X2,X1,k1_tops_2(X2,X3,X1))
      | ~ sP1(k1_tops_2(X2,X3,X1),X1,X2,X3) ) ),
    inference(equality_resolution,[],[f50])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
                 => ( k1_tops_2(X0,X1,X2) = X3
                  <=> ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
                       => ( r2_hidden(X4,X3)
                        <=> ? [X5] :
                              ( k9_subset_1(u1_struct_0(X0),X5,X1) = X4
                              & r2_hidden(X5,X2)
                              & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tops_2(X0,X1,X2) = X3
                  <=> ! [X4] :
                        ( ( r2_hidden(X4,X3)
                        <=> ? [X5] :
                              ( k9_subset_1(u1_struct_0(X0),X5,X1) = X4
                              & r2_hidden(X5,X2)
                              & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) ) )
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X1,X0,X2,X3] :
      ( sP0(X1,X0,X2,X3)
    <=> ! [X4] :
          ( ( r2_hidden(X4,X3)
          <=> ? [X5] :
                ( k9_subset_1(u1_struct_0(X0),X5,X1) = X4
                & r2_hidden(X5,X2)
                & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( sP1(X3,X2,X0,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f16,f22,f21])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X3,X2,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                 => ( r2_hidden(X1,X3)
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                   => ( r2_hidden(X1,X3)
                     => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3))
                  & r2_hidden(X1,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3))
                  & r2_hidden(X1,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3))
          & r2_hidden(X1,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,sK8))
        & r2_hidden(X1,sK8)
        & m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3))
              & r2_hidden(X1,X3)
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X3] :
            ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,sK7),k1_tops_2(X0,sK7,X3))
            & r2_hidden(X1,X3)
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3))
                  & r2_hidden(X1,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK6,X2),k1_tops_2(X0,X2,X3))
                & r2_hidden(sK6,X3)
                & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3))
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK5),X1,X2),k1_tops_2(sK5,X2,X3))
                  & r2_hidden(X1,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) )
      & l1_pre_topc(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK5),sK6,sK7),k1_tops_2(sK5,sK7,sK8))
    & r2_hidden(sK6,sK8)
    & m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))
    & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    & l1_pre_topc(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f20,f39,f38,f37,f36])).

fof(f63,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f64,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f40])).

fof(f65,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f40])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f29,plain,(
    ! [X1,X0,X2,X3] :
      ( ( sP0(X1,X0,X2,X3)
        | ? [X4] :
            ( ( ! [X5] :
                  ( k9_subset_1(u1_struct_0(X0),X5,X1) != X4
                  | ~ r2_hidden(X5,X2)
                  | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X4,X3) )
            & ( ? [X5] :
                  ( k9_subset_1(u1_struct_0(X0),X5,X1) = X4
                  & r2_hidden(X5,X2)
                  & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
              | r2_hidden(X4,X3) )
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) )
      & ( ! [X4] :
            ( ( ( r2_hidden(X4,X3)
                | ! [X5] :
                    ( k9_subset_1(u1_struct_0(X0),X5,X1) != X4
                    | ~ r2_hidden(X5,X2)
                    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & ( ? [X5] :
                    ( k9_subset_1(u1_struct_0(X0),X5,X1) = X4
                    & r2_hidden(X5,X2)
                    & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X4,X3) ) )
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) )
        | ~ sP0(X1,X0,X2,X3) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f30,plain,(
    ! [X1,X0,X2,X3] :
      ( ( sP0(X1,X0,X2,X3)
        | ? [X4] :
            ( ( ! [X5] :
                  ( k9_subset_1(u1_struct_0(X0),X5,X1) != X4
                  | ~ r2_hidden(X5,X2)
                  | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X4,X3) )
            & ( ? [X5] :
                  ( k9_subset_1(u1_struct_0(X0),X5,X1) = X4
                  & r2_hidden(X5,X2)
                  & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
              | r2_hidden(X4,X3) )
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) )
      & ( ! [X4] :
            ( ( ( r2_hidden(X4,X3)
                | ! [X5] :
                    ( k9_subset_1(u1_struct_0(X0),X5,X1) != X4
                    | ~ r2_hidden(X5,X2)
                    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & ( ? [X5] :
                    ( k9_subset_1(u1_struct_0(X0),X5,X1) = X4
                    & r2_hidden(X5,X2)
                    & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X4,X3) ) )
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) )
        | ~ sP0(X1,X0,X2,X3) ) ) ),
    inference(flattening,[],[f29])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ! [X5] :
                  ( k9_subset_1(u1_struct_0(X1),X5,X0) != X4
                  | ~ r2_hidden(X5,X2)
                  | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r2_hidden(X4,X3) )
            & ( ? [X6] :
                  ( k9_subset_1(u1_struct_0(X1),X6,X0) = X4
                  & r2_hidden(X6,X2)
                  & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) )
              | r2_hidden(X4,X3) )
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0)))) ) )
      & ( ! [X7] :
            ( ( ( r2_hidden(X7,X3)
                | ! [X8] :
                    ( k9_subset_1(u1_struct_0(X1),X8,X0) != X7
                    | ~ r2_hidden(X8,X2)
                    | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X1))) ) )
              & ( ? [X9] :
                    ( k9_subset_1(u1_struct_0(X1),X9,X0) = X7
                    & r2_hidden(X9,X2)
                    & m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X1))) )
                | ~ r2_hidden(X7,X3) ) )
            | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0)))) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f30])).

fof(f34,plain,(
    ! [X7,X2,X1,X0] :
      ( ? [X9] :
          ( k9_subset_1(u1_struct_0(X1),X9,X0) = X7
          & r2_hidden(X9,X2)
          & m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2,X7),X0) = X7
        & r2_hidden(sK4(X0,X1,X2,X7),X2)
        & m1_subset_1(sK4(X0,X1,X2,X7),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( k9_subset_1(u1_struct_0(X1),X6,X0) = X4
          & r2_hidden(X6,X2)
          & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X1),sK3(X0,X1,X2,X3),X0) = X4
        & r2_hidden(sK3(X0,X1,X2,X3),X2)
        & m1_subset_1(sK3(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( k9_subset_1(u1_struct_0(X1),X5,X0) != X4
                | ~ r2_hidden(X5,X2)
                | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r2_hidden(X4,X3) )
          & ( ? [X6] :
                ( k9_subset_1(u1_struct_0(X1),X6,X0) = X4
                & r2_hidden(X6,X2)
                & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) )
            | r2_hidden(X4,X3) )
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0)))) )
     => ( ( ! [X5] :
              ( k9_subset_1(u1_struct_0(X1),X5,X0) != sK2(X0,X1,X2,X3)
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
        & ( ? [X6] :
              ( k9_subset_1(u1_struct_0(X1),X6,X0) = sK2(X0,X1,X2,X3)
              & r2_hidden(X6,X2)
              & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) )
          | r2_hidden(sK2(X0,X1,X2,X3),X3) )
        & m1_subset_1(sK2(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ! [X5] :
                ( k9_subset_1(u1_struct_0(X1),X5,X0) != sK2(X0,X1,X2,X3)
                | ~ r2_hidden(X5,X2)
                | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
          & ( ( k9_subset_1(u1_struct_0(X1),sK3(X0,X1,X2,X3),X0) = sK2(X0,X1,X2,X3)
              & r2_hidden(sK3(X0,X1,X2,X3),X2)
              & m1_subset_1(sK3(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1))) )
            | r2_hidden(sK2(X0,X1,X2,X3),X3) )
          & m1_subset_1(sK2(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0)))) ) )
      & ( ! [X7] :
            ( ( ( r2_hidden(X7,X3)
                | ! [X8] :
                    ( k9_subset_1(u1_struct_0(X1),X8,X0) != X7
                    | ~ r2_hidden(X8,X2)
                    | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X1))) ) )
              & ( ( k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2,X7),X0) = X7
                  & r2_hidden(sK4(X0,X1,X2,X7),X2)
                  & m1_subset_1(sK4(X0,X1,X2,X7),k1_zfmisc_1(u1_struct_0(X1))) )
                | ~ r2_hidden(X7,X3) ) )
            | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0)))) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f31,f34,f33,f32])).

fof(f55,plain,(
    ! [X2,X0,X8,X7,X3,X1] :
      ( r2_hidden(X7,X3)
      | k9_subset_1(u1_struct_0(X1),X8,X0) != X7
      | ~ r2_hidden(X8,X2)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0))))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f72,plain,(
    ! [X2,X0,X8,X3,X1] :
      ( r2_hidden(k9_subset_1(u1_struct_0(X1),X8,X0),X3)
      | ~ r2_hidden(X8,X2)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X8,X0),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0))))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(equality_resolution,[],[f55])).

fof(f68,plain,(
    ~ r2_hidden(k9_subset_1(u1_struct_0(sK5),sK6,sK7),k1_tops_2(sK5,sK7,sK8)) ),
    inference(cnf_transformation,[],[f40])).

fof(f66,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f40])).

fof(f67,plain,(
    r2_hidden(sK6,sK8) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_43556,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_5,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_217,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_218,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_217])).

cnf(c_271,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_218])).

cnf(c_43537,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_271])).

cnf(c_45104,plain,
    ( k9_subset_1(X0,X1,X0) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_43556,c_43537])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_270,plain,
    ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
    | ~ r1_tarski(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_3,c_218])).

cnf(c_43538,plain,
    ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_270])).

cnf(c_45549,plain,
    ( m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X1,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_45104,c_43538])).

cnf(c_131514,plain,
    ( m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X1)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_45549,c_43556])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_43554,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_131518,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_131514,c_43554])).

cnf(c_10,plain,
    ( ~ sP1(k1_tops_2(X0,X1,X2),X2,X0,X1)
    | sP0(X1,X0,X2,k1_tops_2(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_20,plain,
    ( sP1(X0,X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X3)))))
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_398,plain,
    ( sP1(X0,X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X3)))))
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_27])).

cnf(c_399,plain,
    ( sP1(X0,X1,sK5,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK5,X2)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) ),
    inference(unflattening,[status(thm)],[c_398])).

cnf(c_449,plain,
    ( sP0(X0,X1,X2,k1_tops_2(X1,X0,X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK5,X3)))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | X3 != X0
    | X5 != X2
    | k1_tops_2(X1,X0,X2) != X4
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_399])).

cnf(c_450,plain,
    ( sP0(X0,sK5,X1,k1_tops_2(sK5,X0,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ m1_subset_1(k1_tops_2(sK5,X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK5,X0))))) ),
    inference(unflattening,[status(thm)],[c_449])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | m1_subset_1(k1_tops_2(X1,X0,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0)))))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_371,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | m1_subset_1(k1_tops_2(X1,X0,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0)))))
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_27])).

cnf(c_372,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | m1_subset_1(k1_tops_2(sK5,X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK5,X0))))) ),
    inference(unflattening,[status(thm)],[c_371])).

cnf(c_454,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | sP0(X0,sK5,X1,k1_tops_2(sK5,X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_450,c_372])).

cnf(c_455,plain,
    ( sP0(X0,sK5,X1,k1_tops_2(sK5,X0,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) ),
    inference(renaming,[status(thm)],[c_454])).

cnf(c_43531,plain,
    ( sP0(X0,sK5,X1,k1_tops_2(sK5,X0,X1)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_455])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_43539,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_43540,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_386,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | u1_struct_0(k1_pre_topc(X1,X0)) = X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_27])).

cnf(c_387,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | u1_struct_0(k1_pre_topc(sK5,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_386])).

cnf(c_43533,plain,
    ( u1_struct_0(k1_pre_topc(sK5,X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_387])).

cnf(c_43769,plain,
    ( u1_struct_0(k1_pre_topc(sK5,sK7)) = sK7 ),
    inference(superposition,[status(thm)],[c_43540,c_43533])).

cnf(c_43555,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_16,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ r2_hidden(X4,X2)
    | r2_hidden(k9_subset_1(u1_struct_0(X1),X4,X0),X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X4,X0),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0)))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_43547,plain,
    ( sP0(X0,X1,X2,X3) != iProver_top
    | r2_hidden(X4,X2) != iProver_top
    | r2_hidden(k9_subset_1(u1_struct_0(X1),X4,X0),X3) = iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k9_subset_1(u1_struct_0(X1),X4,X0),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_44894,plain,
    ( sP0(X0,X1,X2,X3) != iProver_top
    | r2_hidden(X4,X2) != iProver_top
    | r2_hidden(k9_subset_1(u1_struct_0(X1),X4,X0),X3) = iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k9_subset_1(u1_struct_0(X1),X4,X0),u1_struct_0(k1_pre_topc(X1,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_43555,c_43547])).

cnf(c_87195,plain,
    ( sP0(sK7,sK5,X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(k9_subset_1(u1_struct_0(sK5),X2,sK7),X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r1_tarski(k9_subset_1(u1_struct_0(sK5),X2,sK7),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_43769,c_44894])).

cnf(c_43843,plain,
    ( r1_tarski(sK7,u1_struct_0(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_43540,c_43554])).

cnf(c_45106,plain,
    ( k9_subset_1(u1_struct_0(sK5),X0,sK7) = k3_xboole_0(X0,sK7) ),
    inference(superposition,[status(thm)],[c_43843,c_43537])).

cnf(c_87247,plain,
    ( sP0(sK7,sK5,X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(k3_xboole_0(X2,sK7),X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r1_tarski(k3_xboole_0(X2,sK7),sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_87195,c_45106])).

cnf(c_103275,plain,
    ( sP0(sK7,sK5,X0,X1) != iProver_top
    | r2_hidden(k3_xboole_0(sK6,sK7),X1) = iProver_top
    | r2_hidden(sK6,X0) != iProver_top
    | r1_tarski(k3_xboole_0(sK6,sK7),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_43539,c_87247])).

cnf(c_103834,plain,
    ( r2_hidden(k3_xboole_0(sK6,sK7),k1_tops_2(sK5,sK7,X0)) = iProver_top
    | r2_hidden(sK6,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r1_tarski(k3_xboole_0(sK6,sK7),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_43531,c_103275])).

cnf(c_30,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_104649,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top
    | r2_hidden(sK6,X0) != iProver_top
    | r2_hidden(k3_xboole_0(sK6,sK7),k1_tops_2(sK5,sK7,X0)) = iProver_top
    | r1_tarski(k3_xboole_0(sK6,sK7),sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_103834,c_30])).

cnf(c_104650,plain,
    ( r2_hidden(k3_xboole_0(sK6,sK7),k1_tops_2(sK5,sK7,X0)) = iProver_top
    | r2_hidden(sK6,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top
    | r1_tarski(k3_xboole_0(sK6,sK7),sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_104649])).

cnf(c_22,negated_conjecture,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK5),sK6,sK7),k1_tops_2(sK5,sK7,sK8)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_43543,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(sK5),sK6,sK7),k1_tops_2(sK5,sK7,sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_45193,plain,
    ( r2_hidden(k3_xboole_0(sK6,sK7),k1_tops_2(sK5,sK7,sK8)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_45106,c_43543])).

cnf(c_104666,plain,
    ( r2_hidden(sK6,sK8) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top
    | r1_tarski(k3_xboole_0(sK6,sK7),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_104650,c_45193])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_31,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( r2_hidden(sK6,sK8) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_32,plain,
    ( r2_hidden(sK6,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_104781,plain,
    ( r1_tarski(k3_xboole_0(sK6,sK7),sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_104666,c_31,c_32])).

cnf(c_131878,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_131518,c_104781])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:29:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 27.98/4.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.98/4.00  
% 27.98/4.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.98/4.00  
% 27.98/4.00  ------  iProver source info
% 27.98/4.00  
% 27.98/4.00  git: date: 2020-06-30 10:37:57 +0100
% 27.98/4.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.98/4.00  git: non_committed_changes: false
% 27.98/4.00  git: last_make_outside_of_git: false
% 27.98/4.00  
% 27.98/4.00  ------ 
% 27.98/4.00  ------ Parsing...
% 27.98/4.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.98/4.00  
% 27.98/4.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 27.98/4.00  
% 27.98/4.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.98/4.00  
% 27.98/4.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.98/4.00  ------ Proving...
% 27.98/4.00  ------ Problem Properties 
% 27.98/4.00  
% 27.98/4.00  
% 27.98/4.00  clauses                                 25
% 27.98/4.00  conjectures                             5
% 27.98/4.00  EPR                                     3
% 27.98/4.00  Horn                                    21
% 27.98/4.00  unary                                   6
% 27.98/4.00  binary                                  6
% 27.98/4.00  lits                                    66
% 27.98/4.00  lits eq                                 7
% 27.98/4.00  fd_pure                                 0
% 27.98/4.00  fd_pseudo                               0
% 27.98/4.00  fd_cond                                 0
% 27.98/4.00  fd_pseudo_cond                          2
% 27.98/4.00  AC symbols                              0
% 27.98/4.00  
% 27.98/4.00  ------ Input Options Time Limit: Unbounded
% 27.98/4.00  
% 27.98/4.00  
% 27.98/4.00  
% 27.98/4.00  
% 27.98/4.00  ------ Preprocessing...
% 27.98/4.00  
% 27.98/4.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 27.98/4.00  Current options:
% 27.98/4.00  ------ 
% 27.98/4.00  
% 27.98/4.00  
% 27.98/4.00  
% 27.98/4.00  
% 27.98/4.00  ------ Proving...
% 27.98/4.00  
% 27.98/4.00  
% 27.98/4.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.98/4.00  
% 27.98/4.00  ------ Proving...
% 27.98/4.00  
% 27.98/4.00  
% 27.98/4.00  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.98/4.00  
% 27.98/4.00  ------ Proving...
% 27.98/4.00  
% 27.98/4.00  
% 27.98/4.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 27.98/4.00  
% 27.98/4.00  ------ Proving...
% 27.98/4.00  
% 27.98/4.00  
% 27.98/4.00  ------ Preprocessing...
% 27.98/4.00  
% 27.98/4.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.98/4.00  
% 27.98/4.00  ------ Proving...
% 27.98/4.00  
% 27.98/4.00  
% 27.98/4.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.98/4.00  
% 27.98/4.00  ------ Proving...
% 27.98/4.00  
% 27.98/4.00  
% 27.98/4.00  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.98/4.00  
% 27.98/4.00  ------ Proving...
% 27.98/4.00  
% 27.98/4.00  
% 27.98/4.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.98/4.00  
% 27.98/4.00  ------ Proving...
% 27.98/4.00  
% 27.98/4.00  
% 27.98/4.00  ------ Preprocessing...
% 27.98/4.00  
% 27.98/4.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.98/4.00  
% 27.98/4.00  ------ Proving...
% 27.98/4.00  
% 27.98/4.00  
% 27.98/4.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.98/4.00  
% 27.98/4.00  ------ Proving...
% 27.98/4.00  
% 27.98/4.00  
% 27.98/4.00  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.98/4.00  
% 27.98/4.00  ------ Proving...
% 27.98/4.00  
% 27.98/4.00  
% 27.98/4.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.98/4.00  
% 27.98/4.00  ------ Proving...
% 27.98/4.00  
% 27.98/4.00  
% 27.98/4.00  ------ Preprocessing...
% 27.98/4.00  
% 27.98/4.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.98/4.00  
% 27.98/4.00  ------ Proving...
% 27.98/4.00  
% 27.98/4.00  
% 27.98/4.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.98/4.00  
% 27.98/4.00  ------ Proving...
% 27.98/4.00  
% 27.98/4.00  
% 27.98/4.00  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.98/4.00  
% 27.98/4.00  ------ Proving...
% 27.98/4.00  
% 27.98/4.00  
% 27.98/4.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.98/4.00  
% 27.98/4.00  ------ Proving...
% 27.98/4.00  
% 27.98/4.00  
% 27.98/4.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 27.98/4.00  
% 27.98/4.00  ------ Proving...
% 27.98/4.00  
% 27.98/4.00  
% 27.98/4.00  % SZS status Theorem for theBenchmark.p
% 27.98/4.00  
% 27.98/4.00   Resolution empty clause
% 27.98/4.00  
% 27.98/4.00  % SZS output start CNFRefutation for theBenchmark.p
% 27.98/4.00  
% 27.98/4.00  fof(f1,axiom,(
% 27.98/4.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 27.98/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.98/4.00  
% 27.98/4.00  fof(f24,plain,(
% 27.98/4.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 27.98/4.00    inference(nnf_transformation,[],[f1])).
% 27.98/4.00  
% 27.98/4.00  fof(f25,plain,(
% 27.98/4.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 27.98/4.00    inference(flattening,[],[f24])).
% 27.98/4.00  
% 27.98/4.00  fof(f41,plain,(
% 27.98/4.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 27.98/4.00    inference(cnf_transformation,[],[f25])).
% 27.98/4.00  
% 27.98/4.00  fof(f70,plain,(
% 27.98/4.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 27.98/4.00    inference(equality_resolution,[],[f41])).
% 27.98/4.00  
% 27.98/4.00  fof(f3,axiom,(
% 27.98/4.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 27.98/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.98/4.00  
% 27.98/4.00  fof(f12,plain,(
% 27.98/4.00    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 27.98/4.00    inference(ennf_transformation,[],[f3])).
% 27.98/4.00  
% 27.98/4.00  fof(f45,plain,(
% 27.98/4.00    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 27.98/4.00    inference(cnf_transformation,[],[f12])).
% 27.98/4.00  
% 27.98/4.00  fof(f4,axiom,(
% 27.98/4.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 27.98/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.98/4.00  
% 27.98/4.00  fof(f26,plain,(
% 27.98/4.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 27.98/4.00    inference(nnf_transformation,[],[f4])).
% 27.98/4.00  
% 27.98/4.00  fof(f47,plain,(
% 27.98/4.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 27.98/4.00    inference(cnf_transformation,[],[f26])).
% 27.98/4.00  
% 27.98/4.00  fof(f2,axiom,(
% 27.98/4.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 27.98/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.98/4.00  
% 27.98/4.00  fof(f11,plain,(
% 27.98/4.00    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 27.98/4.00    inference(ennf_transformation,[],[f2])).
% 27.98/4.00  
% 27.98/4.00  fof(f44,plain,(
% 27.98/4.00    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 27.98/4.00    inference(cnf_transformation,[],[f11])).
% 27.98/4.00  
% 27.98/4.00  fof(f46,plain,(
% 27.98/4.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 27.98/4.00    inference(cnf_transformation,[],[f26])).
% 27.98/4.00  
% 27.98/4.00  fof(f22,plain,(
% 27.98/4.00    ! [X3,X2,X0,X1] : ((k1_tops_2(X0,X1,X2) = X3 <=> sP0(X1,X0,X2,X3)) | ~sP1(X3,X2,X0,X1))),
% 27.98/4.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 27.98/4.00  
% 27.98/4.00  fof(f27,plain,(
% 27.98/4.00    ! [X3,X2,X0,X1] : (((k1_tops_2(X0,X1,X2) = X3 | ~sP0(X1,X0,X2,X3)) & (sP0(X1,X0,X2,X3) | k1_tops_2(X0,X1,X2) != X3)) | ~sP1(X3,X2,X0,X1))),
% 27.98/4.00    inference(nnf_transformation,[],[f22])).
% 27.98/4.00  
% 27.98/4.00  fof(f28,plain,(
% 27.98/4.00    ! [X0,X1,X2,X3] : (((k1_tops_2(X2,X3,X1) = X0 | ~sP0(X3,X2,X1,X0)) & (sP0(X3,X2,X1,X0) | k1_tops_2(X2,X3,X1) != X0)) | ~sP1(X0,X1,X2,X3))),
% 27.98/4.00    inference(rectify,[],[f27])).
% 27.98/4.00  
% 27.98/4.00  fof(f50,plain,(
% 27.98/4.00    ( ! [X2,X0,X3,X1] : (sP0(X3,X2,X1,X0) | k1_tops_2(X2,X3,X1) != X0 | ~sP1(X0,X1,X2,X3)) )),
% 27.98/4.00    inference(cnf_transformation,[],[f28])).
% 27.98/4.00  
% 27.98/4.00  fof(f71,plain,(
% 27.98/4.00    ( ! [X2,X3,X1] : (sP0(X3,X2,X1,k1_tops_2(X2,X3,X1)) | ~sP1(k1_tops_2(X2,X3,X1),X1,X2,X3)) )),
% 27.98/4.00    inference(equality_resolution,[],[f50])).
% 27.98/4.00  
% 27.98/4.00  fof(f7,axiom,(
% 27.98/4.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) => (k1_tops_2(X0,X1,X2) = X3 <=> ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) => (r2_hidden(X4,X3) <=> ? [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) = X4 & r2_hidden(X5,X2) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))))))))))),
% 27.98/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.98/4.00  
% 27.98/4.00  fof(f16,plain,(
% 27.98/4.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tops_2(X0,X1,X2) = X3 <=> ! [X4] : ((r2_hidden(X4,X3) <=> ? [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) = X4 & r2_hidden(X5,X2) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.98/4.00    inference(ennf_transformation,[],[f7])).
% 27.98/4.00  
% 27.98/4.00  fof(f21,plain,(
% 27.98/4.00    ! [X1,X0,X2,X3] : (sP0(X1,X0,X2,X3) <=> ! [X4] : ((r2_hidden(X4,X3) <=> ? [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) = X4 & r2_hidden(X5,X2) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))))),
% 27.98/4.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 27.98/4.00  
% 27.98/4.00  fof(f23,plain,(
% 27.98/4.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (sP1(X3,X2,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.98/4.00    inference(definition_folding,[],[f16,f22,f21])).
% 27.98/4.00  
% 27.98/4.00  fof(f61,plain,(
% 27.98/4.00    ( ! [X2,X0,X3,X1] : (sP1(X3,X2,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 27.98/4.00    inference(cnf_transformation,[],[f23])).
% 27.98/4.00  
% 27.98/4.00  fof(f9,conjecture,(
% 27.98/4.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,X3) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)))))))),
% 27.98/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.98/4.00  
% 27.98/4.00  fof(f10,negated_conjecture,(
% 27.98/4.00    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,X3) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)))))))),
% 27.98/4.00    inference(negated_conjecture,[],[f9])).
% 27.98/4.00  
% 27.98/4.00  fof(f19,plain,(
% 27.98/4.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)) & r2_hidden(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 27.98/4.00    inference(ennf_transformation,[],[f10])).
% 27.98/4.00  
% 27.98/4.00  fof(f20,plain,(
% 27.98/4.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 27.98/4.00    inference(flattening,[],[f19])).
% 27.98/4.00  
% 27.98/4.00  fof(f39,plain,(
% 27.98/4.00    ( ! [X2,X0,X1] : (? [X3] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,sK8)) & r2_hidden(X1,sK8) & m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 27.98/4.00    introduced(choice_axiom,[])).
% 27.98/4.00  
% 27.98/4.00  fof(f38,plain,(
% 27.98/4.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X3] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,sK7),k1_tops_2(X0,sK7,X3)) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 27.98/4.00    introduced(choice_axiom,[])).
% 27.98/4.00  
% 27.98/4.00  fof(f37,plain,(
% 27.98/4.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (? [X3] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),sK6,X2),k1_tops_2(X0,X2,X3)) & r2_hidden(sK6,X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 27.98/4.00    introduced(choice_axiom,[])).
% 27.98/4.00  
% 27.98/4.00  fof(f36,plain,(
% 27.98/4.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k9_subset_1(u1_struct_0(sK5),X1,X2),k1_tops_2(sK5,X2,X3)) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))) & l1_pre_topc(sK5))),
% 27.98/4.00    introduced(choice_axiom,[])).
% 27.98/4.00  
% 27.98/4.00  fof(f40,plain,(
% 27.98/4.00    (((~r2_hidden(k9_subset_1(u1_struct_0(sK5),sK6,sK7),k1_tops_2(sK5,sK7,sK8)) & r2_hidden(sK6,sK8) & m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))) & l1_pre_topc(sK5)),
% 27.98/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f20,f39,f38,f37,f36])).
% 27.98/4.00  
% 27.98/4.00  fof(f63,plain,(
% 27.98/4.00    l1_pre_topc(sK5)),
% 27.98/4.00    inference(cnf_transformation,[],[f40])).
% 27.98/4.00  
% 27.98/4.00  fof(f8,axiom,(
% 27.98/4.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))))),
% 27.98/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.98/4.00  
% 27.98/4.00  fof(f17,plain,(
% 27.98/4.00    ! [X0,X1,X2] : (m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 27.98/4.00    inference(ennf_transformation,[],[f8])).
% 27.98/4.00  
% 27.98/4.00  fof(f18,plain,(
% 27.98/4.00    ! [X0,X1,X2] : (m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 27.98/4.00    inference(flattening,[],[f17])).
% 27.98/4.00  
% 27.98/4.00  fof(f62,plain,(
% 27.98/4.00    ( ! [X2,X0,X1] : (m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 27.98/4.00    inference(cnf_transformation,[],[f18])).
% 27.98/4.00  
% 27.98/4.00  fof(f64,plain,(
% 27.98/4.00    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))),
% 27.98/4.00    inference(cnf_transformation,[],[f40])).
% 27.98/4.00  
% 27.98/4.00  fof(f65,plain,(
% 27.98/4.00    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))),
% 27.98/4.00    inference(cnf_transformation,[],[f40])).
% 27.98/4.00  
% 27.98/4.00  fof(f6,axiom,(
% 27.98/4.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 27.98/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.98/4.00  
% 27.98/4.00  fof(f15,plain,(
% 27.98/4.00    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.98/4.00    inference(ennf_transformation,[],[f6])).
% 27.98/4.00  
% 27.98/4.00  fof(f49,plain,(
% 27.98/4.00    ( ! [X0,X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 27.98/4.00    inference(cnf_transformation,[],[f15])).
% 27.98/4.00  
% 27.98/4.00  fof(f29,plain,(
% 27.98/4.00    ! [X1,X0,X2,X3] : ((sP0(X1,X0,X2,X3) | ? [X4] : (((! [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X3)) & (? [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) = X4 & r2_hidden(X5,X2) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))) & (! [X4] : (((r2_hidden(X4,X3) | ! [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) = X4 & r2_hidden(X5,X2) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | ~sP0(X1,X0,X2,X3)))),
% 27.98/4.00    inference(nnf_transformation,[],[f21])).
% 27.98/4.00  
% 27.98/4.00  fof(f30,plain,(
% 27.98/4.00    ! [X1,X0,X2,X3] : ((sP0(X1,X0,X2,X3) | ? [X4] : ((! [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X3)) & (? [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) = X4 & r2_hidden(X5,X2) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X4,X3)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))) & (! [X4] : (((r2_hidden(X4,X3) | ! [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) = X4 & r2_hidden(X5,X2) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | ~sP0(X1,X0,X2,X3)))),
% 27.98/4.00    inference(flattening,[],[f29])).
% 27.98/4.00  
% 27.98/4.00  fof(f31,plain,(
% 27.98/4.00    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : ((! [X5] : (k9_subset_1(u1_struct_0(X1),X5,X0) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X4,X3)) & (? [X6] : (k9_subset_1(u1_struct_0(X1),X6,X0) = X4 & r2_hidden(X6,X2) & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X4,X3)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0)))))) & (! [X7] : (((r2_hidden(X7,X3) | ! [X8] : (k9_subset_1(u1_struct_0(X1),X8,X0) != X7 | ~r2_hidden(X8,X2) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X1))))) & (? [X9] : (k9_subset_1(u1_struct_0(X1),X9,X0) = X7 & r2_hidden(X9,X2) & m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X7,X3))) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0))))) | ~sP0(X0,X1,X2,X3)))),
% 27.98/4.00    inference(rectify,[],[f30])).
% 27.98/4.00  
% 27.98/4.00  fof(f34,plain,(
% 27.98/4.00    ! [X7,X2,X1,X0] : (? [X9] : (k9_subset_1(u1_struct_0(X1),X9,X0) = X7 & r2_hidden(X9,X2) & m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2,X7),X0) = X7 & r2_hidden(sK4(X0,X1,X2,X7),X2) & m1_subset_1(sK4(X0,X1,X2,X7),k1_zfmisc_1(u1_struct_0(X1)))))),
% 27.98/4.00    introduced(choice_axiom,[])).
% 27.98/4.00  
% 27.98/4.00  fof(f33,plain,(
% 27.98/4.00    ( ! [X4] : (! [X3,X2,X1,X0] : (? [X6] : (k9_subset_1(u1_struct_0(X1),X6,X0) = X4 & r2_hidden(X6,X2) & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X1),sK3(X0,X1,X2,X3),X0) = X4 & r2_hidden(sK3(X0,X1,X2,X3),X2) & m1_subset_1(sK3(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))))) )),
% 27.98/4.00    introduced(choice_axiom,[])).
% 27.98/4.00  
% 27.98/4.00  fof(f32,plain,(
% 27.98/4.00    ! [X3,X2,X1,X0] : (? [X4] : ((! [X5] : (k9_subset_1(u1_struct_0(X1),X5,X0) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X4,X3)) & (? [X6] : (k9_subset_1(u1_struct_0(X1),X6,X0) = X4 & r2_hidden(X6,X2) & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X4,X3)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0))))) => ((! [X5] : (k9_subset_1(u1_struct_0(X1),X5,X0) != sK2(X0,X1,X2,X3) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (? [X6] : (k9_subset_1(u1_struct_0(X1),X6,X0) = sK2(X0,X1,X2,X3) & r2_hidden(X6,X2) & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1,X2,X3),X3)) & m1_subset_1(sK2(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0))))))),
% 27.98/4.00    introduced(choice_axiom,[])).
% 27.98/4.00  
% 27.98/4.00  fof(f35,plain,(
% 27.98/4.00    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ((! [X5] : (k9_subset_1(u1_struct_0(X1),X5,X0) != sK2(X0,X1,X2,X3) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & ((k9_subset_1(u1_struct_0(X1),sK3(X0,X1,X2,X3),X0) = sK2(X0,X1,X2,X3) & r2_hidden(sK3(X0,X1,X2,X3),X2) & m1_subset_1(sK3(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1,X2,X3),X3)) & m1_subset_1(sK2(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0)))))) & (! [X7] : (((r2_hidden(X7,X3) | ! [X8] : (k9_subset_1(u1_struct_0(X1),X8,X0) != X7 | ~r2_hidden(X8,X2) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X1))))) & ((k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2,X7),X0) = X7 & r2_hidden(sK4(X0,X1,X2,X7),X2) & m1_subset_1(sK4(X0,X1,X2,X7),k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X7,X3))) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0))))) | ~sP0(X0,X1,X2,X3)))),
% 27.98/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f31,f34,f33,f32])).
% 27.98/4.00  
% 27.98/4.00  fof(f55,plain,(
% 27.98/4.00    ( ! [X2,X0,X8,X7,X3,X1] : (r2_hidden(X7,X3) | k9_subset_1(u1_struct_0(X1),X8,X0) != X7 | ~r2_hidden(X8,X2) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0)))) | ~sP0(X0,X1,X2,X3)) )),
% 27.98/4.00    inference(cnf_transformation,[],[f35])).
% 27.98/4.00  
% 27.98/4.00  fof(f72,plain,(
% 27.98/4.00    ( ! [X2,X0,X8,X3,X1] : (r2_hidden(k9_subset_1(u1_struct_0(X1),X8,X0),X3) | ~r2_hidden(X8,X2) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(k9_subset_1(u1_struct_0(X1),X8,X0),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0)))) | ~sP0(X0,X1,X2,X3)) )),
% 27.98/4.00    inference(equality_resolution,[],[f55])).
% 27.98/4.00  
% 27.98/4.00  fof(f68,plain,(
% 27.98/4.00    ~r2_hidden(k9_subset_1(u1_struct_0(sK5),sK6,sK7),k1_tops_2(sK5,sK7,sK8))),
% 27.98/4.00    inference(cnf_transformation,[],[f40])).
% 27.98/4.00  
% 27.98/4.00  fof(f66,plain,(
% 27.98/4.00    m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))),
% 27.98/4.00    inference(cnf_transformation,[],[f40])).
% 27.98/4.00  
% 27.98/4.00  fof(f67,plain,(
% 27.98/4.00    r2_hidden(sK6,sK8)),
% 27.98/4.00    inference(cnf_transformation,[],[f40])).
% 27.98/4.00  
% 27.98/4.00  cnf(c_2,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f70]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_43556,plain,
% 27.98/4.00      ( r1_tarski(X0,X0) = iProver_top ),
% 27.98/4.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_4,plain,
% 27.98/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.98/4.00      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 27.98/4.00      inference(cnf_transformation,[],[f45]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_5,plain,
% 27.98/4.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 27.98/4.00      inference(cnf_transformation,[],[f47]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_217,plain,
% 27.98/4.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 27.98/4.00      inference(prop_impl,[status(thm)],[c_5]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_218,plain,
% 27.98/4.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 27.98/4.00      inference(renaming,[status(thm)],[c_217]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_271,plain,
% 27.98/4.00      ( ~ r1_tarski(X0,X1) | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 27.98/4.00      inference(bin_hyper_res,[status(thm)],[c_4,c_218]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_43537,plain,
% 27.98/4.00      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
% 27.98/4.00      | r1_tarski(X2,X0) != iProver_top ),
% 27.98/4.00      inference(predicate_to_equality,[status(thm)],[c_271]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_45104,plain,
% 27.98/4.00      ( k9_subset_1(X0,X1,X0) = k3_xboole_0(X1,X0) ),
% 27.98/4.00      inference(superposition,[status(thm)],[c_43556,c_43537]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_3,plain,
% 27.98/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.98/4.00      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 27.98/4.00      inference(cnf_transformation,[],[f44]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_270,plain,
% 27.98/4.00      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
% 27.98/4.00      | ~ r1_tarski(X2,X0) ),
% 27.98/4.00      inference(bin_hyper_res,[status(thm)],[c_3,c_218]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_43538,plain,
% 27.98/4.00      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
% 27.98/4.00      | r1_tarski(X2,X0) != iProver_top ),
% 27.98/4.00      inference(predicate_to_equality,[status(thm)],[c_270]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_45549,plain,
% 27.98/4.00      ( m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X1)) = iProver_top
% 27.98/4.00      | r1_tarski(X1,X1) != iProver_top ),
% 27.98/4.00      inference(superposition,[status(thm)],[c_45104,c_43538]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_131514,plain,
% 27.98/4.00      ( m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X1)) = iProver_top ),
% 27.98/4.00      inference(forward_subsumption_resolution,[status(thm)],[c_45549,c_43556]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_6,plain,
% 27.98/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 27.98/4.00      inference(cnf_transformation,[],[f46]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_43554,plain,
% 27.98/4.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 27.98/4.00      | r1_tarski(X0,X1) = iProver_top ),
% 27.98/4.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_131518,plain,
% 27.98/4.00      ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
% 27.98/4.00      inference(superposition,[status(thm)],[c_131514,c_43554]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_10,plain,
% 27.98/4.00      ( ~ sP1(k1_tops_2(X0,X1,X2),X2,X0,X1)
% 27.98/4.00      | sP0(X1,X0,X2,k1_tops_2(X0,X1,X2)) ),
% 27.98/4.00      inference(cnf_transformation,[],[f71]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_20,plain,
% 27.98/4.00      ( sP1(X0,X1,X2,X3)
% 27.98/4.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 27.98/4.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
% 27.98/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X3)))))
% 27.98/4.00      | ~ l1_pre_topc(X2) ),
% 27.98/4.00      inference(cnf_transformation,[],[f61]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_27,negated_conjecture,
% 27.98/4.00      ( l1_pre_topc(sK5) ),
% 27.98/4.00      inference(cnf_transformation,[],[f63]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_398,plain,
% 27.98/4.00      ( sP1(X0,X1,X2,X3)
% 27.98/4.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 27.98/4.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
% 27.98/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X3)))))
% 27.98/4.00      | sK5 != X2 ),
% 27.98/4.00      inference(resolution_lifted,[status(thm)],[c_20,c_27]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_399,plain,
% 27.98/4.00      ( sP1(X0,X1,sK5,X2)
% 27.98/4.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
% 27.98/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK5,X2)))))
% 27.98/4.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) ),
% 27.98/4.00      inference(unflattening,[status(thm)],[c_398]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_449,plain,
% 27.98/4.00      ( sP0(X0,X1,X2,k1_tops_2(X1,X0,X2))
% 27.98/4.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK5)))
% 27.98/4.00      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK5,X3)))))
% 27.98/4.00      | ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
% 27.98/4.00      | X3 != X0
% 27.98/4.00      | X5 != X2
% 27.98/4.00      | k1_tops_2(X1,X0,X2) != X4
% 27.98/4.00      | sK5 != X1 ),
% 27.98/4.00      inference(resolution_lifted,[status(thm)],[c_10,c_399]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_450,plain,
% 27.98/4.00      ( sP0(X0,sK5,X1,k1_tops_2(sK5,X0,X1))
% 27.98/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 27.98/4.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
% 27.98/4.00      | ~ m1_subset_1(k1_tops_2(sK5,X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK5,X0))))) ),
% 27.98/4.00      inference(unflattening,[status(thm)],[c_449]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_21,plain,
% 27.98/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.98/4.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 27.98/4.00      | m1_subset_1(k1_tops_2(X1,X0,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0)))))
% 27.98/4.00      | ~ l1_pre_topc(X1) ),
% 27.98/4.00      inference(cnf_transformation,[],[f62]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_371,plain,
% 27.98/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.98/4.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 27.98/4.00      | m1_subset_1(k1_tops_2(X1,X0,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0)))))
% 27.98/4.00      | sK5 != X1 ),
% 27.98/4.00      inference(resolution_lifted,[status(thm)],[c_21,c_27]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_372,plain,
% 27.98/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 27.98/4.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
% 27.98/4.00      | m1_subset_1(k1_tops_2(sK5,X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK5,X0))))) ),
% 27.98/4.00      inference(unflattening,[status(thm)],[c_371]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_454,plain,
% 27.98/4.00      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
% 27.98/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 27.98/4.00      | sP0(X0,sK5,X1,k1_tops_2(sK5,X0,X1)) ),
% 27.98/4.00      inference(global_propositional_subsumption,[status(thm)],[c_450,c_372]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_455,plain,
% 27.98/4.00      ( sP0(X0,sK5,X1,k1_tops_2(sK5,X0,X1))
% 27.98/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 27.98/4.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) ),
% 27.98/4.00      inference(renaming,[status(thm)],[c_454]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_43531,plain,
% 27.98/4.00      ( sP0(X0,sK5,X1,k1_tops_2(sK5,X0,X1)) = iProver_top
% 27.98/4.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 27.98/4.00      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top ),
% 27.98/4.00      inference(predicate_to_equality,[status(thm)],[c_455]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_26,negated_conjecture,
% 27.98/4.00      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 27.98/4.00      inference(cnf_transformation,[],[f64]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_43539,plain,
% 27.98/4.00      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
% 27.98/4.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_25,negated_conjecture,
% 27.98/4.00      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 27.98/4.00      inference(cnf_transformation,[],[f65]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_43540,plain,
% 27.98/4.00      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
% 27.98/4.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_8,plain,
% 27.98/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.98/4.00      | ~ l1_pre_topc(X1)
% 27.98/4.00      | u1_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 27.98/4.00      inference(cnf_transformation,[],[f49]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_386,plain,
% 27.98/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.98/4.00      | u1_struct_0(k1_pre_topc(X1,X0)) = X0
% 27.98/4.00      | sK5 != X1 ),
% 27.98/4.00      inference(resolution_lifted,[status(thm)],[c_8,c_27]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_387,plain,
% 27.98/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 27.98/4.00      | u1_struct_0(k1_pre_topc(sK5,X0)) = X0 ),
% 27.98/4.00      inference(unflattening,[status(thm)],[c_386]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_43533,plain,
% 27.98/4.00      ( u1_struct_0(k1_pre_topc(sK5,X0)) = X0
% 27.98/4.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
% 27.98/4.00      inference(predicate_to_equality,[status(thm)],[c_387]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_43769,plain,
% 27.98/4.00      ( u1_struct_0(k1_pre_topc(sK5,sK7)) = sK7 ),
% 27.98/4.00      inference(superposition,[status(thm)],[c_43540,c_43533]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_43555,plain,
% 27.98/4.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 27.98/4.00      | r1_tarski(X0,X1) != iProver_top ),
% 27.98/4.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_16,plain,
% 27.98/4.00      ( ~ sP0(X0,X1,X2,X3)
% 27.98/4.00      | ~ r2_hidden(X4,X2)
% 27.98/4.00      | r2_hidden(k9_subset_1(u1_struct_0(X1),X4,X0),X3)
% 27.98/4.00      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
% 27.98/4.00      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X4,X0),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0)))) ),
% 27.98/4.00      inference(cnf_transformation,[],[f72]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_43547,plain,
% 27.98/4.00      ( sP0(X0,X1,X2,X3) != iProver_top
% 27.98/4.00      | r2_hidden(X4,X2) != iProver_top
% 27.98/4.00      | r2_hidden(k9_subset_1(u1_struct_0(X1),X4,X0),X3) = iProver_top
% 27.98/4.00      | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 27.98/4.00      | m1_subset_1(k9_subset_1(u1_struct_0(X1),X4,X0),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0)))) != iProver_top ),
% 27.98/4.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_44894,plain,
% 27.98/4.00      ( sP0(X0,X1,X2,X3) != iProver_top
% 27.98/4.00      | r2_hidden(X4,X2) != iProver_top
% 27.98/4.00      | r2_hidden(k9_subset_1(u1_struct_0(X1),X4,X0),X3) = iProver_top
% 27.98/4.00      | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 27.98/4.00      | r1_tarski(k9_subset_1(u1_struct_0(X1),X4,X0),u1_struct_0(k1_pre_topc(X1,X0))) != iProver_top ),
% 27.98/4.00      inference(superposition,[status(thm)],[c_43555,c_43547]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_87195,plain,
% 27.98/4.00      ( sP0(sK7,sK5,X0,X1) != iProver_top
% 27.98/4.00      | r2_hidden(X2,X0) != iProver_top
% 27.98/4.00      | r2_hidden(k9_subset_1(u1_struct_0(sK5),X2,sK7),X1) = iProver_top
% 27.98/4.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 27.98/4.00      | r1_tarski(k9_subset_1(u1_struct_0(sK5),X2,sK7),sK7) != iProver_top ),
% 27.98/4.00      inference(superposition,[status(thm)],[c_43769,c_44894]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_43843,plain,
% 27.98/4.00      ( r1_tarski(sK7,u1_struct_0(sK5)) = iProver_top ),
% 27.98/4.00      inference(superposition,[status(thm)],[c_43540,c_43554]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_45106,plain,
% 27.98/4.00      ( k9_subset_1(u1_struct_0(sK5),X0,sK7) = k3_xboole_0(X0,sK7) ),
% 27.98/4.00      inference(superposition,[status(thm)],[c_43843,c_43537]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_87247,plain,
% 27.98/4.00      ( sP0(sK7,sK5,X0,X1) != iProver_top
% 27.98/4.00      | r2_hidden(X2,X0) != iProver_top
% 27.98/4.00      | r2_hidden(k3_xboole_0(X2,sK7),X1) = iProver_top
% 27.98/4.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 27.98/4.00      | r1_tarski(k3_xboole_0(X2,sK7),sK7) != iProver_top ),
% 27.98/4.00      inference(demodulation,[status(thm)],[c_87195,c_45106]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_103275,plain,
% 27.98/4.00      ( sP0(sK7,sK5,X0,X1) != iProver_top
% 27.98/4.00      | r2_hidden(k3_xboole_0(sK6,sK7),X1) = iProver_top
% 27.98/4.00      | r2_hidden(sK6,X0) != iProver_top
% 27.98/4.00      | r1_tarski(k3_xboole_0(sK6,sK7),sK7) != iProver_top ),
% 27.98/4.00      inference(superposition,[status(thm)],[c_43539,c_87247]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_103834,plain,
% 27.98/4.00      ( r2_hidden(k3_xboole_0(sK6,sK7),k1_tops_2(sK5,sK7,X0)) = iProver_top
% 27.98/4.00      | r2_hidden(sK6,X0) != iProver_top
% 27.98/4.00      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top
% 27.98/4.00      | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 27.98/4.00      | r1_tarski(k3_xboole_0(sK6,sK7),sK7) != iProver_top ),
% 27.98/4.00      inference(superposition,[status(thm)],[c_43531,c_103275]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_30,plain,
% 27.98/4.00      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
% 27.98/4.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_104649,plain,
% 27.98/4.00      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top
% 27.98/4.00      | r2_hidden(sK6,X0) != iProver_top
% 27.98/4.00      | r2_hidden(k3_xboole_0(sK6,sK7),k1_tops_2(sK5,sK7,X0)) = iProver_top
% 27.98/4.00      | r1_tarski(k3_xboole_0(sK6,sK7),sK7) != iProver_top ),
% 27.98/4.00      inference(global_propositional_subsumption,[status(thm)],[c_103834,c_30]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_104650,plain,
% 27.98/4.00      ( r2_hidden(k3_xboole_0(sK6,sK7),k1_tops_2(sK5,sK7,X0)) = iProver_top
% 27.98/4.00      | r2_hidden(sK6,X0) != iProver_top
% 27.98/4.00      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top
% 27.98/4.00      | r1_tarski(k3_xboole_0(sK6,sK7),sK7) != iProver_top ),
% 27.98/4.00      inference(renaming,[status(thm)],[c_104649]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_22,negated_conjecture,
% 27.98/4.00      ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK5),sK6,sK7),k1_tops_2(sK5,sK7,sK8)) ),
% 27.98/4.00      inference(cnf_transformation,[],[f68]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_43543,plain,
% 27.98/4.00      ( r2_hidden(k9_subset_1(u1_struct_0(sK5),sK6,sK7),k1_tops_2(sK5,sK7,sK8)) != iProver_top ),
% 27.98/4.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_45193,plain,
% 27.98/4.00      ( r2_hidden(k3_xboole_0(sK6,sK7),k1_tops_2(sK5,sK7,sK8)) != iProver_top ),
% 27.98/4.00      inference(demodulation,[status(thm)],[c_45106,c_43543]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_104666,plain,
% 27.98/4.00      ( r2_hidden(sK6,sK8) != iProver_top
% 27.98/4.00      | m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top
% 27.98/4.00      | r1_tarski(k3_xboole_0(sK6,sK7),sK7) != iProver_top ),
% 27.98/4.00      inference(superposition,[status(thm)],[c_104650,c_45193]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_24,negated_conjecture,
% 27.98/4.00      ( m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) ),
% 27.98/4.00      inference(cnf_transformation,[],[f66]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_31,plain,
% 27.98/4.00      ( m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) = iProver_top ),
% 27.98/4.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_23,negated_conjecture,
% 27.98/4.00      ( r2_hidden(sK6,sK8) ),
% 27.98/4.00      inference(cnf_transformation,[],[f67]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_32,plain,
% 27.98/4.00      ( r2_hidden(sK6,sK8) = iProver_top ),
% 27.98/4.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_104781,plain,
% 27.98/4.00      ( r1_tarski(k3_xboole_0(sK6,sK7),sK7) != iProver_top ),
% 27.98/4.00      inference(global_propositional_subsumption,
% 27.98/4.00                [status(thm)],
% 27.98/4.00                [c_104666,c_31,c_32]) ).
% 27.98/4.00  
% 27.98/4.00  cnf(c_131878,plain,
% 27.98/4.00      ( $false ),
% 27.98/4.00      inference(superposition,[status(thm)],[c_131518,c_104781]) ).
% 27.98/4.00  
% 27.98/4.00  
% 27.98/4.00  % SZS output end CNFRefutation for theBenchmark.p
% 27.98/4.00  
% 27.98/4.00  ------                               Statistics
% 27.98/4.00  
% 27.98/4.00  ------ Selected
% 27.98/4.00  
% 27.98/4.00  total_time:                             3.363
% 27.98/4.00  
%------------------------------------------------------------------------------
