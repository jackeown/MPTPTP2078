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
% DateTime   : Thu Dec  3 12:26:00 EST 2020

% Result     : Theorem 6.74s
% Output     : CNFRefutation 6.74s
% Verified   : 
% Statistics : Number of formulae       :  164 (3606 expanded)
%              Number of clauses        :  102 ( 967 expanded)
%              Number of leaves         :   17 (1049 expanded)
%              Depth                    :   26
%              Number of atoms          :  598 (21847 expanded)
%              Number of equality atoms :  195 (3544 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                            & v4_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                      & v4_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ? [X5] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
                      & v4_pre_topc(X5,X0)
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f28])).

fof(f31,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
          & v4_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4
        & v4_pre_topc(sK1(X0,X1,X4),X0)
        & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
              | ~ v4_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1)
            | ~ v4_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r1_tarski(sK0(X0,X1),X1)
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r1_tarski(sK0(X0,X1),X1)
                & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ( k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4
                    & v4_pre_topc(sK1(X0,X1,X4),X0)
                    & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f31,f30])).

fof(f51,plain,(
    ! [X4,X0,X1] :
      ( v4_pre_topc(sK1(X0,X1,X4),X0)
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,conjecture,(
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

fof(f12,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f11])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3)
              | ~ v4_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( k1_tarski(sK5) != k9_subset_1(u1_struct_0(X0),X1,X3)
            | ~ v4_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r2_hidden(sK5,X1)
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ! [X3] :
                ( k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),sK4,X3)
                | ~ v4_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & r2_hidden(X2,sK4)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & v2_tex_2(sK4,X0)
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK3),X1,X3)
                  | ~ v4_pre_topc(X3,sK3)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(sK3)) )
          & v2_tex_2(X1,sK3)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) )
      & l1_pre_topc(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ! [X3] :
        ( k1_tarski(sK5) != k9_subset_1(u1_struct_0(sK3),sK4,X3)
        | ~ v4_pre_topc(X3,sK3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3))) )
    & r2_hidden(sK5,sK4)
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & v2_tex_2(sK4,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & l1_pre_topc(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f24,f37,f36,f35])).

fof(f58,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f59,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f38])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f10,axiom,(
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
                            & v3_pre_topc(X3,X0) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
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
    inference(pure_predicate_removal,[],[f10])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,X3)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,sK2(X0,X1,X2))
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,sK2(X0,X1,X2))
                & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f33])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f62,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f60,plain,(
    v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f61,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f38])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,sK2(X0,X1,X2))
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f64,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k2_enumset1(X2,X2,X2,X2) = k9_subset_1(u1_struct_0(X0),X1,sK2(X0,X1,X2))
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f57,f64])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f67,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f52,plain,(
    ! [X4,X0,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f63,plain,(
    ! [X3] :
      ( k1_tarski(sK5) != k9_subset_1(u1_struct_0(sK3),sK4,X3)
      | ~ v4_pre_topc(X3,sK3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f66,plain,(
    ! [X3] :
      ( k2_enumset1(sK5,sK5,sK5,sK5) != k9_subset_1(u1_struct_0(sK3),sK4,X3)
      | ~ v4_pre_topc(X3,sK3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(definition_unfolding,[],[f63,f64])).

fof(f50,plain,(
    ! [X4,X0,X1] :
      ( m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_13,plain,
    ( v4_pre_topc(sK1(X0,X1,X2),X0)
    | ~ v2_tex_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X2,X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_477,plain,
    ( v4_pre_topc(sK1(X0,X1,X2),X0)
    | ~ v2_tex_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X2,X1)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_22])).

cnf(c_478,plain,
    ( v4_pre_topc(sK1(sK3,X0,X1),sK3)
    | ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X1,X0) ),
    inference(unflattening,[status(thm)],[c_477])).

cnf(c_2016,plain,
    ( v4_pre_topc(sK1(sK3,X0,X1),sK3) = iProver_top
    | v2_tex_2(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_478])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2027,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2022,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2026,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2509,plain,
    ( r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2022,c_2026])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_178,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_179,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_178])).

cnf(c_224,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_3,c_179])).

cnf(c_2021,plain,
    ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_224])).

cnf(c_4430,plain,
    ( k9_subset_1(u1_struct_0(sK3),X0,sK4) = k9_subset_1(u1_struct_0(sK3),sK4,X0) ),
    inference(superposition,[status(thm)],[c_2509,c_2021])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_226,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_179])).

cnf(c_2019,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_226])).

cnf(c_3717,plain,
    ( k9_subset_1(u1_struct_0(sK3),X0,sK4) = k3_xboole_0(X0,sK4) ),
    inference(superposition,[status(thm)],[c_2509,c_2019])).

cnf(c_4436,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,X0) = k3_xboole_0(X0,sK4) ),
    inference(light_normalisation,[status(thm)],[c_4430,c_3717])).

cnf(c_16,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_18,negated_conjecture,
    ( r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_326,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK4 != X0
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_18])).

cnf(c_327,plain,
    ( ~ v2_tex_2(sK4,X0)
    | m1_subset_1(sK2(X0,sK4,sK5),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK5,u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_326])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_314,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | sK4 != X2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_18])).

cnf(c_315,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
    | m1_subset_1(sK5,X0) ),
    inference(unflattening,[status(thm)],[c_314])).

cnf(c_336,plain,
    ( ~ v2_tex_2(sK4,X0)
    | m1_subset_1(sK2(X0,sK4,sK5),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_327,c_315])).

cnf(c_466,plain,
    ( ~ v2_tex_2(sK4,X0)
    | m1_subset_1(sK2(X0,sK4,sK5),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_336,c_22])).

cnf(c_467,plain,
    ( ~ v2_tex_2(sK4,sK3)
    | m1_subset_1(sK2(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unflattening,[status(thm)],[c_466])).

cnf(c_20,negated_conjecture,
    ( v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_329,plain,
    ( ~ v2_tex_2(sK4,sK3)
    | m1_subset_1(sK2(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_327])).

cnf(c_469,plain,
    ( m1_subset_1(sK2(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_467,c_22,c_21,c_20,c_19,c_329])).

cnf(c_2017,plain,
    ( m1_subset_1(sK2(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_469])).

cnf(c_2510,plain,
    ( r1_tarski(sK2(sK3,sK4,sK5),u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2017,c_2026])).

cnf(c_3718,plain,
    ( k9_subset_1(u1_struct_0(sK3),X0,sK2(sK3,sK4,sK5)) = k3_xboole_0(X0,sK2(sK3,sK4,sK5)) ),
    inference(superposition,[status(thm)],[c_2510,c_2019])).

cnf(c_8629,plain,
    ( k3_xboole_0(sK2(sK3,sK4,sK5),sK4) = k3_xboole_0(sK4,sK2(sK3,sK4,sK5)) ),
    inference(superposition,[status(thm)],[c_4436,c_3718])).

cnf(c_15,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,sK2(X1,X0,X2)) = k2_enumset1(X2,X2,X2,X2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_348,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,sK2(X1,X0,X2)) = k2_enumset1(X2,X2,X2,X2)
    | sK4 != X0
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_18])).

cnf(c_349,plain,
    ( ~ v2_tex_2(sK4,X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK5,u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | k9_subset_1(u1_struct_0(X0),sK4,sK2(X0,sK4,sK5)) = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(unflattening,[status(thm)],[c_348])).

cnf(c_358,plain,
    ( ~ v2_tex_2(sK4,X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | k9_subset_1(u1_struct_0(X0),sK4,sK2(X0,sK4,sK5)) = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_349,c_315])).

cnf(c_458,plain,
    ( ~ v2_tex_2(sK4,X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
    | k9_subset_1(u1_struct_0(X0),sK4,sK2(X0,sK4,sK5)) = k2_enumset1(sK5,sK5,sK5,sK5)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_358,c_22])).

cnf(c_459,plain,
    ( ~ v2_tex_2(sK4,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | k9_subset_1(u1_struct_0(sK3),sK4,sK2(sK3,sK4,sK5)) = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(unflattening,[status(thm)],[c_458])).

cnf(c_351,plain,
    ( ~ v2_tex_2(sK4,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ l1_pre_topc(sK3)
    | k9_subset_1(u1_struct_0(sK3),sK4,sK2(sK3,sK4,sK5)) = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_349])).

cnf(c_461,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,sK2(sK3,sK4,sK5)) = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_459,c_22,c_21,c_20,c_19,c_351])).

cnf(c_7674,plain,
    ( k3_xboole_0(sK4,sK2(sK3,sK4,sK5)) = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(superposition,[status(thm)],[c_3718,c_461])).

cnf(c_8632,plain,
    ( k3_xboole_0(sK2(sK3,sK4,sK5),sK4) = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(light_normalisation,[status(thm)],[c_8629,c_7674])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2028,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3716,plain,
    ( k9_subset_1(X0,X1,X0) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_2028,c_2019])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_225,plain,
    ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
    | ~ r1_tarski(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_179])).

cnf(c_2020,plain,
    ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_225])).

cnf(c_3796,plain,
    ( m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X1,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3716,c_2020])).

cnf(c_10947,plain,
    ( m1_subset_1(k2_enumset1(sK5,sK5,sK5,sK5),k1_zfmisc_1(sK4)) = iProver_top
    | r1_tarski(sK4,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_8632,c_3796])).

cnf(c_2168,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2169,plain,
    ( r1_tarski(sK4,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2168])).

cnf(c_15163,plain,
    ( m1_subset_1(k2_enumset1(sK5,sK5,sK5,sK5),k1_zfmisc_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10947,c_2169])).

cnf(c_15167,plain,
    ( r1_tarski(k2_enumset1(sK5,sK5,sK5,sK5),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_15163,c_2026])).

cnf(c_12,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,sK1(X1,X0,X2)) = X2 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_519,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | k9_subset_1(u1_struct_0(X1),X0,sK1(X1,X0,X2)) = X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_22])).

cnf(c_520,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X1,X0)
    | k9_subset_1(u1_struct_0(sK3),X0,sK1(sK3,X0,X1)) = X1 ),
    inference(unflattening,[status(thm)],[c_519])).

cnf(c_2014,plain,
    ( k9_subset_1(u1_struct_0(sK3),X0,sK1(sK3,X0,X1)) = X1
    | v2_tex_2(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_520])).

cnf(c_2685,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,sK1(sK3,sK4,X0)) = X0
    | v2_tex_2(sK4,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2022,c_2014])).

cnf(c_24,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_811,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X1,X0)
    | k9_subset_1(u1_struct_0(sK3),X0,sK1(sK3,X0,X1)) = X1
    | sK4 != X0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_520])).

cnf(c_812,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X0,sK4)
    | k9_subset_1(u1_struct_0(sK3),sK4,sK1(sK3,sK4,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_811])).

cnf(c_813,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,sK1(sK3,sK4,X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_812])).

cnf(c_2721,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,sK1(sK3,sK4,X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2685,c_24,c_813])).

cnf(c_3799,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,sK1(sK3,sK4,k9_subset_1(u1_struct_0(sK3),X0,X1))) = k9_subset_1(u1_struct_0(sK3),X0,X1)
    | r1_tarski(X1,u1_struct_0(sK3)) != iProver_top
    | r1_tarski(k9_subset_1(u1_struct_0(sK3),X0,X1),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2020,c_2721])).

cnf(c_4684,plain,
    ( k3_xboole_0(sK1(sK3,sK4,k9_subset_1(u1_struct_0(sK3),X0,X1)),sK4) = k9_subset_1(u1_struct_0(sK3),X0,X1)
    | r1_tarski(X1,u1_struct_0(sK3)) != iProver_top
    | r1_tarski(k9_subset_1(u1_struct_0(sK3),X0,X1),sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3799,c_4436])).

cnf(c_4688,plain,
    ( k3_xboole_0(sK1(sK3,sK4,k9_subset_1(u1_struct_0(sK3),sK4,sK2(sK3,sK4,sK5))),sK4) = k9_subset_1(u1_struct_0(sK3),sK4,sK2(sK3,sK4,sK5))
    | r1_tarski(k2_enumset1(sK5,sK5,sK5,sK5),sK4) != iProver_top
    | r1_tarski(sK2(sK3,sK4,sK5),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_461,c_4684])).

cnf(c_4697,plain,
    ( k3_xboole_0(sK1(sK3,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK4) = k2_enumset1(sK5,sK5,sK5,sK5)
    | r1_tarski(k2_enumset1(sK5,sK5,sK5,sK5),sK4) != iProver_top
    | r1_tarski(sK2(sK3,sK4,sK5),u1_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4688,c_461])).

cnf(c_23,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_25,plain,
    ( v2_tex_2(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_26,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_328,plain,
    ( v2_tex_2(sK4,X0) != iProver_top
    | m1_subset_1(sK2(X0,sK4,sK5),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(X0)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_327])).

cnf(c_330,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | m1_subset_1(sK2(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_328])).

cnf(c_2185,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(X0,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2411,plain,
    ( ~ m1_subset_1(sK2(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(sK2(sK3,sK4,sK5),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2185])).

cnf(c_2412,plain,
    ( m1_subset_1(sK2(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(sK2(sK3,sK4,sK5),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2411])).

cnf(c_5009,plain,
    ( r1_tarski(k2_enumset1(sK5,sK5,sK5,sK5),sK4) != iProver_top
    | k3_xboole_0(sK1(sK3,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK4) = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4697,c_23,c_24,c_25,c_26,c_330,c_2412])).

cnf(c_5010,plain,
    ( k3_xboole_0(sK1(sK3,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK4) = k2_enumset1(sK5,sK5,sK5,sK5)
    | r1_tarski(k2_enumset1(sK5,sK5,sK5,sK5),sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_5009])).

cnf(c_15883,plain,
    ( k3_xboole_0(sK1(sK3,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK4) = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(superposition,[status(thm)],[c_15167,c_5010])).

cnf(c_17,negated_conjecture,
    ( ~ v4_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_enumset1(sK5,sK5,sK5,sK5) != k9_subset_1(u1_struct_0(sK3),sK4,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2025,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK5) != k9_subset_1(u1_struct_0(sK3),sK4,X0)
    | v4_pre_topc(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_8592,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK5) != k3_xboole_0(X0,sK4)
    | v4_pre_topc(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4436,c_2025])).

cnf(c_16260,plain,
    ( v4_pre_topc(sK1(sK3,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK3) != iProver_top
    | m1_subset_1(sK1(sK3,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_15883,c_8592])).

cnf(c_16540,plain,
    ( v4_pre_topc(sK1(sK3,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK3) != iProver_top
    | r1_tarski(sK1(sK3,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2027,c_16260])).

cnf(c_3794,plain,
    ( m1_subset_1(k2_enumset1(sK5,sK5,sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | r1_tarski(sK2(sK3,sK4,sK5),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_461,c_2020])).

cnf(c_14,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_498,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_22])).

cnf(c_499,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK1(sK3,X0,X1),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X1,X0) ),
    inference(unflattening,[status(thm)],[c_498])).

cnf(c_2015,plain,
    ( v2_tex_2(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK1(sK3,X0,X1),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_499])).

cnf(c_16541,plain,
    ( v4_pre_topc(sK1(sK3,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK3) != iProver_top
    | v2_tex_2(sK4,sK3) != iProver_top
    | m1_subset_1(k2_enumset1(sK5,sK5,sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(k2_enumset1(sK5,sK5,sK5,sK5),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2015,c_16260])).

cnf(c_16904,plain,
    ( v4_pre_topc(sK1(sK3,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16540,c_23,c_24,c_25,c_26,c_330,c_2412,c_3794,c_15167,c_16541])).

cnf(c_16908,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | m1_subset_1(k2_enumset1(sK5,sK5,sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(k2_enumset1(sK5,sK5,sK5,sK5),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2016,c_16904])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16908,c_15167,c_3794,c_2412,c_330,c_26,c_25,c_24,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:15:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 6.74/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.74/1.49  
% 6.74/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.74/1.49  
% 6.74/1.49  ------  iProver source info
% 6.74/1.49  
% 6.74/1.49  git: date: 2020-06-30 10:37:57 +0100
% 6.74/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.74/1.49  git: non_committed_changes: false
% 6.74/1.49  git: last_make_outside_of_git: false
% 6.74/1.49  
% 6.74/1.49  ------ 
% 6.74/1.49  
% 6.74/1.49  ------ Input Options
% 6.74/1.49  
% 6.74/1.49  --out_options                           all
% 6.74/1.49  --tptp_safe_out                         true
% 6.74/1.49  --problem_path                          ""
% 6.74/1.49  --include_path                          ""
% 6.74/1.49  --clausifier                            res/vclausify_rel
% 6.74/1.49  --clausifier_options                    ""
% 6.74/1.49  --stdin                                 false
% 6.74/1.49  --stats_out                             all
% 6.74/1.49  
% 6.74/1.49  ------ General Options
% 6.74/1.49  
% 6.74/1.49  --fof                                   false
% 6.74/1.49  --time_out_real                         305.
% 6.74/1.49  --time_out_virtual                      -1.
% 6.74/1.49  --symbol_type_check                     false
% 6.74/1.49  --clausify_out                          false
% 6.74/1.49  --sig_cnt_out                           false
% 6.74/1.49  --trig_cnt_out                          false
% 6.74/1.49  --trig_cnt_out_tolerance                1.
% 6.74/1.49  --trig_cnt_out_sk_spl                   false
% 6.74/1.49  --abstr_cl_out                          false
% 6.74/1.49  
% 6.74/1.49  ------ Global Options
% 6.74/1.49  
% 6.74/1.49  --schedule                              default
% 6.74/1.49  --add_important_lit                     false
% 6.74/1.49  --prop_solver_per_cl                    1000
% 6.74/1.49  --min_unsat_core                        false
% 6.74/1.49  --soft_assumptions                      false
% 6.74/1.49  --soft_lemma_size                       3
% 6.74/1.49  --prop_impl_unit_size                   0
% 6.74/1.49  --prop_impl_unit                        []
% 6.74/1.49  --share_sel_clauses                     true
% 6.74/1.49  --reset_solvers                         false
% 6.74/1.49  --bc_imp_inh                            [conj_cone]
% 6.74/1.49  --conj_cone_tolerance                   3.
% 6.74/1.49  --extra_neg_conj                        none
% 6.74/1.49  --large_theory_mode                     true
% 6.74/1.49  --prolific_symb_bound                   200
% 6.74/1.49  --lt_threshold                          2000
% 6.74/1.49  --clause_weak_htbl                      true
% 6.74/1.49  --gc_record_bc_elim                     false
% 6.74/1.49  
% 6.74/1.49  ------ Preprocessing Options
% 6.74/1.49  
% 6.74/1.49  --preprocessing_flag                    true
% 6.74/1.49  --time_out_prep_mult                    0.1
% 6.74/1.49  --splitting_mode                        input
% 6.74/1.49  --splitting_grd                         true
% 6.74/1.49  --splitting_cvd                         false
% 6.74/1.49  --splitting_cvd_svl                     false
% 6.74/1.49  --splitting_nvd                         32
% 6.74/1.49  --sub_typing                            true
% 6.74/1.49  --prep_gs_sim                           true
% 6.74/1.49  --prep_unflatten                        true
% 6.74/1.49  --prep_res_sim                          true
% 6.74/1.49  --prep_upred                            true
% 6.74/1.49  --prep_sem_filter                       exhaustive
% 6.74/1.49  --prep_sem_filter_out                   false
% 6.74/1.49  --pred_elim                             true
% 6.74/1.49  --res_sim_input                         true
% 6.74/1.49  --eq_ax_congr_red                       true
% 6.74/1.49  --pure_diseq_elim                       true
% 6.74/1.49  --brand_transform                       false
% 6.74/1.49  --non_eq_to_eq                          false
% 6.74/1.49  --prep_def_merge                        true
% 6.74/1.49  --prep_def_merge_prop_impl              false
% 6.74/1.49  --prep_def_merge_mbd                    true
% 6.74/1.49  --prep_def_merge_tr_red                 false
% 6.74/1.49  --prep_def_merge_tr_cl                  false
% 6.74/1.49  --smt_preprocessing                     true
% 6.74/1.49  --smt_ac_axioms                         fast
% 6.74/1.49  --preprocessed_out                      false
% 6.74/1.49  --preprocessed_stats                    false
% 6.74/1.49  
% 6.74/1.49  ------ Abstraction refinement Options
% 6.74/1.49  
% 6.74/1.49  --abstr_ref                             []
% 6.74/1.49  --abstr_ref_prep                        false
% 6.74/1.49  --abstr_ref_until_sat                   false
% 6.74/1.49  --abstr_ref_sig_restrict                funpre
% 6.74/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 6.74/1.49  --abstr_ref_under                       []
% 6.74/1.49  
% 6.74/1.49  ------ SAT Options
% 6.74/1.49  
% 6.74/1.49  --sat_mode                              false
% 6.74/1.49  --sat_fm_restart_options                ""
% 6.74/1.49  --sat_gr_def                            false
% 6.74/1.49  --sat_epr_types                         true
% 6.74/1.49  --sat_non_cyclic_types                  false
% 6.74/1.49  --sat_finite_models                     false
% 6.74/1.49  --sat_fm_lemmas                         false
% 6.74/1.49  --sat_fm_prep                           false
% 6.74/1.49  --sat_fm_uc_incr                        true
% 6.74/1.49  --sat_out_model                         small
% 6.74/1.49  --sat_out_clauses                       false
% 6.74/1.49  
% 6.74/1.49  ------ QBF Options
% 6.74/1.49  
% 6.74/1.49  --qbf_mode                              false
% 6.74/1.49  --qbf_elim_univ                         false
% 6.74/1.49  --qbf_dom_inst                          none
% 6.74/1.49  --qbf_dom_pre_inst                      false
% 6.74/1.49  --qbf_sk_in                             false
% 6.74/1.49  --qbf_pred_elim                         true
% 6.74/1.49  --qbf_split                             512
% 6.74/1.49  
% 6.74/1.49  ------ BMC1 Options
% 6.74/1.49  
% 6.74/1.49  --bmc1_incremental                      false
% 6.74/1.49  --bmc1_axioms                           reachable_all
% 6.74/1.49  --bmc1_min_bound                        0
% 6.74/1.49  --bmc1_max_bound                        -1
% 6.74/1.49  --bmc1_max_bound_default                -1
% 6.74/1.49  --bmc1_symbol_reachability              true
% 6.74/1.49  --bmc1_property_lemmas                  false
% 6.74/1.49  --bmc1_k_induction                      false
% 6.74/1.49  --bmc1_non_equiv_states                 false
% 6.74/1.49  --bmc1_deadlock                         false
% 6.74/1.49  --bmc1_ucm                              false
% 6.74/1.49  --bmc1_add_unsat_core                   none
% 6.74/1.49  --bmc1_unsat_core_children              false
% 6.74/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 6.74/1.49  --bmc1_out_stat                         full
% 6.74/1.49  --bmc1_ground_init                      false
% 6.74/1.49  --bmc1_pre_inst_next_state              false
% 6.74/1.49  --bmc1_pre_inst_state                   false
% 6.74/1.49  --bmc1_pre_inst_reach_state             false
% 6.74/1.49  --bmc1_out_unsat_core                   false
% 6.74/1.49  --bmc1_aig_witness_out                  false
% 6.74/1.49  --bmc1_verbose                          false
% 6.74/1.49  --bmc1_dump_clauses_tptp                false
% 6.74/1.49  --bmc1_dump_unsat_core_tptp             false
% 6.74/1.49  --bmc1_dump_file                        -
% 6.74/1.49  --bmc1_ucm_expand_uc_limit              128
% 6.74/1.49  --bmc1_ucm_n_expand_iterations          6
% 6.74/1.49  --bmc1_ucm_extend_mode                  1
% 6.74/1.49  --bmc1_ucm_init_mode                    2
% 6.74/1.49  --bmc1_ucm_cone_mode                    none
% 6.74/1.49  --bmc1_ucm_reduced_relation_type        0
% 6.74/1.49  --bmc1_ucm_relax_model                  4
% 6.74/1.49  --bmc1_ucm_full_tr_after_sat            true
% 6.74/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 6.74/1.49  --bmc1_ucm_layered_model                none
% 6.74/1.49  --bmc1_ucm_max_lemma_size               10
% 6.74/1.49  
% 6.74/1.49  ------ AIG Options
% 6.74/1.49  
% 6.74/1.49  --aig_mode                              false
% 6.74/1.49  
% 6.74/1.49  ------ Instantiation Options
% 6.74/1.49  
% 6.74/1.49  --instantiation_flag                    true
% 6.74/1.49  --inst_sos_flag                         true
% 6.74/1.49  --inst_sos_phase                        true
% 6.74/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.74/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.74/1.49  --inst_lit_sel_side                     num_symb
% 6.74/1.49  --inst_solver_per_active                1400
% 6.74/1.49  --inst_solver_calls_frac                1.
% 6.74/1.49  --inst_passive_queue_type               priority_queues
% 6.74/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.74/1.49  --inst_passive_queues_freq              [25;2]
% 6.74/1.49  --inst_dismatching                      true
% 6.74/1.49  --inst_eager_unprocessed_to_passive     true
% 6.74/1.49  --inst_prop_sim_given                   true
% 6.74/1.49  --inst_prop_sim_new                     false
% 6.74/1.49  --inst_subs_new                         false
% 6.74/1.49  --inst_eq_res_simp                      false
% 6.74/1.49  --inst_subs_given                       false
% 6.74/1.49  --inst_orphan_elimination               true
% 6.74/1.49  --inst_learning_loop_flag               true
% 6.74/1.49  --inst_learning_start                   3000
% 6.74/1.49  --inst_learning_factor                  2
% 6.74/1.49  --inst_start_prop_sim_after_learn       3
% 6.74/1.49  --inst_sel_renew                        solver
% 6.74/1.49  --inst_lit_activity_flag                true
% 6.74/1.49  --inst_restr_to_given                   false
% 6.74/1.49  --inst_activity_threshold               500
% 6.74/1.49  --inst_out_proof                        true
% 6.74/1.49  
% 6.74/1.49  ------ Resolution Options
% 6.74/1.49  
% 6.74/1.49  --resolution_flag                       true
% 6.74/1.49  --res_lit_sel                           adaptive
% 6.74/1.49  --res_lit_sel_side                      none
% 6.74/1.49  --res_ordering                          kbo
% 6.74/1.49  --res_to_prop_solver                    active
% 6.74/1.49  --res_prop_simpl_new                    false
% 6.74/1.49  --res_prop_simpl_given                  true
% 6.74/1.49  --res_passive_queue_type                priority_queues
% 6.74/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.74/1.49  --res_passive_queues_freq               [15;5]
% 6.74/1.49  --res_forward_subs                      full
% 6.74/1.49  --res_backward_subs                     full
% 6.74/1.49  --res_forward_subs_resolution           true
% 6.74/1.49  --res_backward_subs_resolution          true
% 6.74/1.49  --res_orphan_elimination                true
% 6.74/1.49  --res_time_limit                        2.
% 6.74/1.49  --res_out_proof                         true
% 6.74/1.49  
% 6.74/1.49  ------ Superposition Options
% 6.74/1.49  
% 6.74/1.49  --superposition_flag                    true
% 6.74/1.49  --sup_passive_queue_type                priority_queues
% 6.74/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.74/1.49  --sup_passive_queues_freq               [8;1;4]
% 6.74/1.49  --demod_completeness_check              fast
% 6.74/1.49  --demod_use_ground                      true
% 6.74/1.49  --sup_to_prop_solver                    passive
% 6.74/1.49  --sup_prop_simpl_new                    true
% 6.74/1.49  --sup_prop_simpl_given                  true
% 6.74/1.49  --sup_fun_splitting                     true
% 6.74/1.49  --sup_smt_interval                      50000
% 6.74/1.49  
% 6.74/1.49  ------ Superposition Simplification Setup
% 6.74/1.49  
% 6.74/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 6.74/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 6.74/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 6.74/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 6.74/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 6.74/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 6.74/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 6.74/1.49  --sup_immed_triv                        [TrivRules]
% 6.74/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.74/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 6.74/1.49  --sup_immed_bw_main                     []
% 6.74/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 6.74/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 6.74/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 6.74/1.49  --sup_input_bw                          []
% 6.74/1.49  
% 6.74/1.49  ------ Combination Options
% 6.74/1.49  
% 6.74/1.49  --comb_res_mult                         3
% 6.74/1.49  --comb_sup_mult                         2
% 6.74/1.49  --comb_inst_mult                        10
% 6.74/1.49  
% 6.74/1.49  ------ Debug Options
% 6.74/1.49  
% 6.74/1.49  --dbg_backtrace                         false
% 6.74/1.49  --dbg_dump_prop_clauses                 false
% 6.74/1.49  --dbg_dump_prop_clauses_file            -
% 6.74/1.49  --dbg_out_stat                          false
% 6.74/1.49  ------ Parsing...
% 6.74/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.74/1.49  
% 6.74/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 6.74/1.49  
% 6.74/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.74/1.49  
% 6.74/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.74/1.49  ------ Proving...
% 6.74/1.49  ------ Problem Properties 
% 6.74/1.49  
% 6.74/1.49  
% 6.74/1.49  clauses                                 20
% 6.74/1.49  conjectures                             4
% 6.74/1.49  EPR                                     3
% 6.74/1.49  Horn                                    18
% 6.74/1.49  unary                                   6
% 6.74/1.49  binary                                  6
% 6.74/1.49  lits                                    50
% 6.74/1.49  lits eq                                 7
% 6.74/1.49  fd_pure                                 0
% 6.74/1.49  fd_pseudo                               0
% 6.74/1.49  fd_cond                                 0
% 6.74/1.49  fd_pseudo_cond                          1
% 6.74/1.49  AC symbols                              0
% 6.74/1.49  
% 6.74/1.49  ------ Schedule dynamic 5 is on 
% 6.74/1.49  
% 6.74/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.74/1.49  
% 6.74/1.49  
% 6.74/1.49  ------ 
% 6.74/1.49  Current options:
% 6.74/1.49  ------ 
% 6.74/1.49  
% 6.74/1.49  ------ Input Options
% 6.74/1.49  
% 6.74/1.49  --out_options                           all
% 6.74/1.49  --tptp_safe_out                         true
% 6.74/1.49  --problem_path                          ""
% 6.74/1.49  --include_path                          ""
% 6.74/1.49  --clausifier                            res/vclausify_rel
% 6.74/1.49  --clausifier_options                    ""
% 6.74/1.49  --stdin                                 false
% 6.74/1.49  --stats_out                             all
% 6.74/1.49  
% 6.74/1.49  ------ General Options
% 6.74/1.49  
% 6.74/1.49  --fof                                   false
% 6.74/1.49  --time_out_real                         305.
% 6.74/1.49  --time_out_virtual                      -1.
% 6.74/1.49  --symbol_type_check                     false
% 6.74/1.49  --clausify_out                          false
% 6.74/1.49  --sig_cnt_out                           false
% 6.74/1.49  --trig_cnt_out                          false
% 6.74/1.49  --trig_cnt_out_tolerance                1.
% 6.74/1.49  --trig_cnt_out_sk_spl                   false
% 6.74/1.49  --abstr_cl_out                          false
% 6.74/1.49  
% 6.74/1.49  ------ Global Options
% 6.74/1.49  
% 6.74/1.49  --schedule                              default
% 6.74/1.49  --add_important_lit                     false
% 6.74/1.49  --prop_solver_per_cl                    1000
% 6.74/1.49  --min_unsat_core                        false
% 6.74/1.49  --soft_assumptions                      false
% 6.74/1.49  --soft_lemma_size                       3
% 6.74/1.49  --prop_impl_unit_size                   0
% 6.74/1.49  --prop_impl_unit                        []
% 6.74/1.49  --share_sel_clauses                     true
% 6.74/1.49  --reset_solvers                         false
% 6.74/1.49  --bc_imp_inh                            [conj_cone]
% 6.74/1.49  --conj_cone_tolerance                   3.
% 6.74/1.49  --extra_neg_conj                        none
% 6.74/1.49  --large_theory_mode                     true
% 6.74/1.49  --prolific_symb_bound                   200
% 6.74/1.49  --lt_threshold                          2000
% 6.74/1.49  --clause_weak_htbl                      true
% 6.74/1.49  --gc_record_bc_elim                     false
% 6.74/1.49  
% 6.74/1.49  ------ Preprocessing Options
% 6.74/1.49  
% 6.74/1.49  --preprocessing_flag                    true
% 6.74/1.49  --time_out_prep_mult                    0.1
% 6.74/1.49  --splitting_mode                        input
% 6.74/1.49  --splitting_grd                         true
% 6.74/1.49  --splitting_cvd                         false
% 6.74/1.49  --splitting_cvd_svl                     false
% 6.74/1.49  --splitting_nvd                         32
% 6.74/1.49  --sub_typing                            true
% 6.74/1.49  --prep_gs_sim                           true
% 6.74/1.49  --prep_unflatten                        true
% 6.74/1.49  --prep_res_sim                          true
% 6.74/1.49  --prep_upred                            true
% 6.74/1.49  --prep_sem_filter                       exhaustive
% 6.74/1.49  --prep_sem_filter_out                   false
% 6.74/1.49  --pred_elim                             true
% 6.74/1.49  --res_sim_input                         true
% 6.74/1.49  --eq_ax_congr_red                       true
% 6.74/1.49  --pure_diseq_elim                       true
% 6.74/1.49  --brand_transform                       false
% 6.74/1.49  --non_eq_to_eq                          false
% 6.74/1.49  --prep_def_merge                        true
% 6.74/1.49  --prep_def_merge_prop_impl              false
% 6.74/1.49  --prep_def_merge_mbd                    true
% 6.74/1.49  --prep_def_merge_tr_red                 false
% 6.74/1.49  --prep_def_merge_tr_cl                  false
% 6.74/1.49  --smt_preprocessing                     true
% 6.74/1.49  --smt_ac_axioms                         fast
% 6.74/1.49  --preprocessed_out                      false
% 6.74/1.49  --preprocessed_stats                    false
% 6.74/1.49  
% 6.74/1.49  ------ Abstraction refinement Options
% 6.74/1.49  
% 6.74/1.49  --abstr_ref                             []
% 6.74/1.49  --abstr_ref_prep                        false
% 6.74/1.49  --abstr_ref_until_sat                   false
% 6.74/1.49  --abstr_ref_sig_restrict                funpre
% 6.74/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 6.74/1.49  --abstr_ref_under                       []
% 6.74/1.49  
% 6.74/1.49  ------ SAT Options
% 6.74/1.49  
% 6.74/1.49  --sat_mode                              false
% 6.74/1.49  --sat_fm_restart_options                ""
% 6.74/1.49  --sat_gr_def                            false
% 6.74/1.49  --sat_epr_types                         true
% 6.74/1.49  --sat_non_cyclic_types                  false
% 6.74/1.49  --sat_finite_models                     false
% 6.74/1.49  --sat_fm_lemmas                         false
% 6.74/1.49  --sat_fm_prep                           false
% 6.74/1.49  --sat_fm_uc_incr                        true
% 6.74/1.49  --sat_out_model                         small
% 6.74/1.49  --sat_out_clauses                       false
% 6.74/1.49  
% 6.74/1.49  ------ QBF Options
% 6.74/1.49  
% 6.74/1.49  --qbf_mode                              false
% 6.74/1.49  --qbf_elim_univ                         false
% 6.74/1.49  --qbf_dom_inst                          none
% 6.74/1.49  --qbf_dom_pre_inst                      false
% 6.74/1.49  --qbf_sk_in                             false
% 6.74/1.49  --qbf_pred_elim                         true
% 6.74/1.49  --qbf_split                             512
% 6.74/1.49  
% 6.74/1.49  ------ BMC1 Options
% 6.74/1.49  
% 6.74/1.49  --bmc1_incremental                      false
% 6.74/1.49  --bmc1_axioms                           reachable_all
% 6.74/1.49  --bmc1_min_bound                        0
% 6.74/1.49  --bmc1_max_bound                        -1
% 6.74/1.49  --bmc1_max_bound_default                -1
% 6.74/1.49  --bmc1_symbol_reachability              true
% 6.74/1.49  --bmc1_property_lemmas                  false
% 6.74/1.49  --bmc1_k_induction                      false
% 6.74/1.49  --bmc1_non_equiv_states                 false
% 6.74/1.49  --bmc1_deadlock                         false
% 6.74/1.49  --bmc1_ucm                              false
% 6.74/1.49  --bmc1_add_unsat_core                   none
% 6.74/1.49  --bmc1_unsat_core_children              false
% 6.74/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 6.74/1.49  --bmc1_out_stat                         full
% 6.74/1.49  --bmc1_ground_init                      false
% 6.74/1.49  --bmc1_pre_inst_next_state              false
% 6.74/1.49  --bmc1_pre_inst_state                   false
% 6.74/1.49  --bmc1_pre_inst_reach_state             false
% 6.74/1.49  --bmc1_out_unsat_core                   false
% 6.74/1.49  --bmc1_aig_witness_out                  false
% 6.74/1.49  --bmc1_verbose                          false
% 6.74/1.49  --bmc1_dump_clauses_tptp                false
% 6.74/1.49  --bmc1_dump_unsat_core_tptp             false
% 6.74/1.49  --bmc1_dump_file                        -
% 6.74/1.49  --bmc1_ucm_expand_uc_limit              128
% 6.74/1.49  --bmc1_ucm_n_expand_iterations          6
% 6.74/1.49  --bmc1_ucm_extend_mode                  1
% 6.74/1.49  --bmc1_ucm_init_mode                    2
% 6.74/1.49  --bmc1_ucm_cone_mode                    none
% 6.74/1.49  --bmc1_ucm_reduced_relation_type        0
% 6.74/1.49  --bmc1_ucm_relax_model                  4
% 6.74/1.49  --bmc1_ucm_full_tr_after_sat            true
% 6.74/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 6.74/1.49  --bmc1_ucm_layered_model                none
% 6.74/1.49  --bmc1_ucm_max_lemma_size               10
% 6.74/1.49  
% 6.74/1.49  ------ AIG Options
% 6.74/1.49  
% 6.74/1.49  --aig_mode                              false
% 6.74/1.49  
% 6.74/1.49  ------ Instantiation Options
% 6.74/1.49  
% 6.74/1.49  --instantiation_flag                    true
% 6.74/1.49  --inst_sos_flag                         true
% 6.74/1.49  --inst_sos_phase                        true
% 6.74/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.74/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.74/1.49  --inst_lit_sel_side                     none
% 6.74/1.49  --inst_solver_per_active                1400
% 6.74/1.49  --inst_solver_calls_frac                1.
% 6.74/1.49  --inst_passive_queue_type               priority_queues
% 6.74/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.74/1.49  --inst_passive_queues_freq              [25;2]
% 6.74/1.49  --inst_dismatching                      true
% 6.74/1.49  --inst_eager_unprocessed_to_passive     true
% 6.74/1.49  --inst_prop_sim_given                   true
% 6.74/1.49  --inst_prop_sim_new                     false
% 6.74/1.49  --inst_subs_new                         false
% 6.74/1.49  --inst_eq_res_simp                      false
% 6.74/1.49  --inst_subs_given                       false
% 6.74/1.49  --inst_orphan_elimination               true
% 6.74/1.49  --inst_learning_loop_flag               true
% 6.74/1.49  --inst_learning_start                   3000
% 6.74/1.49  --inst_learning_factor                  2
% 6.74/1.49  --inst_start_prop_sim_after_learn       3
% 6.74/1.49  --inst_sel_renew                        solver
% 6.74/1.49  --inst_lit_activity_flag                true
% 6.74/1.49  --inst_restr_to_given                   false
% 6.74/1.49  --inst_activity_threshold               500
% 6.74/1.49  --inst_out_proof                        true
% 6.74/1.49  
% 6.74/1.49  ------ Resolution Options
% 6.74/1.49  
% 6.74/1.49  --resolution_flag                       false
% 6.74/1.49  --res_lit_sel                           adaptive
% 6.74/1.49  --res_lit_sel_side                      none
% 6.74/1.49  --res_ordering                          kbo
% 6.74/1.49  --res_to_prop_solver                    active
% 6.74/1.49  --res_prop_simpl_new                    false
% 6.74/1.49  --res_prop_simpl_given                  true
% 6.74/1.49  --res_passive_queue_type                priority_queues
% 6.74/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.74/1.49  --res_passive_queues_freq               [15;5]
% 6.74/1.49  --res_forward_subs                      full
% 6.74/1.49  --res_backward_subs                     full
% 6.74/1.49  --res_forward_subs_resolution           true
% 6.74/1.49  --res_backward_subs_resolution          true
% 6.74/1.49  --res_orphan_elimination                true
% 6.74/1.49  --res_time_limit                        2.
% 6.74/1.49  --res_out_proof                         true
% 6.74/1.49  
% 6.74/1.49  ------ Superposition Options
% 6.74/1.49  
% 6.74/1.49  --superposition_flag                    true
% 6.74/1.49  --sup_passive_queue_type                priority_queues
% 6.74/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.74/1.49  --sup_passive_queues_freq               [8;1;4]
% 6.74/1.49  --demod_completeness_check              fast
% 6.74/1.49  --demod_use_ground                      true
% 6.74/1.49  --sup_to_prop_solver                    passive
% 6.74/1.49  --sup_prop_simpl_new                    true
% 6.74/1.49  --sup_prop_simpl_given                  true
% 6.74/1.49  --sup_fun_splitting                     true
% 6.74/1.49  --sup_smt_interval                      50000
% 6.74/1.49  
% 6.74/1.49  ------ Superposition Simplification Setup
% 6.74/1.49  
% 6.74/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 6.74/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 6.74/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 6.74/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 6.74/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 6.74/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 6.74/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 6.74/1.49  --sup_immed_triv                        [TrivRules]
% 6.74/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.74/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 6.74/1.49  --sup_immed_bw_main                     []
% 6.74/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 6.74/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 6.74/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 6.74/1.49  --sup_input_bw                          []
% 6.74/1.49  
% 6.74/1.49  ------ Combination Options
% 6.74/1.49  
% 6.74/1.49  --comb_res_mult                         3
% 6.74/1.49  --comb_sup_mult                         2
% 6.74/1.49  --comb_inst_mult                        10
% 6.74/1.49  
% 6.74/1.49  ------ Debug Options
% 6.74/1.49  
% 6.74/1.49  --dbg_backtrace                         false
% 6.74/1.49  --dbg_dump_prop_clauses                 false
% 6.74/1.49  --dbg_dump_prop_clauses_file            -
% 6.74/1.49  --dbg_out_stat                          false
% 6.74/1.49  
% 6.74/1.49  
% 6.74/1.49  
% 6.74/1.49  
% 6.74/1.49  ------ Proving...
% 6.74/1.49  
% 6.74/1.49  
% 6.74/1.49  % SZS status Theorem for theBenchmark.p
% 6.74/1.49  
% 6.74/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 6.74/1.49  
% 6.74/1.49  fof(f9,axiom,(
% 6.74/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 6.74/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.74/1.49  
% 6.74/1.49  fof(f19,plain,(
% 6.74/1.49    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.74/1.49    inference(ennf_transformation,[],[f9])).
% 6.74/1.49  
% 6.74/1.49  fof(f20,plain,(
% 6.74/1.49    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.74/1.49    inference(flattening,[],[f19])).
% 6.74/1.49  
% 6.74/1.49  fof(f28,plain,(
% 6.74/1.49    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.74/1.49    inference(nnf_transformation,[],[f20])).
% 6.74/1.49  
% 6.74/1.49  fof(f29,plain,(
% 6.74/1.49    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v4_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.74/1.49    inference(rectify,[],[f28])).
% 6.74/1.49  
% 6.74/1.49  fof(f31,plain,(
% 6.74/1.49    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v4_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4 & v4_pre_topc(sK1(X0,X1,X4),X0) & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 6.74/1.49    introduced(choice_axiom,[])).
% 6.74/1.49  
% 6.74/1.49  fof(f30,plain,(
% 6.74/1.49    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 6.74/1.49    introduced(choice_axiom,[])).
% 6.74/1.49  
% 6.74/1.49  fof(f32,plain,(
% 6.74/1.49    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4 & v4_pre_topc(sK1(X0,X1,X4),X0) & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.74/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f31,f30])).
% 6.74/1.49  
% 6.74/1.49  fof(f51,plain,(
% 6.74/1.49    ( ! [X4,X0,X1] : (v4_pre_topc(sK1(X0,X1,X4),X0) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 6.74/1.49    inference(cnf_transformation,[],[f32])).
% 6.74/1.49  
% 6.74/1.49  fof(f11,conjecture,(
% 6.74/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,X3) & v4_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 6.74/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.74/1.49  
% 6.74/1.49  fof(f12,negated_conjecture,(
% 6.74/1.49    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,X3) & v4_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 6.74/1.49    inference(negated_conjecture,[],[f11])).
% 6.74/1.49  
% 6.74/1.49  fof(f23,plain,(
% 6.74/1.49    ? [X0] : (? [X1] : ((? [X2] : ((! [X3] : ((k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v4_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 6.74/1.49    inference(ennf_transformation,[],[f12])).
% 6.74/1.49  
% 6.74/1.49  fof(f24,plain,(
% 6.74/1.49    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 6.74/1.49    inference(flattening,[],[f23])).
% 6.74/1.49  
% 6.74/1.49  fof(f37,plain,(
% 6.74/1.49    ( ! [X0,X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (! [X3] : (k1_tarski(sK5) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK5,X1) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 6.74/1.49    introduced(choice_axiom,[])).
% 6.74/1.49  
% 6.74/1.49  fof(f36,plain,(
% 6.74/1.49    ( ! [X0] : (? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),sK4,X3) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,sK4) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(sK4,X0) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 6.74/1.49    introduced(choice_axiom,[])).
% 6.74/1.49  
% 6.74/1.49  fof(f35,plain,(
% 6.74/1.49    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK3),X1,X3) | ~v4_pre_topc(X3,sK3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK3))) & v2_tex_2(X1,sK3) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK3))),
% 6.74/1.49    introduced(choice_axiom,[])).
% 6.74/1.49  
% 6.74/1.49  fof(f38,plain,(
% 6.74/1.49    ((! [X3] : (k1_tarski(sK5) != k9_subset_1(u1_struct_0(sK3),sK4,X3) | ~v4_pre_topc(X3,sK3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))) & r2_hidden(sK5,sK4) & m1_subset_1(sK5,u1_struct_0(sK3))) & v2_tex_2(sK4,sK3) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK3)),
% 6.74/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f24,f37,f36,f35])).
% 6.74/1.49  
% 6.74/1.49  fof(f58,plain,(
% 6.74/1.49    l1_pre_topc(sK3)),
% 6.74/1.49    inference(cnf_transformation,[],[f38])).
% 6.74/1.49  
% 6.74/1.49  fof(f7,axiom,(
% 6.74/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 6.74/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.74/1.49  
% 6.74/1.49  fof(f27,plain,(
% 6.74/1.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 6.74/1.49    inference(nnf_transformation,[],[f7])).
% 6.74/1.49  
% 6.74/1.49  fof(f48,plain,(
% 6.74/1.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 6.74/1.49    inference(cnf_transformation,[],[f27])).
% 6.74/1.49  
% 6.74/1.49  fof(f59,plain,(
% 6.74/1.49    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 6.74/1.49    inference(cnf_transformation,[],[f38])).
% 6.74/1.49  
% 6.74/1.49  fof(f47,plain,(
% 6.74/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 6.74/1.49    inference(cnf_transformation,[],[f27])).
% 6.74/1.49  
% 6.74/1.49  fof(f4,axiom,(
% 6.74/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 6.74/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.74/1.49  
% 6.74/1.49  fof(f14,plain,(
% 6.74/1.49    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 6.74/1.49    inference(ennf_transformation,[],[f4])).
% 6.74/1.49  
% 6.74/1.49  fof(f44,plain,(
% 6.74/1.49    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 6.74/1.49    inference(cnf_transformation,[],[f14])).
% 6.74/1.49  
% 6.74/1.49  fof(f6,axiom,(
% 6.74/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 6.74/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.74/1.49  
% 6.74/1.49  fof(f16,plain,(
% 6.74/1.49    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 6.74/1.49    inference(ennf_transformation,[],[f6])).
% 6.74/1.49  
% 6.74/1.49  fof(f46,plain,(
% 6.74/1.49    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 6.74/1.49    inference(cnf_transformation,[],[f16])).
% 6.74/1.49  
% 6.74/1.49  fof(f10,axiom,(
% 6.74/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,X3) & v3_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 6.74/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.74/1.49  
% 6.74/1.49  fof(f13,plain,(
% 6.74/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,X3)) & r2_hidden(X2,X1))))))),
% 6.74/1.49    inference(pure_predicate_removal,[],[f10])).
% 6.74/1.49  
% 6.74/1.49  fof(f21,plain,(
% 6.74/1.49    ! [X0] : (! [X1] : ((! [X2] : ((? [X3] : (k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v2_tex_2(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.74/1.49    inference(ennf_transformation,[],[f13])).
% 6.74/1.49  
% 6.74/1.49  fof(f22,plain,(
% 6.74/1.49    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.74/1.49    inference(flattening,[],[f21])).
% 6.74/1.49  
% 6.74/1.49  fof(f33,plain,(
% 6.74/1.49    ! [X2,X1,X0] : (? [X3] : (k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,sK2(X0,X1,X2)) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 6.74/1.49    introduced(choice_axiom,[])).
% 6.74/1.49  
% 6.74/1.49  fof(f34,plain,(
% 6.74/1.49    ! [X0] : (! [X1] : (! [X2] : ((k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,sK2(X0,X1,X2)) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.74/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f33])).
% 6.74/1.49  
% 6.74/1.49  fof(f56,plain,(
% 6.74/1.49    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 6.74/1.49    inference(cnf_transformation,[],[f34])).
% 6.74/1.49  
% 6.74/1.49  fof(f62,plain,(
% 6.74/1.49    r2_hidden(sK5,sK4)),
% 6.74/1.49    inference(cnf_transformation,[],[f38])).
% 6.74/1.49  
% 6.74/1.49  fof(f8,axiom,(
% 6.74/1.49    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 6.74/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.74/1.49  
% 6.74/1.49  fof(f17,plain,(
% 6.74/1.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 6.74/1.49    inference(ennf_transformation,[],[f8])).
% 6.74/1.49  
% 6.74/1.49  fof(f18,plain,(
% 6.74/1.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 6.74/1.49    inference(flattening,[],[f17])).
% 6.74/1.49  
% 6.74/1.49  fof(f49,plain,(
% 6.74/1.49    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 6.74/1.49    inference(cnf_transformation,[],[f18])).
% 6.74/1.49  
% 6.74/1.49  fof(f60,plain,(
% 6.74/1.49    v2_tex_2(sK4,sK3)),
% 6.74/1.49    inference(cnf_transformation,[],[f38])).
% 6.74/1.49  
% 6.74/1.49  fof(f61,plain,(
% 6.74/1.49    m1_subset_1(sK5,u1_struct_0(sK3))),
% 6.74/1.49    inference(cnf_transformation,[],[f38])).
% 6.74/1.49  
% 6.74/1.49  fof(f57,plain,(
% 6.74/1.49    ( ! [X2,X0,X1] : (k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,sK2(X0,X1,X2)) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 6.74/1.49    inference(cnf_transformation,[],[f34])).
% 6.74/1.49  
% 6.74/1.49  fof(f2,axiom,(
% 6.74/1.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 6.74/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.74/1.49  
% 6.74/1.49  fof(f42,plain,(
% 6.74/1.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 6.74/1.49    inference(cnf_transformation,[],[f2])).
% 6.74/1.49  
% 6.74/1.49  fof(f3,axiom,(
% 6.74/1.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)),
% 6.74/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.74/1.49  
% 6.74/1.49  fof(f43,plain,(
% 6.74/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 6.74/1.49    inference(cnf_transformation,[],[f3])).
% 6.74/1.49  
% 6.74/1.49  fof(f64,plain,(
% 6.74/1.49    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 6.74/1.49    inference(definition_unfolding,[],[f42,f43])).
% 6.74/1.49  
% 6.74/1.49  fof(f65,plain,(
% 6.74/1.49    ( ! [X2,X0,X1] : (k2_enumset1(X2,X2,X2,X2) = k9_subset_1(u1_struct_0(X0),X1,sK2(X0,X1,X2)) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 6.74/1.49    inference(definition_unfolding,[],[f57,f64])).
% 6.74/1.49  
% 6.74/1.49  fof(f1,axiom,(
% 6.74/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 6.74/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.74/1.49  
% 6.74/1.49  fof(f25,plain,(
% 6.74/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.74/1.49    inference(nnf_transformation,[],[f1])).
% 6.74/1.49  
% 6.74/1.49  fof(f26,plain,(
% 6.74/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.74/1.49    inference(flattening,[],[f25])).
% 6.74/1.49  
% 6.74/1.49  fof(f40,plain,(
% 6.74/1.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 6.74/1.49    inference(cnf_transformation,[],[f26])).
% 6.74/1.49  
% 6.74/1.49  fof(f67,plain,(
% 6.74/1.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 6.74/1.49    inference(equality_resolution,[],[f40])).
% 6.74/1.49  
% 6.74/1.49  fof(f5,axiom,(
% 6.74/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 6.74/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.74/1.49  
% 6.74/1.49  fof(f15,plain,(
% 6.74/1.49    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 6.74/1.49    inference(ennf_transformation,[],[f5])).
% 6.74/1.49  
% 6.74/1.49  fof(f45,plain,(
% 6.74/1.49    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 6.74/1.49    inference(cnf_transformation,[],[f15])).
% 6.74/1.49  
% 6.74/1.49  fof(f52,plain,(
% 6.74/1.49    ( ! [X4,X0,X1] : (k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4 | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 6.74/1.49    inference(cnf_transformation,[],[f32])).
% 6.74/1.49  
% 6.74/1.49  fof(f63,plain,(
% 6.74/1.49    ( ! [X3] : (k1_tarski(sK5) != k9_subset_1(u1_struct_0(sK3),sK4,X3) | ~v4_pre_topc(X3,sK3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))) )),
% 6.74/1.49    inference(cnf_transformation,[],[f38])).
% 6.74/1.49  
% 6.74/1.49  fof(f66,plain,(
% 6.74/1.49    ( ! [X3] : (k2_enumset1(sK5,sK5,sK5,sK5) != k9_subset_1(u1_struct_0(sK3),sK4,X3) | ~v4_pre_topc(X3,sK3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))) )),
% 6.74/1.49    inference(definition_unfolding,[],[f63,f64])).
% 6.74/1.49  
% 6.74/1.49  fof(f50,plain,(
% 6.74/1.49    ( ! [X4,X0,X1] : (m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 6.74/1.49    inference(cnf_transformation,[],[f32])).
% 6.74/1.49  
% 6.74/1.49  cnf(c_13,plain,
% 6.74/1.49      ( v4_pre_topc(sK1(X0,X1,X2),X0)
% 6.74/1.49      | ~ v2_tex_2(X1,X0)
% 6.74/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 6.74/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 6.74/1.49      | ~ r1_tarski(X2,X1)
% 6.74/1.49      | ~ l1_pre_topc(X0) ),
% 6.74/1.49      inference(cnf_transformation,[],[f51]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_22,negated_conjecture,
% 6.74/1.49      ( l1_pre_topc(sK3) ),
% 6.74/1.49      inference(cnf_transformation,[],[f58]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_477,plain,
% 6.74/1.49      ( v4_pre_topc(sK1(X0,X1,X2),X0)
% 6.74/1.49      | ~ v2_tex_2(X1,X0)
% 6.74/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 6.74/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 6.74/1.49      | ~ r1_tarski(X2,X1)
% 6.74/1.49      | sK3 != X0 ),
% 6.74/1.49      inference(resolution_lifted,[status(thm)],[c_13,c_22]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_478,plain,
% 6.74/1.49      ( v4_pre_topc(sK1(sK3,X0,X1),sK3)
% 6.74/1.49      | ~ v2_tex_2(X0,sK3)
% 6.74/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 6.74/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 6.74/1.49      | ~ r1_tarski(X1,X0) ),
% 6.74/1.49      inference(unflattening,[status(thm)],[c_477]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_2016,plain,
% 6.74/1.49      ( v4_pre_topc(sK1(sK3,X0,X1),sK3) = iProver_top
% 6.74/1.49      | v2_tex_2(X0,sK3) != iProver_top
% 6.74/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 6.74/1.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 6.74/1.49      | r1_tarski(X1,X0) != iProver_top ),
% 6.74/1.49      inference(predicate_to_equality,[status(thm)],[c_478]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_6,plain,
% 6.74/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 6.74/1.49      inference(cnf_transformation,[],[f48]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_2027,plain,
% 6.74/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 6.74/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 6.74/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_21,negated_conjecture,
% 6.74/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 6.74/1.49      inference(cnf_transformation,[],[f59]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_2022,plain,
% 6.74/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 6.74/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_7,plain,
% 6.74/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 6.74/1.49      inference(cnf_transformation,[],[f47]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_2026,plain,
% 6.74/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 6.74/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 6.74/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_2509,plain,
% 6.74/1.49      ( r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
% 6.74/1.49      inference(superposition,[status(thm)],[c_2022,c_2026]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_3,plain,
% 6.74/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 6.74/1.49      | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
% 6.74/1.49      inference(cnf_transformation,[],[f44]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_178,plain,
% 6.74/1.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 6.74/1.49      inference(prop_impl,[status(thm)],[c_6]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_179,plain,
% 6.74/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 6.74/1.49      inference(renaming,[status(thm)],[c_178]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_224,plain,
% 6.74/1.49      ( ~ r1_tarski(X0,X1)
% 6.74/1.49      | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
% 6.74/1.49      inference(bin_hyper_res,[status(thm)],[c_3,c_179]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_2021,plain,
% 6.74/1.49      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
% 6.74/1.49      | r1_tarski(X1,X0) != iProver_top ),
% 6.74/1.49      inference(predicate_to_equality,[status(thm)],[c_224]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_4430,plain,
% 6.74/1.49      ( k9_subset_1(u1_struct_0(sK3),X0,sK4) = k9_subset_1(u1_struct_0(sK3),sK4,X0) ),
% 6.74/1.49      inference(superposition,[status(thm)],[c_2509,c_2021]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_5,plain,
% 6.74/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 6.74/1.49      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 6.74/1.49      inference(cnf_transformation,[],[f46]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_226,plain,
% 6.74/1.49      ( ~ r1_tarski(X0,X1) | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 6.74/1.49      inference(bin_hyper_res,[status(thm)],[c_5,c_179]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_2019,plain,
% 6.74/1.49      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
% 6.74/1.49      | r1_tarski(X2,X0) != iProver_top ),
% 6.74/1.49      inference(predicate_to_equality,[status(thm)],[c_226]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_3717,plain,
% 6.74/1.49      ( k9_subset_1(u1_struct_0(sK3),X0,sK4) = k3_xboole_0(X0,sK4) ),
% 6.74/1.49      inference(superposition,[status(thm)],[c_2509,c_2019]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_4436,plain,
% 6.74/1.49      ( k9_subset_1(u1_struct_0(sK3),sK4,X0) = k3_xboole_0(X0,sK4) ),
% 6.74/1.49      inference(light_normalisation,[status(thm)],[c_4430,c_3717]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_16,plain,
% 6.74/1.49      ( ~ v2_tex_2(X0,X1)
% 6.74/1.49      | ~ r2_hidden(X2,X0)
% 6.74/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 6.74/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 6.74/1.49      | m1_subset_1(sK2(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 6.74/1.49      | ~ l1_pre_topc(X1) ),
% 6.74/1.49      inference(cnf_transformation,[],[f56]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_18,negated_conjecture,
% 6.74/1.49      ( r2_hidden(sK5,sK4) ),
% 6.74/1.49      inference(cnf_transformation,[],[f62]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_326,plain,
% 6.74/1.49      ( ~ v2_tex_2(X0,X1)
% 6.74/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 6.74/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 6.74/1.49      | m1_subset_1(sK2(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 6.74/1.49      | ~ l1_pre_topc(X1)
% 6.74/1.49      | sK4 != X0
% 6.74/1.49      | sK5 != X2 ),
% 6.74/1.49      inference(resolution_lifted,[status(thm)],[c_16,c_18]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_327,plain,
% 6.74/1.49      ( ~ v2_tex_2(sK4,X0)
% 6.74/1.49      | m1_subset_1(sK2(X0,sK4,sK5),k1_zfmisc_1(u1_struct_0(X0)))
% 6.74/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
% 6.74/1.49      | ~ m1_subset_1(sK5,u1_struct_0(X0))
% 6.74/1.49      | ~ l1_pre_topc(X0) ),
% 6.74/1.49      inference(unflattening,[status(thm)],[c_326]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_8,plain,
% 6.74/1.49      ( ~ r2_hidden(X0,X1)
% 6.74/1.49      | m1_subset_1(X0,X2)
% 6.74/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 6.74/1.49      inference(cnf_transformation,[],[f49]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_314,plain,
% 6.74/1.49      ( m1_subset_1(X0,X1)
% 6.74/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 6.74/1.49      | sK4 != X2
% 6.74/1.49      | sK5 != X0 ),
% 6.74/1.49      inference(resolution_lifted,[status(thm)],[c_8,c_18]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_315,plain,
% 6.74/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0)) | m1_subset_1(sK5,X0) ),
% 6.74/1.50      inference(unflattening,[status(thm)],[c_314]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_336,plain,
% 6.74/1.50      ( ~ v2_tex_2(sK4,X0)
% 6.74/1.50      | m1_subset_1(sK2(X0,sK4,sK5),k1_zfmisc_1(u1_struct_0(X0)))
% 6.74/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
% 6.74/1.50      | ~ l1_pre_topc(X0) ),
% 6.74/1.50      inference(forward_subsumption_resolution,
% 6.74/1.50                [status(thm)],
% 6.74/1.50                [c_327,c_315]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_466,plain,
% 6.74/1.50      ( ~ v2_tex_2(sK4,X0)
% 6.74/1.50      | m1_subset_1(sK2(X0,sK4,sK5),k1_zfmisc_1(u1_struct_0(X0)))
% 6.74/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
% 6.74/1.50      | sK3 != X0 ),
% 6.74/1.50      inference(resolution_lifted,[status(thm)],[c_336,c_22]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_467,plain,
% 6.74/1.50      ( ~ v2_tex_2(sK4,sK3)
% 6.74/1.50      | m1_subset_1(sK2(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 6.74/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 6.74/1.50      inference(unflattening,[status(thm)],[c_466]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_20,negated_conjecture,
% 6.74/1.50      ( v2_tex_2(sK4,sK3) ),
% 6.74/1.50      inference(cnf_transformation,[],[f60]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_19,negated_conjecture,
% 6.74/1.50      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 6.74/1.50      inference(cnf_transformation,[],[f61]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_329,plain,
% 6.74/1.50      ( ~ v2_tex_2(sK4,sK3)
% 6.74/1.50      | m1_subset_1(sK2(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 6.74/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 6.74/1.50      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 6.74/1.50      | ~ l1_pre_topc(sK3) ),
% 6.74/1.50      inference(instantiation,[status(thm)],[c_327]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_469,plain,
% 6.74/1.50      ( m1_subset_1(sK2(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 6.74/1.50      inference(global_propositional_subsumption,
% 6.74/1.50                [status(thm)],
% 6.74/1.50                [c_467,c_22,c_21,c_20,c_19,c_329]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_2017,plain,
% 6.74/1.50      ( m1_subset_1(sK2(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 6.74/1.50      inference(predicate_to_equality,[status(thm)],[c_469]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_2510,plain,
% 6.74/1.50      ( r1_tarski(sK2(sK3,sK4,sK5),u1_struct_0(sK3)) = iProver_top ),
% 6.74/1.50      inference(superposition,[status(thm)],[c_2017,c_2026]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_3718,plain,
% 6.74/1.50      ( k9_subset_1(u1_struct_0(sK3),X0,sK2(sK3,sK4,sK5)) = k3_xboole_0(X0,sK2(sK3,sK4,sK5)) ),
% 6.74/1.50      inference(superposition,[status(thm)],[c_2510,c_2019]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_8629,plain,
% 6.74/1.50      ( k3_xboole_0(sK2(sK3,sK4,sK5),sK4) = k3_xboole_0(sK4,sK2(sK3,sK4,sK5)) ),
% 6.74/1.50      inference(superposition,[status(thm)],[c_4436,c_3718]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_15,plain,
% 6.74/1.50      ( ~ v2_tex_2(X0,X1)
% 6.74/1.50      | ~ r2_hidden(X2,X0)
% 6.74/1.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 6.74/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 6.74/1.50      | ~ l1_pre_topc(X1)
% 6.74/1.50      | k9_subset_1(u1_struct_0(X1),X0,sK2(X1,X0,X2)) = k2_enumset1(X2,X2,X2,X2) ),
% 6.74/1.50      inference(cnf_transformation,[],[f65]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_348,plain,
% 6.74/1.50      ( ~ v2_tex_2(X0,X1)
% 6.74/1.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 6.74/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 6.74/1.50      | ~ l1_pre_topc(X1)
% 6.74/1.50      | k9_subset_1(u1_struct_0(X1),X0,sK2(X1,X0,X2)) = k2_enumset1(X2,X2,X2,X2)
% 6.74/1.50      | sK4 != X0
% 6.74/1.50      | sK5 != X2 ),
% 6.74/1.50      inference(resolution_lifted,[status(thm)],[c_15,c_18]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_349,plain,
% 6.74/1.50      ( ~ v2_tex_2(sK4,X0)
% 6.74/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
% 6.74/1.50      | ~ m1_subset_1(sK5,u1_struct_0(X0))
% 6.74/1.50      | ~ l1_pre_topc(X0)
% 6.74/1.50      | k9_subset_1(u1_struct_0(X0),sK4,sK2(X0,sK4,sK5)) = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 6.74/1.50      inference(unflattening,[status(thm)],[c_348]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_358,plain,
% 6.74/1.50      ( ~ v2_tex_2(sK4,X0)
% 6.74/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
% 6.74/1.50      | ~ l1_pre_topc(X0)
% 6.74/1.50      | k9_subset_1(u1_struct_0(X0),sK4,sK2(X0,sK4,sK5)) = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 6.74/1.50      inference(forward_subsumption_resolution,
% 6.74/1.50                [status(thm)],
% 6.74/1.50                [c_349,c_315]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_458,plain,
% 6.74/1.50      ( ~ v2_tex_2(sK4,X0)
% 6.74/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
% 6.74/1.50      | k9_subset_1(u1_struct_0(X0),sK4,sK2(X0,sK4,sK5)) = k2_enumset1(sK5,sK5,sK5,sK5)
% 6.74/1.50      | sK3 != X0 ),
% 6.74/1.50      inference(resolution_lifted,[status(thm)],[c_358,c_22]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_459,plain,
% 6.74/1.50      ( ~ v2_tex_2(sK4,sK3)
% 6.74/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 6.74/1.50      | k9_subset_1(u1_struct_0(sK3),sK4,sK2(sK3,sK4,sK5)) = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 6.74/1.50      inference(unflattening,[status(thm)],[c_458]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_351,plain,
% 6.74/1.50      ( ~ v2_tex_2(sK4,sK3)
% 6.74/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 6.74/1.50      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 6.74/1.50      | ~ l1_pre_topc(sK3)
% 6.74/1.50      | k9_subset_1(u1_struct_0(sK3),sK4,sK2(sK3,sK4,sK5)) = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 6.74/1.50      inference(instantiation,[status(thm)],[c_349]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_461,plain,
% 6.74/1.50      ( k9_subset_1(u1_struct_0(sK3),sK4,sK2(sK3,sK4,sK5)) = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 6.74/1.50      inference(global_propositional_subsumption,
% 6.74/1.50                [status(thm)],
% 6.74/1.50                [c_459,c_22,c_21,c_20,c_19,c_351]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_7674,plain,
% 6.74/1.50      ( k3_xboole_0(sK4,sK2(sK3,sK4,sK5)) = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 6.74/1.50      inference(superposition,[status(thm)],[c_3718,c_461]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_8632,plain,
% 6.74/1.50      ( k3_xboole_0(sK2(sK3,sK4,sK5),sK4) = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 6.74/1.50      inference(light_normalisation,[status(thm)],[c_8629,c_7674]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_1,plain,
% 6.74/1.50      ( r1_tarski(X0,X0) ),
% 6.74/1.50      inference(cnf_transformation,[],[f67]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_2028,plain,
% 6.74/1.50      ( r1_tarski(X0,X0) = iProver_top ),
% 6.74/1.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_3716,plain,
% 6.74/1.50      ( k9_subset_1(X0,X1,X0) = k3_xboole_0(X1,X0) ),
% 6.74/1.50      inference(superposition,[status(thm)],[c_2028,c_2019]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_4,plain,
% 6.74/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 6.74/1.50      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 6.74/1.50      inference(cnf_transformation,[],[f45]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_225,plain,
% 6.74/1.50      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
% 6.74/1.50      | ~ r1_tarski(X2,X0) ),
% 6.74/1.50      inference(bin_hyper_res,[status(thm)],[c_4,c_179]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_2020,plain,
% 6.74/1.50      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
% 6.74/1.50      | r1_tarski(X2,X0) != iProver_top ),
% 6.74/1.50      inference(predicate_to_equality,[status(thm)],[c_225]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_3796,plain,
% 6.74/1.50      ( m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X1)) = iProver_top
% 6.74/1.50      | r1_tarski(X1,X1) != iProver_top ),
% 6.74/1.50      inference(superposition,[status(thm)],[c_3716,c_2020]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_10947,plain,
% 6.74/1.50      ( m1_subset_1(k2_enumset1(sK5,sK5,sK5,sK5),k1_zfmisc_1(sK4)) = iProver_top
% 6.74/1.50      | r1_tarski(sK4,sK4) != iProver_top ),
% 6.74/1.50      inference(superposition,[status(thm)],[c_8632,c_3796]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_2168,plain,
% 6.74/1.50      ( r1_tarski(sK4,sK4) ),
% 6.74/1.50      inference(instantiation,[status(thm)],[c_1]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_2169,plain,
% 6.74/1.50      ( r1_tarski(sK4,sK4) = iProver_top ),
% 6.74/1.50      inference(predicate_to_equality,[status(thm)],[c_2168]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_15163,plain,
% 6.74/1.50      ( m1_subset_1(k2_enumset1(sK5,sK5,sK5,sK5),k1_zfmisc_1(sK4)) = iProver_top ),
% 6.74/1.50      inference(global_propositional_subsumption,
% 6.74/1.50                [status(thm)],
% 6.74/1.50                [c_10947,c_2169]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_15167,plain,
% 6.74/1.50      ( r1_tarski(k2_enumset1(sK5,sK5,sK5,sK5),sK4) = iProver_top ),
% 6.74/1.50      inference(superposition,[status(thm)],[c_15163,c_2026]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_12,plain,
% 6.74/1.50      ( ~ v2_tex_2(X0,X1)
% 6.74/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 6.74/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 6.74/1.50      | ~ r1_tarski(X2,X0)
% 6.74/1.50      | ~ l1_pre_topc(X1)
% 6.74/1.50      | k9_subset_1(u1_struct_0(X1),X0,sK1(X1,X0,X2)) = X2 ),
% 6.74/1.50      inference(cnf_transformation,[],[f52]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_519,plain,
% 6.74/1.50      ( ~ v2_tex_2(X0,X1)
% 6.74/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 6.74/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 6.74/1.50      | ~ r1_tarski(X2,X0)
% 6.74/1.50      | k9_subset_1(u1_struct_0(X1),X0,sK1(X1,X0,X2)) = X2
% 6.74/1.50      | sK3 != X1 ),
% 6.74/1.50      inference(resolution_lifted,[status(thm)],[c_12,c_22]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_520,plain,
% 6.74/1.50      ( ~ v2_tex_2(X0,sK3)
% 6.74/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 6.74/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 6.74/1.50      | ~ r1_tarski(X1,X0)
% 6.74/1.50      | k9_subset_1(u1_struct_0(sK3),X0,sK1(sK3,X0,X1)) = X1 ),
% 6.74/1.50      inference(unflattening,[status(thm)],[c_519]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_2014,plain,
% 6.74/1.50      ( k9_subset_1(u1_struct_0(sK3),X0,sK1(sK3,X0,X1)) = X1
% 6.74/1.50      | v2_tex_2(X0,sK3) != iProver_top
% 6.74/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 6.74/1.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 6.74/1.50      | r1_tarski(X1,X0) != iProver_top ),
% 6.74/1.50      inference(predicate_to_equality,[status(thm)],[c_520]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_2685,plain,
% 6.74/1.50      ( k9_subset_1(u1_struct_0(sK3),sK4,sK1(sK3,sK4,X0)) = X0
% 6.74/1.50      | v2_tex_2(sK4,sK3) != iProver_top
% 6.74/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 6.74/1.50      | r1_tarski(X0,sK4) != iProver_top ),
% 6.74/1.50      inference(superposition,[status(thm)],[c_2022,c_2014]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_24,plain,
% 6.74/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 6.74/1.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_811,plain,
% 6.74/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 6.74/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 6.74/1.50      | ~ r1_tarski(X1,X0)
% 6.74/1.50      | k9_subset_1(u1_struct_0(sK3),X0,sK1(sK3,X0,X1)) = X1
% 6.74/1.50      | sK4 != X0
% 6.74/1.50      | sK3 != sK3 ),
% 6.74/1.50      inference(resolution_lifted,[status(thm)],[c_20,c_520]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_812,plain,
% 6.74/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 6.74/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 6.74/1.50      | ~ r1_tarski(X0,sK4)
% 6.74/1.50      | k9_subset_1(u1_struct_0(sK3),sK4,sK1(sK3,sK4,X0)) = X0 ),
% 6.74/1.50      inference(unflattening,[status(thm)],[c_811]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_813,plain,
% 6.74/1.50      ( k9_subset_1(u1_struct_0(sK3),sK4,sK1(sK3,sK4,X0)) = X0
% 6.74/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 6.74/1.50      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 6.74/1.50      | r1_tarski(X0,sK4) != iProver_top ),
% 6.74/1.50      inference(predicate_to_equality,[status(thm)],[c_812]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_2721,plain,
% 6.74/1.50      ( k9_subset_1(u1_struct_0(sK3),sK4,sK1(sK3,sK4,X0)) = X0
% 6.74/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 6.74/1.50      | r1_tarski(X0,sK4) != iProver_top ),
% 6.74/1.50      inference(global_propositional_subsumption,
% 6.74/1.50                [status(thm)],
% 6.74/1.50                [c_2685,c_24,c_813]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_3799,plain,
% 6.74/1.50      ( k9_subset_1(u1_struct_0(sK3),sK4,sK1(sK3,sK4,k9_subset_1(u1_struct_0(sK3),X0,X1))) = k9_subset_1(u1_struct_0(sK3),X0,X1)
% 6.74/1.50      | r1_tarski(X1,u1_struct_0(sK3)) != iProver_top
% 6.74/1.50      | r1_tarski(k9_subset_1(u1_struct_0(sK3),X0,X1),sK4) != iProver_top ),
% 6.74/1.50      inference(superposition,[status(thm)],[c_2020,c_2721]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_4684,plain,
% 6.74/1.50      ( k3_xboole_0(sK1(sK3,sK4,k9_subset_1(u1_struct_0(sK3),X0,X1)),sK4) = k9_subset_1(u1_struct_0(sK3),X0,X1)
% 6.74/1.50      | r1_tarski(X1,u1_struct_0(sK3)) != iProver_top
% 6.74/1.50      | r1_tarski(k9_subset_1(u1_struct_0(sK3),X0,X1),sK4) != iProver_top ),
% 6.74/1.50      inference(demodulation,[status(thm)],[c_3799,c_4436]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_4688,plain,
% 6.74/1.50      ( k3_xboole_0(sK1(sK3,sK4,k9_subset_1(u1_struct_0(sK3),sK4,sK2(sK3,sK4,sK5))),sK4) = k9_subset_1(u1_struct_0(sK3),sK4,sK2(sK3,sK4,sK5))
% 6.74/1.50      | r1_tarski(k2_enumset1(sK5,sK5,sK5,sK5),sK4) != iProver_top
% 6.74/1.50      | r1_tarski(sK2(sK3,sK4,sK5),u1_struct_0(sK3)) != iProver_top ),
% 6.74/1.50      inference(superposition,[status(thm)],[c_461,c_4684]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_4697,plain,
% 6.74/1.50      ( k3_xboole_0(sK1(sK3,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK4) = k2_enumset1(sK5,sK5,sK5,sK5)
% 6.74/1.50      | r1_tarski(k2_enumset1(sK5,sK5,sK5,sK5),sK4) != iProver_top
% 6.74/1.50      | r1_tarski(sK2(sK3,sK4,sK5),u1_struct_0(sK3)) != iProver_top ),
% 6.74/1.50      inference(light_normalisation,[status(thm)],[c_4688,c_461]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_23,plain,
% 6.74/1.50      ( l1_pre_topc(sK3) = iProver_top ),
% 6.74/1.50      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_25,plain,
% 6.74/1.50      ( v2_tex_2(sK4,sK3) = iProver_top ),
% 6.74/1.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_26,plain,
% 6.74/1.50      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 6.74/1.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_328,plain,
% 6.74/1.50      ( v2_tex_2(sK4,X0) != iProver_top
% 6.74/1.50      | m1_subset_1(sK2(X0,sK4,sK5),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 6.74/1.50      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 6.74/1.50      | m1_subset_1(sK5,u1_struct_0(X0)) != iProver_top
% 6.74/1.50      | l1_pre_topc(X0) != iProver_top ),
% 6.74/1.50      inference(predicate_to_equality,[status(thm)],[c_327]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_330,plain,
% 6.74/1.50      ( v2_tex_2(sK4,sK3) != iProver_top
% 6.74/1.50      | m1_subset_1(sK2(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 6.74/1.50      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 6.74/1.50      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 6.74/1.50      | l1_pre_topc(sK3) != iProver_top ),
% 6.74/1.50      inference(instantiation,[status(thm)],[c_328]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_2185,plain,
% 6.74/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 6.74/1.50      | r1_tarski(X0,u1_struct_0(sK3)) ),
% 6.74/1.50      inference(instantiation,[status(thm)],[c_7]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_2411,plain,
% 6.74/1.50      ( ~ m1_subset_1(sK2(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 6.74/1.50      | r1_tarski(sK2(sK3,sK4,sK5),u1_struct_0(sK3)) ),
% 6.74/1.50      inference(instantiation,[status(thm)],[c_2185]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_2412,plain,
% 6.74/1.50      ( m1_subset_1(sK2(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 6.74/1.50      | r1_tarski(sK2(sK3,sK4,sK5),u1_struct_0(sK3)) = iProver_top ),
% 6.74/1.50      inference(predicate_to_equality,[status(thm)],[c_2411]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_5009,plain,
% 6.74/1.50      ( r1_tarski(k2_enumset1(sK5,sK5,sK5,sK5),sK4) != iProver_top
% 6.74/1.50      | k3_xboole_0(sK1(sK3,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK4) = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 6.74/1.50      inference(global_propositional_subsumption,
% 6.74/1.50                [status(thm)],
% 6.74/1.50                [c_4697,c_23,c_24,c_25,c_26,c_330,c_2412]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_5010,plain,
% 6.74/1.50      ( k3_xboole_0(sK1(sK3,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK4) = k2_enumset1(sK5,sK5,sK5,sK5)
% 6.74/1.50      | r1_tarski(k2_enumset1(sK5,sK5,sK5,sK5),sK4) != iProver_top ),
% 6.74/1.50      inference(renaming,[status(thm)],[c_5009]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_15883,plain,
% 6.74/1.50      ( k3_xboole_0(sK1(sK3,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK4) = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 6.74/1.50      inference(superposition,[status(thm)],[c_15167,c_5010]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_17,negated_conjecture,
% 6.74/1.50      ( ~ v4_pre_topc(X0,sK3)
% 6.74/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 6.74/1.50      | k2_enumset1(sK5,sK5,sK5,sK5) != k9_subset_1(u1_struct_0(sK3),sK4,X0) ),
% 6.74/1.50      inference(cnf_transformation,[],[f66]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_2025,plain,
% 6.74/1.50      ( k2_enumset1(sK5,sK5,sK5,sK5) != k9_subset_1(u1_struct_0(sK3),sK4,X0)
% 6.74/1.50      | v4_pre_topc(X0,sK3) != iProver_top
% 6.74/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 6.74/1.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_8592,plain,
% 6.74/1.50      ( k2_enumset1(sK5,sK5,sK5,sK5) != k3_xboole_0(X0,sK4)
% 6.74/1.50      | v4_pre_topc(X0,sK3) != iProver_top
% 6.74/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 6.74/1.50      inference(demodulation,[status(thm)],[c_4436,c_2025]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_16260,plain,
% 6.74/1.50      ( v4_pre_topc(sK1(sK3,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK3) != iProver_top
% 6.74/1.50      | m1_subset_1(sK1(sK3,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 6.74/1.50      inference(superposition,[status(thm)],[c_15883,c_8592]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_16540,plain,
% 6.74/1.50      ( v4_pre_topc(sK1(sK3,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK3) != iProver_top
% 6.74/1.50      | r1_tarski(sK1(sK3,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),u1_struct_0(sK3)) != iProver_top ),
% 6.74/1.50      inference(superposition,[status(thm)],[c_2027,c_16260]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_3794,plain,
% 6.74/1.50      ( m1_subset_1(k2_enumset1(sK5,sK5,sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 6.74/1.50      | r1_tarski(sK2(sK3,sK4,sK5),u1_struct_0(sK3)) != iProver_top ),
% 6.74/1.50      inference(superposition,[status(thm)],[c_461,c_2020]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_14,plain,
% 6.74/1.50      ( ~ v2_tex_2(X0,X1)
% 6.74/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 6.74/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 6.74/1.50      | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 6.74/1.50      | ~ r1_tarski(X2,X0)
% 6.74/1.50      | ~ l1_pre_topc(X1) ),
% 6.74/1.50      inference(cnf_transformation,[],[f50]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_498,plain,
% 6.74/1.50      ( ~ v2_tex_2(X0,X1)
% 6.74/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 6.74/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 6.74/1.50      | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 6.74/1.50      | ~ r1_tarski(X2,X0)
% 6.74/1.50      | sK3 != X1 ),
% 6.74/1.50      inference(resolution_lifted,[status(thm)],[c_14,c_22]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_499,plain,
% 6.74/1.50      ( ~ v2_tex_2(X0,sK3)
% 6.74/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 6.74/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 6.74/1.50      | m1_subset_1(sK1(sK3,X0,X1),k1_zfmisc_1(u1_struct_0(sK3)))
% 6.74/1.50      | ~ r1_tarski(X1,X0) ),
% 6.74/1.50      inference(unflattening,[status(thm)],[c_498]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_2015,plain,
% 6.74/1.50      ( v2_tex_2(X0,sK3) != iProver_top
% 6.74/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 6.74/1.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 6.74/1.50      | m1_subset_1(sK1(sK3,X0,X1),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 6.74/1.50      | r1_tarski(X1,X0) != iProver_top ),
% 6.74/1.50      inference(predicate_to_equality,[status(thm)],[c_499]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_16541,plain,
% 6.74/1.50      ( v4_pre_topc(sK1(sK3,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK3) != iProver_top
% 6.74/1.50      | v2_tex_2(sK4,sK3) != iProver_top
% 6.74/1.50      | m1_subset_1(k2_enumset1(sK5,sK5,sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 6.74/1.50      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 6.74/1.50      | r1_tarski(k2_enumset1(sK5,sK5,sK5,sK5),sK4) != iProver_top ),
% 6.74/1.50      inference(superposition,[status(thm)],[c_2015,c_16260]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_16904,plain,
% 6.74/1.50      ( v4_pre_topc(sK1(sK3,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK3) != iProver_top ),
% 6.74/1.50      inference(global_propositional_subsumption,
% 6.74/1.50                [status(thm)],
% 6.74/1.50                [c_16540,c_23,c_24,c_25,c_26,c_330,c_2412,c_3794,c_15167,
% 6.74/1.50                 c_16541]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(c_16908,plain,
% 6.74/1.50      ( v2_tex_2(sK4,sK3) != iProver_top
% 6.74/1.50      | m1_subset_1(k2_enumset1(sK5,sK5,sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 6.74/1.50      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 6.74/1.50      | r1_tarski(k2_enumset1(sK5,sK5,sK5,sK5),sK4) != iProver_top ),
% 6.74/1.50      inference(superposition,[status(thm)],[c_2016,c_16904]) ).
% 6.74/1.50  
% 6.74/1.50  cnf(contradiction,plain,
% 6.74/1.50      ( $false ),
% 6.74/1.50      inference(minisat,
% 6.74/1.50                [status(thm)],
% 6.74/1.50                [c_16908,c_15167,c_3794,c_2412,c_330,c_26,c_25,c_24,c_23]) ).
% 6.74/1.50  
% 6.74/1.50  
% 6.74/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 6.74/1.50  
% 6.74/1.50  ------                               Statistics
% 6.74/1.50  
% 6.74/1.50  ------ General
% 6.74/1.50  
% 6.74/1.50  abstr_ref_over_cycles:                  0
% 6.74/1.50  abstr_ref_under_cycles:                 0
% 6.74/1.50  gc_basic_clause_elim:                   0
% 6.74/1.50  forced_gc_time:                         0
% 6.74/1.50  parsing_time:                           0.007
% 6.74/1.50  unif_index_cands_time:                  0.
% 6.74/1.50  unif_index_add_time:                    0.
% 6.74/1.50  orderings_time:                         0.
% 6.74/1.50  out_proof_time:                         0.011
% 6.74/1.50  total_time:                             0.541
% 6.74/1.50  num_of_symbols:                         48
% 6.74/1.50  num_of_terms:                           19276
% 6.74/1.50  
% 6.74/1.50  ------ Preprocessing
% 6.74/1.50  
% 6.74/1.50  num_of_splits:                          0
% 6.74/1.50  num_of_split_atoms:                     0
% 6.74/1.50  num_of_reused_defs:                     0
% 6.74/1.50  num_eq_ax_congr_red:                    23
% 6.74/1.50  num_of_sem_filtered_clauses:            1
% 6.74/1.50  num_of_subtypes:                        0
% 6.74/1.50  monotx_restored_types:                  0
% 6.74/1.50  sat_num_of_epr_types:                   0
% 6.74/1.50  sat_num_of_non_cyclic_types:            0
% 6.74/1.50  sat_guarded_non_collapsed_types:        0
% 6.74/1.50  num_pure_diseq_elim:                    0
% 6.74/1.50  simp_replaced_by:                       0
% 6.74/1.50  res_preprocessed:                       109
% 6.74/1.50  prep_upred:                             0
% 6.74/1.50  prep_unflattend:                        34
% 6.74/1.50  smt_new_axioms:                         0
% 6.74/1.50  pred_elim_cands:                        4
% 6.74/1.50  pred_elim:                              2
% 6.74/1.50  pred_elim_cl:                           2
% 6.74/1.50  pred_elim_cycles:                       7
% 6.74/1.50  merged_defs:                            8
% 6.74/1.50  merged_defs_ncl:                        0
% 6.74/1.50  bin_hyper_res:                          11
% 6.74/1.50  prep_cycles:                            4
% 6.74/1.50  pred_elim_time:                         0.015
% 6.74/1.50  splitting_time:                         0.
% 6.74/1.50  sem_filter_time:                        0.
% 6.74/1.50  monotx_time:                            0.
% 6.74/1.50  subtype_inf_time:                       0.
% 6.74/1.50  
% 6.74/1.50  ------ Problem properties
% 6.74/1.50  
% 6.74/1.50  clauses:                                20
% 6.74/1.50  conjectures:                            4
% 6.74/1.50  epr:                                    3
% 6.74/1.50  horn:                                   18
% 6.74/1.50  ground:                                 5
% 6.74/1.50  unary:                                  6
% 6.74/1.50  binary:                                 6
% 6.74/1.50  lits:                                   50
% 6.74/1.50  lits_eq:                                7
% 6.74/1.50  fd_pure:                                0
% 6.74/1.50  fd_pseudo:                              0
% 6.74/1.50  fd_cond:                                0
% 6.74/1.50  fd_pseudo_cond:                         1
% 6.74/1.50  ac_symbols:                             0
% 6.74/1.50  
% 6.74/1.50  ------ Propositional Solver
% 6.74/1.50  
% 6.74/1.50  prop_solver_calls:                      31
% 6.74/1.50  prop_fast_solver_calls:                 1858
% 6.74/1.50  smt_solver_calls:                       0
% 6.74/1.50  smt_fast_solver_calls:                  0
% 6.74/1.50  prop_num_of_clauses:                    7843
% 6.74/1.50  prop_preprocess_simplified:             14029
% 6.74/1.50  prop_fo_subsumed:                       67
% 6.74/1.50  prop_solver_time:                       0.
% 6.74/1.50  smt_solver_time:                        0.
% 6.74/1.50  smt_fast_solver_time:                   0.
% 6.74/1.50  prop_fast_solver_time:                  0.
% 6.74/1.50  prop_unsat_core_time:                   0.
% 6.74/1.50  
% 6.74/1.50  ------ QBF
% 6.74/1.50  
% 6.74/1.50  qbf_q_res:                              0
% 6.74/1.50  qbf_num_tautologies:                    0
% 6.74/1.50  qbf_prep_cycles:                        0
% 6.74/1.50  
% 6.74/1.50  ------ BMC1
% 6.74/1.50  
% 6.74/1.50  bmc1_current_bound:                     -1
% 6.74/1.50  bmc1_last_solved_bound:                 -1
% 6.74/1.50  bmc1_unsat_core_size:                   -1
% 6.74/1.50  bmc1_unsat_core_parents_size:           -1
% 6.74/1.50  bmc1_merge_next_fun:                    0
% 6.74/1.50  bmc1_unsat_core_clauses_time:           0.
% 6.74/1.50  
% 6.74/1.50  ------ Instantiation
% 6.74/1.50  
% 6.74/1.50  inst_num_of_clauses:                    1962
% 6.74/1.50  inst_num_in_passive:                    13
% 6.74/1.50  inst_num_in_active:                     995
% 6.74/1.50  inst_num_in_unprocessed:                954
% 6.74/1.50  inst_num_of_loops:                      1170
% 6.74/1.50  inst_num_of_learning_restarts:          0
% 6.74/1.50  inst_num_moves_active_passive:          171
% 6.74/1.50  inst_lit_activity:                      0
% 6.74/1.50  inst_lit_activity_moves:                1
% 6.74/1.50  inst_num_tautologies:                   0
% 6.74/1.50  inst_num_prop_implied:                  0
% 6.74/1.50  inst_num_existing_simplified:           0
% 6.74/1.50  inst_num_eq_res_simplified:             0
% 6.74/1.50  inst_num_child_elim:                    0
% 6.74/1.50  inst_num_of_dismatching_blockings:      893
% 6.74/1.50  inst_num_of_non_proper_insts:           2944
% 6.74/1.50  inst_num_of_duplicates:                 0
% 6.74/1.50  inst_inst_num_from_inst_to_res:         0
% 6.74/1.50  inst_dismatching_checking_time:         0.
% 6.74/1.50  
% 6.74/1.50  ------ Resolution
% 6.74/1.50  
% 6.74/1.50  res_num_of_clauses:                     0
% 6.74/1.50  res_num_in_passive:                     0
% 6.74/1.50  res_num_in_active:                      0
% 6.74/1.50  res_num_of_loops:                       113
% 6.74/1.50  res_forward_subset_subsumed:            191
% 6.74/1.50  res_backward_subset_subsumed:           0
% 6.74/1.50  res_forward_subsumed:                   0
% 6.74/1.50  res_backward_subsumed:                  0
% 6.74/1.50  res_forward_subsumption_resolution:     4
% 6.74/1.50  res_backward_subsumption_resolution:    0
% 6.74/1.50  res_clause_to_clause_subsumption:       2795
% 6.74/1.50  res_orphan_elimination:                 0
% 6.74/1.50  res_tautology_del:                      207
% 6.74/1.50  res_num_eq_res_simplified:              0
% 6.74/1.50  res_num_sel_changes:                    0
% 6.74/1.50  res_moves_from_active_to_pass:          0
% 6.74/1.50  
% 6.74/1.50  ------ Superposition
% 6.74/1.50  
% 6.74/1.50  sup_time_total:                         0.
% 6.74/1.50  sup_time_generating:                    0.
% 6.74/1.50  sup_time_sim_full:                      0.
% 6.74/1.50  sup_time_sim_immed:                     0.
% 6.74/1.50  
% 6.74/1.50  sup_num_of_clauses:                     569
% 6.74/1.50  sup_num_in_active:                      220
% 6.74/1.50  sup_num_in_passive:                     349
% 6.74/1.50  sup_num_of_loops:                       233
% 6.74/1.50  sup_fw_superposition:                   509
% 6.74/1.50  sup_bw_superposition:                   368
% 6.74/1.50  sup_immediate_simplified:               337
% 6.74/1.50  sup_given_eliminated:                   0
% 6.74/1.50  comparisons_done:                       0
% 6.74/1.50  comparisons_avoided:                    0
% 6.74/1.50  
% 6.74/1.50  ------ Simplifications
% 6.74/1.50  
% 6.74/1.50  
% 6.74/1.50  sim_fw_subset_subsumed:                 25
% 6.74/1.50  sim_bw_subset_subsumed:                 22
% 6.74/1.50  sim_fw_subsumed:                        49
% 6.74/1.50  sim_bw_subsumed:                        2
% 6.74/1.50  sim_fw_subsumption_res:                 0
% 6.74/1.50  sim_bw_subsumption_res:                 0
% 6.74/1.50  sim_tautology_del:                      44
% 6.74/1.50  sim_eq_tautology_del:                   15
% 6.74/1.50  sim_eq_res_simp:                        0
% 6.74/1.50  sim_fw_demodulated:                     192
% 6.74/1.50  sim_bw_demodulated:                     18
% 6.74/1.50  sim_light_normalised:                   97
% 6.74/1.50  sim_joinable_taut:                      0
% 6.74/1.50  sim_joinable_simp:                      0
% 6.74/1.50  sim_ac_normalised:                      0
% 6.74/1.50  sim_smt_subsumption:                    0
% 6.74/1.50  
%------------------------------------------------------------------------------
