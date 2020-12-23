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
% DateTime   : Thu Dec  3 12:25:47 EST 2020

% Result     : Theorem 3.80s
% Output     : CNFRefutation 3.80s
% Verified   : 
% Statistics : Number of formulae       :  185 (1150 expanded)
%              Number of clauses        :  123 ( 336 expanded)
%              Number of leaves         :   17 ( 361 expanded)
%              Depth                    :   27
%              Number of atoms          :  742 (7517 expanded)
%              Number of equality atoms :  248 (2036 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f51,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f11,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v2_tex_2(X2,X0)
                      & X2 = X3
                      & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                   => v2_tex_2(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v2_tex_2(X2,X0)
                        & X2 = X3
                        & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                     => v2_tex_2(X3,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tex_2(X3,X1)
                  & v2_tex_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tex_2(X3,X1)
                  & v2_tex_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ v2_tex_2(X3,X1)
          & v2_tex_2(X2,X0)
          & X2 = X3
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v2_tex_2(sK5,X1)
        & v2_tex_2(X2,X0)
        & sK5 = X2
        & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ v2_tex_2(X3,X1)
              & v2_tex_2(X2,X0)
              & X2 = X3
              & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X3] :
            ( ~ v2_tex_2(X3,X1)
            & v2_tex_2(sK4,X0)
            & sK4 = X3
            & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tex_2(X3,X1)
                  & v2_tex_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ v2_tex_2(X3,sK3)
                & v2_tex_2(X2,X0)
                & X2 = X3
                & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v2_tex_2(X3,X1)
                    & v2_tex_2(X2,X0)
                    & X2 = X3
                    & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tex_2(X3,X1)
                  & v2_tex_2(X2,sK2)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ~ v2_tex_2(sK5,sK3)
    & v2_tex_2(sK4,sK2)
    & sK4 = sK5
    & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK3)
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f24,f37,f36,f35,f34])).

fof(f62,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f58,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f59,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
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
    inference(nnf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f41,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f61,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f38])).

fof(f10,axiom,(
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
                            & v3_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ? [X5] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
                      & v3_pre_topc(X5,X0)
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f29])).

fof(f32,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
          & v3_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4
        & v3_pre_topc(sK1(X0,X1,X4),X0)
        & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1)
            | ~ v3_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r1_tarski(sK0(X0,X1),X1)
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r1_tarski(sK0(X0,X1),X1)
                & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ( k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4
                    & v3_pre_topc(sK1(X0,X1,X4),X0)
                    & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f32,f31])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f60,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f38])).

fof(f63,plain,(
    sK4 = sK5 ),
    inference(cnf_transformation,[],[f38])).

fof(f54,plain,(
    ! [X4,X0,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f64,plain,(
    v2_tex_2(sK4,sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f65,plain,(
    ~ v2_tex_2(sK5,sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | r1_tarski(sK0(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( v2_tex_2(X1,X0)
      | k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v3_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f68,plain,(
    ! [X2,X0,X3] :
      ( v3_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f52,plain,(
    ! [X4,X0,X1] :
      ( m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f53,plain,(
    ! [X4,X0,X1] :
      ( v3_pre_topc(sK1(X0,X1,X4),X0)
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_12,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1871,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_22,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_7,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1874,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3118,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_1874])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_27,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3127,plain,
    ( m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3118,c_27])).

cnf(c_3128,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_3127])).

cnf(c_3134,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK2) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1871,c_3128])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_144,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_5])).

cnf(c_145,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_144])).

cnf(c_1858,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_145])).

cnf(c_3133,plain,
    ( m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1858,c_3128])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_28,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3325,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3133,c_28])).

cnf(c_3326,plain,
    ( m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_3325])).

cnf(c_3331,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1871,c_3326])).

cnf(c_3464,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3331,c_28])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1872,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1875,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3642,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X1,X2) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X2))) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1872,c_1875])).

cnf(c_7537,plain,
    ( m1_pre_topc(sK2,X0) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3464,c_3642])).

cnf(c_13866,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7537,c_27])).

cnf(c_13867,plain,
    ( m1_pre_topc(sK2,X0) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_13866])).

cnf(c_13871,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_13867,c_1875])).

cnf(c_64,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_14368,plain,
    ( l1_pre_topc(X1) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13871,c_64])).

cnf(c_14369,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_14368])).

cnf(c_14380,plain,
    ( m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3134,c_14369])).

cnf(c_51,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_53,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_51])).

cnf(c_7548,plain,
    ( m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7537])).

cnf(c_14540,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14380,c_27,c_53,c_7548])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1877,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_14544,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_14540,c_1877])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1880,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_14904,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK2)
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14544,c_1880])).

cnf(c_2384,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_1858])).

cnf(c_2552,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2384,c_27])).

cnf(c_2553,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_2552])).

cnf(c_3117,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2553,c_1874])).

cnf(c_3249,plain,
    ( m1_pre_topc(X0,sK3) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3117,c_28])).

cnf(c_3250,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_3249])).

cnf(c_3335,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK3) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3134,c_3250])).

cnf(c_7540,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2553,c_3642])).

cnf(c_7803,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3335,c_7540])).

cnf(c_2610,plain,
    ( ~ m1_pre_topc(X0,sK3)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2611,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2610])).

cnf(c_7947,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7803,c_28,c_2611,c_3117])).

cnf(c_7953,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7947,c_1877])).

cnf(c_7959,plain,
    ( m1_pre_topc(sK2,sK2) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_7953])).

cnf(c_14991,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14904,c_27,c_53,c_7959])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1862,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_15,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1868,plain,
    ( v2_tex_2(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3655,plain,
    ( v2_tex_2(X0,X1) = iProver_top
    | m1_pre_topc(X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X2))) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1868,c_1875])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1861,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_21,negated_conjecture,
    ( sK4 = sK5 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1882,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1861,c_21])).

cnf(c_16,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,sK1(X1,X0,X2)) = X2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1867,plain,
    ( k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X2)) = X2
    | v2_tex_2(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4355,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK5,sK1(sK2,sK5,X0)) = X0
    | v2_tex_2(sK5,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X0,sK5) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1882,c_1867])).

cnf(c_20,negated_conjecture,
    ( v2_tex_2(sK4,sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1863,plain,
    ( v2_tex_2(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1881,plain,
    ( v2_tex_2(sK5,sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1863,c_21])).

cnf(c_4584,plain,
    ( r1_tarski(X0,sK5) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k9_subset_1(u1_struct_0(sK2),sK5,sK1(sK2,sK5,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4355,c_27,c_1881])).

cnf(c_4585,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK5,sK1(sK2,sK5,X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X0,sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_4584])).

cnf(c_9247,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK5,sK1(sK2,sK5,sK0(X0,X1))) = sK0(X0,X1)
    | v2_tex_2(X1,X0) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r1_tarski(sK0(X0,X1),sK5) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3655,c_4585])).

cnf(c_12657,plain,
    ( l1_pre_topc(X0) != iProver_top
    | r1_tarski(sK0(X0,X1),sK5) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | v2_tex_2(X1,X0) = iProver_top
    | k9_subset_1(u1_struct_0(sK2),sK5,sK1(sK2,sK5,sK0(X0,X1))) = sK0(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9247,c_27])).

cnf(c_12658,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK5,sK1(sK2,sK5,sK0(X0,X1))) = sK0(X0,X1)
    | v2_tex_2(X1,X0) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r1_tarski(sK0(X0,X1),sK5) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_12657])).

cnf(c_12666,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK5,sK1(sK2,sK5,sK0(sK3,sK5))) = sK0(sK3,sK5)
    | v2_tex_2(sK5,sK3) = iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | r1_tarski(sK0(sK3,sK5),sK5) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1862,c_12658])).

cnf(c_19,negated_conjecture,
    ( ~ v2_tex_2(sK5,sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_543,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK3 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_19])).

cnf(c_544,plain,
    ( m1_subset_1(sK0(sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_543])).

cnf(c_14,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK0(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_554,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK0(X1,X0),X0)
    | ~ l1_pre_topc(X1)
    | sK3 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_19])).

cnf(c_555,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(sK0(sK3,sK5),sK5)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_554])).

cnf(c_1888,plain,
    ( v2_tex_2(sK5,sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1881])).

cnf(c_1896,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1882])).

cnf(c_2098,plain,
    ( ~ m1_pre_topc(sK3,X0)
    | m1_subset_1(sK0(sK3,sK5),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK0(sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2100,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | m1_subset_1(sK0(sK3,sK5),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK0(sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2098])).

cnf(c_3332,plain,
    ( m1_pre_topc(sK3,sK2)
    | ~ l1_pre_topc(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3331])).

cnf(c_5907,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK0(sK3,sK5),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(sK0(sK3,sK5),X0)
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,sK1(X1,X0,sK0(sK3,sK5))) = sK0(sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_12614,plain,
    ( ~ v2_tex_2(sK5,X0)
    | ~ m1_subset_1(sK0(sK3,sK5),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(sK0(sK3,sK5),sK5)
    | ~ l1_pre_topc(X0)
    | k9_subset_1(u1_struct_0(X0),sK5,sK1(X0,sK5,sK0(sK3,sK5))) = sK0(sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_5907])).

cnf(c_12616,plain,
    ( ~ v2_tex_2(sK5,sK2)
    | ~ m1_subset_1(sK0(sK3,sK5),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(sK0(sK3,sK5),sK5)
    | ~ l1_pre_topc(sK2)
    | k9_subset_1(u1_struct_0(sK2),sK5,sK1(sK2,sK5,sK0(sK3,sK5))) = sK0(sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_12614])).

cnf(c_13646,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK5,sK1(sK2,sK5,sK0(sK3,sK5))) = sK0(sK3,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12666,c_26,c_25,c_23,c_544,c_555,c_1888,c_1896,c_2100,c_3332,c_12616])).

cnf(c_15000,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK5,sK1(sK2,sK5,sK0(sK3,sK5))) = sK0(sK3,sK5) ),
    inference(demodulation,[status(thm)],[c_14991,c_13646])).

cnf(c_13,plain,
    ( v2_tex_2(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK0(X1,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1912,plain,
    ( v2_tex_2(sK5,sK3)
    | ~ v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | k9_subset_1(u1_struct_0(sK3),sK5,X0) != sK0(sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_9046,plain,
    ( v2_tex_2(sK5,sK3)
    | ~ v3_pre_topc(sK1(X0,sK5,sK0(sK3,sK5)),sK3)
    | ~ m1_subset_1(sK1(X0,sK5,sK0(sK3,sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | k9_subset_1(u1_struct_0(sK3),sK5,sK1(X0,sK5,sK0(sK3,sK5))) != sK0(sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_1912])).

cnf(c_9050,plain,
    ( v2_tex_2(sK5,sK3)
    | ~ v3_pre_topc(sK1(sK2,sK5,sK0(sK3,sK5)),sK3)
    | ~ m1_subset_1(sK1(sK2,sK5,sK0(sK3,sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | k9_subset_1(u1_struct_0(sK3),sK5,sK1(sK2,sK5,sK0(sK3,sK5))) != sK0(sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_9046])).

cnf(c_10,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1926,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X0,sK3)
    | ~ m1_pre_topc(sK3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_8681,plain,
    ( ~ v3_pre_topc(sK1(X0,sK5,sK0(sK3,sK5)),X1)
    | v3_pre_topc(sK1(X0,sK5,sK0(sK3,sK5)),sK3)
    | ~ m1_pre_topc(sK3,X1)
    | ~ m1_subset_1(sK1(X0,sK5,sK0(sK3,sK5)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1(X0,sK5,sK0(sK3,sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_1926])).

cnf(c_8702,plain,
    ( ~ v3_pre_topc(sK1(sK2,sK5,sK0(sK3,sK5)),sK2)
    | v3_pre_topc(sK1(sK2,sK5,sK0(sK3,sK5)),sK3)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ m1_subset_1(sK1(sK2,sK5,sK0(sK3,sK5)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK1(sK2,sK5,sK0(sK3,sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_8681])).

cnf(c_2107,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(sK1(X0,X2,X3),k1_zfmisc_1(u1_struct_0(X0)))
    | m1_subset_1(sK1(X0,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_6871,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(sK1(X0,sK5,sK0(sK3,sK5)),k1_zfmisc_1(u1_struct_0(X0)))
    | m1_subset_1(sK1(X0,sK5,sK0(sK3,sK5)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_2107])).

cnf(c_8680,plain,
    ( ~ m1_pre_topc(X0,sK3)
    | ~ m1_subset_1(sK1(X0,sK5,sK0(sK3,sK5)),k1_zfmisc_1(u1_struct_0(X0)))
    | m1_subset_1(sK1(X0,sK5,sK0(sK3,sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_6871])).

cnf(c_8686,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK1(sK2,sK5,sK0(sK3,sK5)),k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(sK2,sK5,sK0(sK3,sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_8680])).

cnf(c_18,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_3027,plain,
    ( ~ v2_tex_2(sK5,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | m1_subset_1(sK1(X0,sK5,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X1,sK5)
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_5393,plain,
    ( ~ v2_tex_2(sK5,X0)
    | m1_subset_1(sK1(X0,sK5,sK0(sK3,sK5)),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK0(sK3,sK5),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(sK0(sK3,sK5),sK5)
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_3027])).

cnf(c_5395,plain,
    ( ~ v2_tex_2(sK5,sK2)
    | m1_subset_1(sK1(sK2,sK5,sK0(sK3,sK5)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK0(sK3,sK5),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(sK0(sK3,sK5),sK5)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_5393])).

cnf(c_17,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_pre_topc(sK1(X1,X0,X2),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_3026,plain,
    ( ~ v2_tex_2(sK5,X0)
    | v3_pre_topc(sK1(X0,sK5,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X1,sK5)
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_5381,plain,
    ( ~ v2_tex_2(sK5,X0)
    | v3_pre_topc(sK1(X0,sK5,sK0(sK3,sK5)),X0)
    | ~ m1_subset_1(sK0(sK3,sK5),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(sK0(sK3,sK5),sK5)
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_3026])).

cnf(c_5383,plain,
    ( ~ v2_tex_2(sK5,sK2)
    | v3_pre_topc(sK1(sK2,sK5,sK0(sK3,sK5)),sK2)
    | ~ m1_subset_1(sK0(sK3,sK5),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(sK0(sK3,sK5),sK5)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_5381])).

cnf(c_2922,plain,
    ( ~ m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2385,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ m1_pre_topc(X0,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2384])).

cnf(c_2387,plain,
    ( m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2385])).

cnf(c_52,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15000,c_9050,c_8702,c_8686,c_5395,c_5383,c_3332,c_2922,c_2387,c_2100,c_1896,c_1888,c_555,c_544,c_52,c_19,c_23,c_25,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:43:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 3.80/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.80/0.99  
% 3.80/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.80/0.99  
% 3.80/0.99  ------  iProver source info
% 3.80/0.99  
% 3.80/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.80/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.80/0.99  git: non_committed_changes: false
% 3.80/0.99  git: last_make_outside_of_git: false
% 3.80/0.99  
% 3.80/0.99  ------ 
% 3.80/0.99  
% 3.80/0.99  ------ Input Options
% 3.80/0.99  
% 3.80/0.99  --out_options                           all
% 3.80/0.99  --tptp_safe_out                         true
% 3.80/0.99  --problem_path                          ""
% 3.80/0.99  --include_path                          ""
% 3.80/0.99  --clausifier                            res/vclausify_rel
% 3.80/0.99  --clausifier_options                    ""
% 3.80/0.99  --stdin                                 false
% 3.80/0.99  --stats_out                             all
% 3.80/0.99  
% 3.80/0.99  ------ General Options
% 3.80/0.99  
% 3.80/0.99  --fof                                   false
% 3.80/0.99  --time_out_real                         305.
% 3.80/0.99  --time_out_virtual                      -1.
% 3.80/0.99  --symbol_type_check                     false
% 3.80/0.99  --clausify_out                          false
% 3.80/0.99  --sig_cnt_out                           false
% 3.80/0.99  --trig_cnt_out                          false
% 3.80/0.99  --trig_cnt_out_tolerance                1.
% 3.80/0.99  --trig_cnt_out_sk_spl                   false
% 3.80/0.99  --abstr_cl_out                          false
% 3.80/0.99  
% 3.80/0.99  ------ Global Options
% 3.80/0.99  
% 3.80/0.99  --schedule                              default
% 3.80/0.99  --add_important_lit                     false
% 3.80/0.99  --prop_solver_per_cl                    1000
% 3.80/0.99  --min_unsat_core                        false
% 3.80/0.99  --soft_assumptions                      false
% 3.80/0.99  --soft_lemma_size                       3
% 3.80/0.99  --prop_impl_unit_size                   0
% 3.80/0.99  --prop_impl_unit                        []
% 3.80/0.99  --share_sel_clauses                     true
% 3.80/0.99  --reset_solvers                         false
% 3.80/0.99  --bc_imp_inh                            [conj_cone]
% 3.80/0.99  --conj_cone_tolerance                   3.
% 3.80/0.99  --extra_neg_conj                        none
% 3.80/0.99  --large_theory_mode                     true
% 3.80/0.99  --prolific_symb_bound                   200
% 3.80/0.99  --lt_threshold                          2000
% 3.80/0.99  --clause_weak_htbl                      true
% 3.80/0.99  --gc_record_bc_elim                     false
% 3.80/0.99  
% 3.80/0.99  ------ Preprocessing Options
% 3.80/0.99  
% 3.80/0.99  --preprocessing_flag                    true
% 3.80/0.99  --time_out_prep_mult                    0.1
% 3.80/0.99  --splitting_mode                        input
% 3.80/0.99  --splitting_grd                         true
% 3.80/0.99  --splitting_cvd                         false
% 3.80/0.99  --splitting_cvd_svl                     false
% 3.80/0.99  --splitting_nvd                         32
% 3.80/0.99  --sub_typing                            true
% 3.80/0.99  --prep_gs_sim                           true
% 3.80/0.99  --prep_unflatten                        true
% 3.80/0.99  --prep_res_sim                          true
% 3.80/0.99  --prep_upred                            true
% 3.80/0.99  --prep_sem_filter                       exhaustive
% 3.80/0.99  --prep_sem_filter_out                   false
% 3.80/0.99  --pred_elim                             true
% 3.80/0.99  --res_sim_input                         true
% 3.80/0.99  --eq_ax_congr_red                       true
% 3.80/0.99  --pure_diseq_elim                       true
% 3.80/0.99  --brand_transform                       false
% 3.80/0.99  --non_eq_to_eq                          false
% 3.80/0.99  --prep_def_merge                        true
% 3.80/0.99  --prep_def_merge_prop_impl              false
% 3.80/0.99  --prep_def_merge_mbd                    true
% 3.80/0.99  --prep_def_merge_tr_red                 false
% 3.80/0.99  --prep_def_merge_tr_cl                  false
% 3.80/0.99  --smt_preprocessing                     true
% 3.80/0.99  --smt_ac_axioms                         fast
% 3.80/0.99  --preprocessed_out                      false
% 3.80/0.99  --preprocessed_stats                    false
% 3.80/0.99  
% 3.80/0.99  ------ Abstraction refinement Options
% 3.80/0.99  
% 3.80/0.99  --abstr_ref                             []
% 3.80/0.99  --abstr_ref_prep                        false
% 3.80/0.99  --abstr_ref_until_sat                   false
% 3.80/0.99  --abstr_ref_sig_restrict                funpre
% 3.80/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.80/0.99  --abstr_ref_under                       []
% 3.80/0.99  
% 3.80/0.99  ------ SAT Options
% 3.80/0.99  
% 3.80/0.99  --sat_mode                              false
% 3.80/0.99  --sat_fm_restart_options                ""
% 3.80/0.99  --sat_gr_def                            false
% 3.80/0.99  --sat_epr_types                         true
% 3.80/0.99  --sat_non_cyclic_types                  false
% 3.80/0.99  --sat_finite_models                     false
% 3.80/0.99  --sat_fm_lemmas                         false
% 3.80/0.99  --sat_fm_prep                           false
% 3.80/0.99  --sat_fm_uc_incr                        true
% 3.80/0.99  --sat_out_model                         small
% 3.80/0.99  --sat_out_clauses                       false
% 3.80/0.99  
% 3.80/0.99  ------ QBF Options
% 3.80/0.99  
% 3.80/0.99  --qbf_mode                              false
% 3.80/0.99  --qbf_elim_univ                         false
% 3.80/0.99  --qbf_dom_inst                          none
% 3.80/0.99  --qbf_dom_pre_inst                      false
% 3.80/0.99  --qbf_sk_in                             false
% 3.80/0.99  --qbf_pred_elim                         true
% 3.80/0.99  --qbf_split                             512
% 3.80/0.99  
% 3.80/0.99  ------ BMC1 Options
% 3.80/0.99  
% 3.80/0.99  --bmc1_incremental                      false
% 3.80/0.99  --bmc1_axioms                           reachable_all
% 3.80/0.99  --bmc1_min_bound                        0
% 3.80/0.99  --bmc1_max_bound                        -1
% 3.80/0.99  --bmc1_max_bound_default                -1
% 3.80/0.99  --bmc1_symbol_reachability              true
% 3.80/0.99  --bmc1_property_lemmas                  false
% 3.80/0.99  --bmc1_k_induction                      false
% 3.80/0.99  --bmc1_non_equiv_states                 false
% 3.80/0.99  --bmc1_deadlock                         false
% 3.80/0.99  --bmc1_ucm                              false
% 3.80/0.99  --bmc1_add_unsat_core                   none
% 3.80/0.99  --bmc1_unsat_core_children              false
% 3.80/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.80/0.99  --bmc1_out_stat                         full
% 3.80/0.99  --bmc1_ground_init                      false
% 3.80/0.99  --bmc1_pre_inst_next_state              false
% 3.80/0.99  --bmc1_pre_inst_state                   false
% 3.80/0.99  --bmc1_pre_inst_reach_state             false
% 3.80/0.99  --bmc1_out_unsat_core                   false
% 3.80/0.99  --bmc1_aig_witness_out                  false
% 3.80/0.99  --bmc1_verbose                          false
% 3.80/0.99  --bmc1_dump_clauses_tptp                false
% 3.80/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.80/0.99  --bmc1_dump_file                        -
% 3.80/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.80/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.80/0.99  --bmc1_ucm_extend_mode                  1
% 3.80/0.99  --bmc1_ucm_init_mode                    2
% 3.80/0.99  --bmc1_ucm_cone_mode                    none
% 3.80/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.80/0.99  --bmc1_ucm_relax_model                  4
% 3.80/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.80/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.80/0.99  --bmc1_ucm_layered_model                none
% 3.80/0.99  --bmc1_ucm_max_lemma_size               10
% 3.80/0.99  
% 3.80/0.99  ------ AIG Options
% 3.80/0.99  
% 3.80/0.99  --aig_mode                              false
% 3.80/0.99  
% 3.80/0.99  ------ Instantiation Options
% 3.80/0.99  
% 3.80/0.99  --instantiation_flag                    true
% 3.80/0.99  --inst_sos_flag                         true
% 3.80/0.99  --inst_sos_phase                        true
% 3.80/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.80/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.80/0.99  --inst_lit_sel_side                     num_symb
% 3.80/0.99  --inst_solver_per_active                1400
% 3.80/0.99  --inst_solver_calls_frac                1.
% 3.80/0.99  --inst_passive_queue_type               priority_queues
% 3.80/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.80/0.99  --inst_passive_queues_freq              [25;2]
% 3.80/0.99  --inst_dismatching                      true
% 3.80/0.99  --inst_eager_unprocessed_to_passive     true
% 3.80/0.99  --inst_prop_sim_given                   true
% 3.80/0.99  --inst_prop_sim_new                     false
% 3.80/0.99  --inst_subs_new                         false
% 3.80/0.99  --inst_eq_res_simp                      false
% 3.80/0.99  --inst_subs_given                       false
% 3.80/0.99  --inst_orphan_elimination               true
% 3.80/0.99  --inst_learning_loop_flag               true
% 3.80/0.99  --inst_learning_start                   3000
% 3.80/0.99  --inst_learning_factor                  2
% 3.80/0.99  --inst_start_prop_sim_after_learn       3
% 3.80/0.99  --inst_sel_renew                        solver
% 3.80/0.99  --inst_lit_activity_flag                true
% 3.80/0.99  --inst_restr_to_given                   false
% 3.80/0.99  --inst_activity_threshold               500
% 3.80/0.99  --inst_out_proof                        true
% 3.80/0.99  
% 3.80/0.99  ------ Resolution Options
% 3.80/0.99  
% 3.80/0.99  --resolution_flag                       true
% 3.80/0.99  --res_lit_sel                           adaptive
% 3.80/0.99  --res_lit_sel_side                      none
% 3.80/0.99  --res_ordering                          kbo
% 3.80/0.99  --res_to_prop_solver                    active
% 3.80/0.99  --res_prop_simpl_new                    false
% 3.80/0.99  --res_prop_simpl_given                  true
% 3.80/0.99  --res_passive_queue_type                priority_queues
% 3.80/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.80/0.99  --res_passive_queues_freq               [15;5]
% 3.80/0.99  --res_forward_subs                      full
% 3.80/0.99  --res_backward_subs                     full
% 3.80/0.99  --res_forward_subs_resolution           true
% 3.80/0.99  --res_backward_subs_resolution          true
% 3.80/0.99  --res_orphan_elimination                true
% 3.80/0.99  --res_time_limit                        2.
% 3.80/0.99  --res_out_proof                         true
% 3.80/0.99  
% 3.80/0.99  ------ Superposition Options
% 3.80/0.99  
% 3.80/0.99  --superposition_flag                    true
% 3.80/0.99  --sup_passive_queue_type                priority_queues
% 3.80/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.80/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.80/0.99  --demod_completeness_check              fast
% 3.80/0.99  --demod_use_ground                      true
% 3.80/0.99  --sup_to_prop_solver                    passive
% 3.80/0.99  --sup_prop_simpl_new                    true
% 3.80/0.99  --sup_prop_simpl_given                  true
% 3.80/0.99  --sup_fun_splitting                     true
% 3.80/0.99  --sup_smt_interval                      50000
% 3.80/0.99  
% 3.80/0.99  ------ Superposition Simplification Setup
% 3.80/0.99  
% 3.80/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.80/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.80/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.80/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.80/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.80/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.80/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.80/0.99  --sup_immed_triv                        [TrivRules]
% 3.80/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.80/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.80/0.99  --sup_immed_bw_main                     []
% 3.80/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.80/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.80/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.80/0.99  --sup_input_bw                          []
% 3.80/0.99  
% 3.80/0.99  ------ Combination Options
% 3.80/0.99  
% 3.80/0.99  --comb_res_mult                         3
% 3.80/0.99  --comb_sup_mult                         2
% 3.80/0.99  --comb_inst_mult                        10
% 3.80/0.99  
% 3.80/0.99  ------ Debug Options
% 3.80/0.99  
% 3.80/0.99  --dbg_backtrace                         false
% 3.80/0.99  --dbg_dump_prop_clauses                 false
% 3.80/0.99  --dbg_dump_prop_clauses_file            -
% 3.80/0.99  --dbg_out_stat                          false
% 3.80/0.99  ------ Parsing...
% 3.80/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.80/0.99  
% 3.80/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.80/0.99  
% 3.80/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.80/0.99  
% 3.80/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.80/0.99  ------ Proving...
% 3.80/0.99  ------ Problem Properties 
% 3.80/0.99  
% 3.80/0.99  
% 3.80/0.99  clauses                                 25
% 3.80/0.99  conjectures                             8
% 3.80/0.99  EPR                                     9
% 3.80/0.99  Horn                                    23
% 3.80/0.99  unary                                   9
% 3.80/0.99  binary                                  3
% 3.80/0.99  lits                                    72
% 3.80/0.99  lits eq                                 5
% 3.80/0.99  fd_pure                                 0
% 3.80/0.99  fd_pseudo                               0
% 3.80/0.99  fd_cond                                 0
% 3.80/0.99  fd_pseudo_cond                          1
% 3.80/0.99  AC symbols                              0
% 3.80/0.99  
% 3.80/0.99  ------ Schedule dynamic 5 is on 
% 3.80/0.99  
% 3.80/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.80/0.99  
% 3.80/0.99  
% 3.80/0.99  ------ 
% 3.80/0.99  Current options:
% 3.80/0.99  ------ 
% 3.80/0.99  
% 3.80/0.99  ------ Input Options
% 3.80/0.99  
% 3.80/0.99  --out_options                           all
% 3.80/0.99  --tptp_safe_out                         true
% 3.80/0.99  --problem_path                          ""
% 3.80/0.99  --include_path                          ""
% 3.80/0.99  --clausifier                            res/vclausify_rel
% 3.80/0.99  --clausifier_options                    ""
% 3.80/0.99  --stdin                                 false
% 3.80/0.99  --stats_out                             all
% 3.80/0.99  
% 3.80/0.99  ------ General Options
% 3.80/0.99  
% 3.80/0.99  --fof                                   false
% 3.80/0.99  --time_out_real                         305.
% 3.80/0.99  --time_out_virtual                      -1.
% 3.80/0.99  --symbol_type_check                     false
% 3.80/0.99  --clausify_out                          false
% 3.80/0.99  --sig_cnt_out                           false
% 3.80/0.99  --trig_cnt_out                          false
% 3.80/0.99  --trig_cnt_out_tolerance                1.
% 3.80/0.99  --trig_cnt_out_sk_spl                   false
% 3.80/0.99  --abstr_cl_out                          false
% 3.80/0.99  
% 3.80/0.99  ------ Global Options
% 3.80/0.99  
% 3.80/0.99  --schedule                              default
% 3.80/0.99  --add_important_lit                     false
% 3.80/0.99  --prop_solver_per_cl                    1000
% 3.80/0.99  --min_unsat_core                        false
% 3.80/0.99  --soft_assumptions                      false
% 3.80/0.99  --soft_lemma_size                       3
% 3.80/0.99  --prop_impl_unit_size                   0
% 3.80/0.99  --prop_impl_unit                        []
% 3.80/0.99  --share_sel_clauses                     true
% 3.80/0.99  --reset_solvers                         false
% 3.80/0.99  --bc_imp_inh                            [conj_cone]
% 3.80/0.99  --conj_cone_tolerance                   3.
% 3.80/0.99  --extra_neg_conj                        none
% 3.80/0.99  --large_theory_mode                     true
% 3.80/0.99  --prolific_symb_bound                   200
% 3.80/0.99  --lt_threshold                          2000
% 3.80/0.99  --clause_weak_htbl                      true
% 3.80/0.99  --gc_record_bc_elim                     false
% 3.80/0.99  
% 3.80/0.99  ------ Preprocessing Options
% 3.80/0.99  
% 3.80/0.99  --preprocessing_flag                    true
% 3.80/0.99  --time_out_prep_mult                    0.1
% 3.80/0.99  --splitting_mode                        input
% 3.80/0.99  --splitting_grd                         true
% 3.80/0.99  --splitting_cvd                         false
% 3.80/0.99  --splitting_cvd_svl                     false
% 3.80/0.99  --splitting_nvd                         32
% 3.80/0.99  --sub_typing                            true
% 3.80/0.99  --prep_gs_sim                           true
% 3.80/0.99  --prep_unflatten                        true
% 3.80/0.99  --prep_res_sim                          true
% 3.80/0.99  --prep_upred                            true
% 3.80/0.99  --prep_sem_filter                       exhaustive
% 3.80/0.99  --prep_sem_filter_out                   false
% 3.80/0.99  --pred_elim                             true
% 3.80/0.99  --res_sim_input                         true
% 3.80/0.99  --eq_ax_congr_red                       true
% 3.80/0.99  --pure_diseq_elim                       true
% 3.80/0.99  --brand_transform                       false
% 3.80/0.99  --non_eq_to_eq                          false
% 3.80/0.99  --prep_def_merge                        true
% 3.80/0.99  --prep_def_merge_prop_impl              false
% 3.80/0.99  --prep_def_merge_mbd                    true
% 3.80/0.99  --prep_def_merge_tr_red                 false
% 3.80/0.99  --prep_def_merge_tr_cl                  false
% 3.80/0.99  --smt_preprocessing                     true
% 3.80/0.99  --smt_ac_axioms                         fast
% 3.80/0.99  --preprocessed_out                      false
% 3.80/0.99  --preprocessed_stats                    false
% 3.80/0.99  
% 3.80/0.99  ------ Abstraction refinement Options
% 3.80/0.99  
% 3.80/0.99  --abstr_ref                             []
% 3.80/0.99  --abstr_ref_prep                        false
% 3.80/0.99  --abstr_ref_until_sat                   false
% 3.80/0.99  --abstr_ref_sig_restrict                funpre
% 3.80/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.80/0.99  --abstr_ref_under                       []
% 3.80/0.99  
% 3.80/0.99  ------ SAT Options
% 3.80/0.99  
% 3.80/0.99  --sat_mode                              false
% 3.80/0.99  --sat_fm_restart_options                ""
% 3.80/0.99  --sat_gr_def                            false
% 3.80/0.99  --sat_epr_types                         true
% 3.80/0.99  --sat_non_cyclic_types                  false
% 3.80/0.99  --sat_finite_models                     false
% 3.80/0.99  --sat_fm_lemmas                         false
% 3.80/0.99  --sat_fm_prep                           false
% 3.80/0.99  --sat_fm_uc_incr                        true
% 3.80/0.99  --sat_out_model                         small
% 3.80/0.99  --sat_out_clauses                       false
% 3.80/0.99  
% 3.80/0.99  ------ QBF Options
% 3.80/0.99  
% 3.80/0.99  --qbf_mode                              false
% 3.80/0.99  --qbf_elim_univ                         false
% 3.80/0.99  --qbf_dom_inst                          none
% 3.80/0.99  --qbf_dom_pre_inst                      false
% 3.80/0.99  --qbf_sk_in                             false
% 3.80/0.99  --qbf_pred_elim                         true
% 3.80/0.99  --qbf_split                             512
% 3.80/0.99  
% 3.80/0.99  ------ BMC1 Options
% 3.80/0.99  
% 3.80/0.99  --bmc1_incremental                      false
% 3.80/0.99  --bmc1_axioms                           reachable_all
% 3.80/0.99  --bmc1_min_bound                        0
% 3.80/0.99  --bmc1_max_bound                        -1
% 3.80/0.99  --bmc1_max_bound_default                -1
% 3.80/0.99  --bmc1_symbol_reachability              true
% 3.80/0.99  --bmc1_property_lemmas                  false
% 3.80/0.99  --bmc1_k_induction                      false
% 3.80/0.99  --bmc1_non_equiv_states                 false
% 3.80/0.99  --bmc1_deadlock                         false
% 3.80/0.99  --bmc1_ucm                              false
% 3.80/0.99  --bmc1_add_unsat_core                   none
% 3.80/0.99  --bmc1_unsat_core_children              false
% 3.80/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.80/0.99  --bmc1_out_stat                         full
% 3.80/0.99  --bmc1_ground_init                      false
% 3.80/0.99  --bmc1_pre_inst_next_state              false
% 3.80/0.99  --bmc1_pre_inst_state                   false
% 3.80/0.99  --bmc1_pre_inst_reach_state             false
% 3.80/0.99  --bmc1_out_unsat_core                   false
% 3.80/0.99  --bmc1_aig_witness_out                  false
% 3.80/0.99  --bmc1_verbose                          false
% 3.80/0.99  --bmc1_dump_clauses_tptp                false
% 3.80/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.80/0.99  --bmc1_dump_file                        -
% 3.80/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.80/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.80/0.99  --bmc1_ucm_extend_mode                  1
% 3.80/0.99  --bmc1_ucm_init_mode                    2
% 3.80/0.99  --bmc1_ucm_cone_mode                    none
% 3.80/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.80/0.99  --bmc1_ucm_relax_model                  4
% 3.80/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.80/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.80/0.99  --bmc1_ucm_layered_model                none
% 3.80/0.99  --bmc1_ucm_max_lemma_size               10
% 3.80/0.99  
% 3.80/0.99  ------ AIG Options
% 3.80/0.99  
% 3.80/0.99  --aig_mode                              false
% 3.80/0.99  
% 3.80/0.99  ------ Instantiation Options
% 3.80/0.99  
% 3.80/0.99  --instantiation_flag                    true
% 3.80/0.99  --inst_sos_flag                         true
% 3.80/0.99  --inst_sos_phase                        true
% 3.80/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.80/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.80/0.99  --inst_lit_sel_side                     none
% 3.80/0.99  --inst_solver_per_active                1400
% 3.80/0.99  --inst_solver_calls_frac                1.
% 3.80/0.99  --inst_passive_queue_type               priority_queues
% 3.80/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.80/0.99  --inst_passive_queues_freq              [25;2]
% 3.80/0.99  --inst_dismatching                      true
% 3.80/0.99  --inst_eager_unprocessed_to_passive     true
% 3.80/0.99  --inst_prop_sim_given                   true
% 3.80/0.99  --inst_prop_sim_new                     false
% 3.80/0.99  --inst_subs_new                         false
% 3.80/0.99  --inst_eq_res_simp                      false
% 3.80/0.99  --inst_subs_given                       false
% 3.80/0.99  --inst_orphan_elimination               true
% 3.80/0.99  --inst_learning_loop_flag               true
% 3.80/0.99  --inst_learning_start                   3000
% 3.80/0.99  --inst_learning_factor                  2
% 3.80/0.99  --inst_start_prop_sim_after_learn       3
% 3.80/0.99  --inst_sel_renew                        solver
% 3.80/0.99  --inst_lit_activity_flag                true
% 3.80/0.99  --inst_restr_to_given                   false
% 3.80/0.99  --inst_activity_threshold               500
% 3.80/0.99  --inst_out_proof                        true
% 3.80/0.99  
% 3.80/0.99  ------ Resolution Options
% 3.80/0.99  
% 3.80/0.99  --resolution_flag                       false
% 3.80/0.99  --res_lit_sel                           adaptive
% 3.80/0.99  --res_lit_sel_side                      none
% 3.80/0.99  --res_ordering                          kbo
% 3.80/0.99  --res_to_prop_solver                    active
% 3.80/0.99  --res_prop_simpl_new                    false
% 3.80/0.99  --res_prop_simpl_given                  true
% 3.80/0.99  --res_passive_queue_type                priority_queues
% 3.80/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.80/0.99  --res_passive_queues_freq               [15;5]
% 3.80/0.99  --res_forward_subs                      full
% 3.80/0.99  --res_backward_subs                     full
% 3.80/0.99  --res_forward_subs_resolution           true
% 3.80/0.99  --res_backward_subs_resolution          true
% 3.80/0.99  --res_orphan_elimination                true
% 3.80/0.99  --res_time_limit                        2.
% 3.80/0.99  --res_out_proof                         true
% 3.80/0.99  
% 3.80/0.99  ------ Superposition Options
% 3.80/0.99  
% 3.80/0.99  --superposition_flag                    true
% 3.80/0.99  --sup_passive_queue_type                priority_queues
% 3.80/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.80/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.80/0.99  --demod_completeness_check              fast
% 3.80/0.99  --demod_use_ground                      true
% 3.80/0.99  --sup_to_prop_solver                    passive
% 3.80/0.99  --sup_prop_simpl_new                    true
% 3.80/0.99  --sup_prop_simpl_given                  true
% 3.80/0.99  --sup_fun_splitting                     true
% 3.80/0.99  --sup_smt_interval                      50000
% 3.80/0.99  
% 3.80/0.99  ------ Superposition Simplification Setup
% 3.80/0.99  
% 3.80/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.80/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.80/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.80/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.80/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.80/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.80/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.80/0.99  --sup_immed_triv                        [TrivRules]
% 3.80/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.80/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.80/0.99  --sup_immed_bw_main                     []
% 3.80/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.80/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.80/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.80/0.99  --sup_input_bw                          []
% 3.80/0.99  
% 3.80/0.99  ------ Combination Options
% 3.80/0.99  
% 3.80/0.99  --comb_res_mult                         3
% 3.80/0.99  --comb_sup_mult                         2
% 3.80/0.99  --comb_inst_mult                        10
% 3.80/0.99  
% 3.80/0.99  ------ Debug Options
% 3.80/0.99  
% 3.80/0.99  --dbg_backtrace                         false
% 3.80/0.99  --dbg_dump_prop_clauses                 false
% 3.80/0.99  --dbg_dump_prop_clauses_file            -
% 3.80/0.99  --dbg_out_stat                          false
% 3.80/0.99  
% 3.80/0.99  
% 3.80/0.99  
% 3.80/0.99  
% 3.80/0.99  ------ Proving...
% 3.80/0.99  
% 3.80/0.99  
% 3.80/0.99  % SZS status Theorem for theBenchmark.p
% 3.80/0.99  
% 3.80/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.80/0.99  
% 3.80/0.99  fof(f9,axiom,(
% 3.80/0.99    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 3.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f20,plain,(
% 3.80/0.99    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 3.80/0.99    inference(ennf_transformation,[],[f9])).
% 3.80/0.99  
% 3.80/0.99  fof(f51,plain,(
% 3.80/0.99    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 3.80/0.99    inference(cnf_transformation,[],[f20])).
% 3.80/0.99  
% 3.80/0.99  fof(f11,conjecture,(
% 3.80/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v2_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v2_tex_2(X3,X1))))))),
% 3.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f12,negated_conjecture,(
% 3.80/0.99    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v2_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v2_tex_2(X3,X1))))))),
% 3.80/0.99    inference(negated_conjecture,[],[f11])).
% 3.80/0.99  
% 3.80/0.99  fof(f23,plain,(
% 3.80/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v2_tex_2(X3,X1) & (v2_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 3.80/0.99    inference(ennf_transformation,[],[f12])).
% 3.80/0.99  
% 3.80/0.99  fof(f24,plain,(
% 3.80/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v2_tex_2(X3,X1) & v2_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 3.80/0.99    inference(flattening,[],[f23])).
% 3.80/0.99  
% 3.80/0.99  fof(f37,plain,(
% 3.80/0.99    ( ! [X2,X0,X1] : (? [X3] : (~v2_tex_2(X3,X1) & v2_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v2_tex_2(sK5,X1) & v2_tex_2(X2,X0) & sK5 = X2 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 3.80/0.99    introduced(choice_axiom,[])).
% 3.80/0.99  
% 3.80/0.99  fof(f36,plain,(
% 3.80/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (~v2_tex_2(X3,X1) & v2_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X3] : (~v2_tex_2(X3,X1) & v2_tex_2(sK4,X0) & sK4 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.80/0.99    introduced(choice_axiom,[])).
% 3.80/0.99  
% 3.80/0.99  fof(f35,plain,(
% 3.80/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~v2_tex_2(X3,X1) & v2_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) => (? [X2] : (? [X3] : (~v2_tex_2(X3,sK3) & v2_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(sK3))) )),
% 3.80/0.99    introduced(choice_axiom,[])).
% 3.80/0.99  
% 3.80/0.99  fof(f34,plain,(
% 3.80/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v2_tex_2(X3,X1) & v2_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (~v2_tex_2(X3,X1) & v2_tex_2(X2,sK2) & X2 = X3 & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(X1)) & l1_pre_topc(sK2))),
% 3.80/0.99    introduced(choice_axiom,[])).
% 3.80/0.99  
% 3.80/0.99  fof(f38,plain,(
% 3.80/0.99    (((~v2_tex_2(sK5,sK3) & v2_tex_2(sK4,sK2) & sK4 = sK5 & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK3)) & l1_pre_topc(sK2)),
% 3.80/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f24,f37,f36,f35,f34])).
% 3.80/0.99  
% 3.80/0.99  fof(f62,plain,(
% 3.80/0.99    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),
% 3.80/0.99    inference(cnf_transformation,[],[f38])).
% 3.80/0.99  
% 3.80/0.99  fof(f5,axiom,(
% 3.80/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 3.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f15,plain,(
% 3.80/0.99    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 3.80/0.99    inference(ennf_transformation,[],[f5])).
% 3.80/0.99  
% 3.80/0.99  fof(f46,plain,(
% 3.80/0.99    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 3.80/0.99    inference(cnf_transformation,[],[f15])).
% 3.80/0.99  
% 3.80/0.99  fof(f58,plain,(
% 3.80/0.99    l1_pre_topc(sK2)),
% 3.80/0.99    inference(cnf_transformation,[],[f38])).
% 3.80/0.99  
% 3.80/0.99  fof(f6,axiom,(
% 3.80/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 3.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f16,plain,(
% 3.80/0.99    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.80/0.99    inference(ennf_transformation,[],[f6])).
% 3.80/0.99  
% 3.80/0.99  fof(f28,plain,(
% 3.80/0.99    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.80/0.99    inference(nnf_transformation,[],[f16])).
% 3.80/0.99  
% 3.80/0.99  fof(f47,plain,(
% 3.80/0.99    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.80/0.99    inference(cnf_transformation,[],[f28])).
% 3.80/0.99  
% 3.80/0.99  fof(f3,axiom,(
% 3.80/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f13,plain,(
% 3.80/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.80/0.99    inference(ennf_transformation,[],[f3])).
% 3.80/0.99  
% 3.80/0.99  fof(f44,plain,(
% 3.80/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.80/0.99    inference(cnf_transformation,[],[f13])).
% 3.80/0.99  
% 3.80/0.99  fof(f59,plain,(
% 3.80/0.99    l1_pre_topc(sK3)),
% 3.80/0.99    inference(cnf_transformation,[],[f38])).
% 3.80/0.99  
% 3.80/0.99  fof(f8,axiom,(
% 3.80/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f19,plain,(
% 3.80/0.99    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.80/0.99    inference(ennf_transformation,[],[f8])).
% 3.80/0.99  
% 3.80/0.99  fof(f50,plain,(
% 3.80/0.99    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.80/0.99    inference(cnf_transformation,[],[f19])).
% 3.80/0.99  
% 3.80/0.99  fof(f4,axiom,(
% 3.80/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 3.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f14,plain,(
% 3.80/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.80/0.99    inference(ennf_transformation,[],[f4])).
% 3.80/0.99  
% 3.80/0.99  fof(f45,plain,(
% 3.80/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.80/0.99    inference(cnf_transformation,[],[f14])).
% 3.80/0.99  
% 3.80/0.99  fof(f2,axiom,(
% 3.80/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f27,plain,(
% 3.80/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.80/0.99    inference(nnf_transformation,[],[f2])).
% 3.80/0.99  
% 3.80/0.99  fof(f42,plain,(
% 3.80/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.80/0.99    inference(cnf_transformation,[],[f27])).
% 3.80/0.99  
% 3.80/0.99  fof(f1,axiom,(
% 3.80/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f25,plain,(
% 3.80/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.80/0.99    inference(nnf_transformation,[],[f1])).
% 3.80/0.99  
% 3.80/0.99  fof(f26,plain,(
% 3.80/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.80/0.99    inference(flattening,[],[f25])).
% 3.80/0.99  
% 3.80/0.99  fof(f41,plain,(
% 3.80/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.80/0.99    inference(cnf_transformation,[],[f26])).
% 3.80/0.99  
% 3.80/0.99  fof(f61,plain,(
% 3.80/0.99    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))),
% 3.80/0.99    inference(cnf_transformation,[],[f38])).
% 3.80/0.99  
% 3.80/0.99  fof(f10,axiom,(
% 3.80/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 3.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f21,plain,(
% 3.80/0.99    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.80/0.99    inference(ennf_transformation,[],[f10])).
% 3.80/0.99  
% 3.80/0.99  fof(f22,plain,(
% 3.80/0.99    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.80/0.99    inference(flattening,[],[f21])).
% 3.80/0.99  
% 3.80/0.99  fof(f29,plain,(
% 3.80/0.99    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.80/0.99    inference(nnf_transformation,[],[f22])).
% 3.80/0.99  
% 3.80/0.99  fof(f30,plain,(
% 3.80/0.99    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v3_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.80/0.99    inference(rectify,[],[f29])).
% 3.80/0.99  
% 3.80/0.99  fof(f32,plain,(
% 3.80/0.99    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v3_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4 & v3_pre_topc(sK1(X0,X1,X4),X0) & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.80/0.99    introduced(choice_axiom,[])).
% 3.80/0.99  
% 3.80/0.99  fof(f31,plain,(
% 3.80/0.99    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.80/0.99    introduced(choice_axiom,[])).
% 3.80/0.99  
% 3.80/0.99  fof(f33,plain,(
% 3.80/0.99    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4 & v3_pre_topc(sK1(X0,X1,X4),X0) & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.80/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f32,f31])).
% 3.80/0.99  
% 3.80/0.99  fof(f55,plain,(
% 3.80/0.99    ( ! [X0,X1] : (v2_tex_2(X1,X0) | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.80/0.99    inference(cnf_transformation,[],[f33])).
% 3.80/0.99  
% 3.80/0.99  fof(f60,plain,(
% 3.80/0.99    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))),
% 3.80/0.99    inference(cnf_transformation,[],[f38])).
% 3.80/0.99  
% 3.80/0.99  fof(f63,plain,(
% 3.80/0.99    sK4 = sK5),
% 3.80/0.99    inference(cnf_transformation,[],[f38])).
% 3.80/0.99  
% 3.80/0.99  fof(f54,plain,(
% 3.80/0.99    ( ! [X4,X0,X1] : (k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4 | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.80/0.99    inference(cnf_transformation,[],[f33])).
% 3.80/0.99  
% 3.80/0.99  fof(f64,plain,(
% 3.80/0.99    v2_tex_2(sK4,sK2)),
% 3.80/0.99    inference(cnf_transformation,[],[f38])).
% 3.80/0.99  
% 3.80/0.99  fof(f65,plain,(
% 3.80/0.99    ~v2_tex_2(sK5,sK3)),
% 3.80/0.99    inference(cnf_transformation,[],[f38])).
% 3.80/0.99  
% 3.80/0.99  fof(f56,plain,(
% 3.80/0.99    ( ! [X0,X1] : (v2_tex_2(X1,X0) | r1_tarski(sK0(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.80/0.99    inference(cnf_transformation,[],[f33])).
% 3.80/0.99  
% 3.80/0.99  fof(f57,plain,(
% 3.80/0.99    ( ! [X0,X3,X1] : (v2_tex_2(X1,X0) | k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.80/0.99    inference(cnf_transformation,[],[f33])).
% 3.80/0.99  
% 3.80/0.99  fof(f7,axiom,(
% 3.80/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 3.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.99  
% 3.80/0.99  fof(f17,plain,(
% 3.80/0.99    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v3_pre_topc(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.80/0.99    inference(ennf_transformation,[],[f7])).
% 3.80/0.99  
% 3.80/0.99  fof(f18,plain,(
% 3.80/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.80/0.99    inference(flattening,[],[f17])).
% 3.80/0.99  
% 3.80/0.99  fof(f49,plain,(
% 3.80/0.99    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.80/0.99    inference(cnf_transformation,[],[f18])).
% 3.80/0.99  
% 3.80/0.99  fof(f68,plain,(
% 3.80/0.99    ( ! [X2,X0,X3] : (v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.80/0.99    inference(equality_resolution,[],[f49])).
% 3.80/0.99  
% 3.80/0.99  fof(f52,plain,(
% 3.80/0.99    ( ! [X4,X0,X1] : (m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.80/0.99    inference(cnf_transformation,[],[f33])).
% 3.80/0.99  
% 3.80/0.99  fof(f53,plain,(
% 3.80/0.99    ( ! [X4,X0,X1] : (v3_pre_topc(sK1(X0,X1,X4),X0) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.80/0.99    inference(cnf_transformation,[],[f33])).
% 3.80/0.99  
% 3.80/0.99  cnf(c_12,plain,
% 3.80/0.99      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 3.80/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1871,plain,
% 3.80/0.99      ( m1_pre_topc(X0,X0) = iProver_top
% 3.80/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_22,negated_conjecture,
% 3.80/0.99      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
% 3.80/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7,plain,
% 3.80/0.99      ( m1_pre_topc(X0,X1)
% 3.80/0.99      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.80/0.99      | ~ l1_pre_topc(X1) ),
% 3.80/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1874,plain,
% 3.80/0.99      ( m1_pre_topc(X0,X1) = iProver_top
% 3.80/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 3.80/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3118,plain,
% 3.80/0.99      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.80/0.99      | m1_pre_topc(X0,sK2) = iProver_top
% 3.80/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_22,c_1874]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_26,negated_conjecture,
% 3.80/0.99      ( l1_pre_topc(sK2) ),
% 3.80/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_27,plain,
% 3.80/0.99      ( l1_pre_topc(sK2) = iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3127,plain,
% 3.80/0.99      ( m1_pre_topc(X0,sK2) = iProver_top
% 3.80/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
% 3.80/0.99      inference(global_propositional_subsumption,
% 3.80/0.99                [status(thm)],
% 3.80/0.99                [c_3118,c_27]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3128,plain,
% 3.80/0.99      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.80/0.99      | m1_pre_topc(X0,sK2) = iProver_top ),
% 3.80/0.99      inference(renaming,[status(thm)],[c_3127]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3134,plain,
% 3.80/0.99      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK2) = iProver_top
% 3.80/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_1871,c_3128]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_9,plain,
% 3.80/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.80/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.80/0.99      | ~ l1_pre_topc(X0)
% 3.80/0.99      | ~ l1_pre_topc(X1) ),
% 3.80/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_5,plain,
% 3.80/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.80/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_144,plain,
% 3.80/0.99      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.80/0.99      | ~ m1_pre_topc(X0,X1)
% 3.80/0.99      | ~ l1_pre_topc(X1) ),
% 3.80/0.99      inference(global_propositional_subsumption,[status(thm)],[c_9,c_5]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_145,plain,
% 3.80/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.80/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.80/0.99      | ~ l1_pre_topc(X1) ),
% 3.80/0.99      inference(renaming,[status(thm)],[c_144]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1858,plain,
% 3.80/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.80/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 3.80/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_145]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3133,plain,
% 3.80/0.99      ( m1_pre_topc(X0,sK2) = iProver_top
% 3.80/0.99      | m1_pre_topc(X0,sK3) != iProver_top
% 3.80/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_1858,c_3128]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_25,negated_conjecture,
% 3.80/0.99      ( l1_pre_topc(sK3) ),
% 3.80/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_28,plain,
% 3.80/0.99      ( l1_pre_topc(sK3) = iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3325,plain,
% 3.80/0.99      ( m1_pre_topc(X0,sK3) != iProver_top
% 3.80/0.99      | m1_pre_topc(X0,sK2) = iProver_top ),
% 3.80/0.99      inference(global_propositional_subsumption,
% 3.80/0.99                [status(thm)],
% 3.80/0.99                [c_3133,c_28]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3326,plain,
% 3.80/0.99      ( m1_pre_topc(X0,sK2) = iProver_top
% 3.80/0.99      | m1_pre_topc(X0,sK3) != iProver_top ),
% 3.80/0.99      inference(renaming,[status(thm)],[c_3325]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3331,plain,
% 3.80/0.99      ( m1_pre_topc(sK3,sK2) = iProver_top
% 3.80/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_1871,c_3326]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3464,plain,
% 3.80/0.99      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 3.80/0.99      inference(global_propositional_subsumption,
% 3.80/0.99                [status(thm)],
% 3.80/0.99                [c_3331,c_28]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_11,plain,
% 3.80/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.80/0.99      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.80/0.99      | ~ l1_pre_topc(X1) ),
% 3.80/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1872,plain,
% 3.80/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.80/0.99      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.80/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_6,plain,
% 3.80/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.80/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 3.80/0.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.80/0.99      | ~ l1_pre_topc(X1) ),
% 3.80/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1875,plain,
% 3.80/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.80/0.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.80/0.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.80/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3642,plain,
% 3.80/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.80/0.99      | m1_pre_topc(X1,X2) != iProver_top
% 3.80/0.99      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X2))) = iProver_top
% 3.80/0.99      | l1_pre_topc(X1) != iProver_top
% 3.80/0.99      | l1_pre_topc(X2) != iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_1872,c_1875]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7537,plain,
% 3.80/0.99      ( m1_pre_topc(sK2,X0) != iProver_top
% 3.80/0.99      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 3.80/0.99      | l1_pre_topc(X0) != iProver_top
% 3.80/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_3464,c_3642]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_13866,plain,
% 3.80/0.99      ( l1_pre_topc(X0) != iProver_top
% 3.80/0.99      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 3.80/0.99      | m1_pre_topc(sK2,X0) != iProver_top ),
% 3.80/0.99      inference(global_propositional_subsumption,
% 3.80/0.99                [status(thm)],
% 3.80/0.99                [c_7537,c_27]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_13867,plain,
% 3.80/0.99      ( m1_pre_topc(sK2,X0) != iProver_top
% 3.80/0.99      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 3.80/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.80/0.99      inference(renaming,[status(thm)],[c_13866]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_13871,plain,
% 3.80/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.80/0.99      | m1_pre_topc(sK2,X0) != iProver_top
% 3.80/0.99      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.80/0.99      | l1_pre_topc(X1) != iProver_top
% 3.80/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_13867,c_1875]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_64,plain,
% 3.80/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.80/0.99      | l1_pre_topc(X1) != iProver_top
% 3.80/0.99      | l1_pre_topc(X0) = iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_14368,plain,
% 3.80/0.99      ( l1_pre_topc(X1) != iProver_top
% 3.80/0.99      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.80/0.99      | m1_pre_topc(sK2,X0) != iProver_top
% 3.80/0.99      | m1_pre_topc(X0,X1) != iProver_top ),
% 3.80/0.99      inference(global_propositional_subsumption,
% 3.80/0.99                [status(thm)],
% 3.80/0.99                [c_13871,c_64]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_14369,plain,
% 3.80/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.80/0.99      | m1_pre_topc(sK2,X0) != iProver_top
% 3.80/0.99      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.80/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.80/0.99      inference(renaming,[status(thm)],[c_14368]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_14380,plain,
% 3.80/0.99      ( m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.80/0.99      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.80/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.80/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_3134,c_14369]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_51,plain,
% 3.80/0.99      ( m1_pre_topc(X0,X0) = iProver_top
% 3.80/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_53,plain,
% 3.80/0.99      ( m1_pre_topc(sK2,sK2) = iProver_top
% 3.80/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_51]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7548,plain,
% 3.80/0.99      ( m1_pre_topc(sK2,sK2) != iProver_top
% 3.80/0.99      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.80/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_7537]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_14540,plain,
% 3.80/0.99      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.80/0.99      inference(global_propositional_subsumption,
% 3.80/0.99                [status(thm)],
% 3.80/0.99                [c_14380,c_27,c_53,c_7548]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_4,plain,
% 3.80/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.80/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1877,plain,
% 3.80/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.80/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_14544,plain,
% 3.80/0.99      ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_14540,c_1877]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_0,plain,
% 3.80/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.80/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1880,plain,
% 3.80/0.99      ( X0 = X1
% 3.80/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.80/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_14904,plain,
% 3.80/0.99      ( u1_struct_0(sK3) = u1_struct_0(sK2)
% 3.80/0.99      | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_14544,c_1880]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2384,plain,
% 3.80/0.99      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 3.80/0.99      | m1_pre_topc(X0,sK2) != iProver_top
% 3.80/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_22,c_1858]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2552,plain,
% 3.80/0.99      ( m1_pre_topc(X0,sK2) != iProver_top
% 3.80/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
% 3.80/0.99      inference(global_propositional_subsumption,
% 3.80/0.99                [status(thm)],
% 3.80/0.99                [c_2384,c_27]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2553,plain,
% 3.80/0.99      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 3.80/0.99      | m1_pre_topc(X0,sK2) != iProver_top ),
% 3.80/0.99      inference(renaming,[status(thm)],[c_2552]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3117,plain,
% 3.80/0.99      ( m1_pre_topc(X0,sK2) != iProver_top
% 3.80/0.99      | m1_pre_topc(X0,sK3) = iProver_top
% 3.80/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_2553,c_1874]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3249,plain,
% 3.80/0.99      ( m1_pre_topc(X0,sK3) = iProver_top
% 3.80/0.99      | m1_pre_topc(X0,sK2) != iProver_top ),
% 3.80/0.99      inference(global_propositional_subsumption,
% 3.80/0.99                [status(thm)],
% 3.80/0.99                [c_3117,c_28]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3250,plain,
% 3.80/0.99      ( m1_pre_topc(X0,sK2) != iProver_top
% 3.80/0.99      | m1_pre_topc(X0,sK3) = iProver_top ),
% 3.80/0.99      inference(renaming,[status(thm)],[c_3249]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3335,plain,
% 3.80/0.99      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK3) = iProver_top
% 3.80/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_3134,c_3250]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7540,plain,
% 3.80/0.99      ( m1_pre_topc(X0,sK2) != iProver_top
% 3.80/0.99      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X1) != iProver_top
% 3.80/0.99      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.80/0.99      | l1_pre_topc(X1) != iProver_top
% 3.80/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_2553,c_3642]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7803,plain,
% 3.80/0.99      ( m1_pre_topc(X0,sK2) != iProver_top
% 3.80/0.99      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 3.80/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.80/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_3335,c_7540]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2610,plain,
% 3.80/0.99      ( ~ m1_pre_topc(X0,sK3)
% 3.80/0.99      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.80/0.99      | ~ l1_pre_topc(sK3) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2611,plain,
% 3.80/0.99      ( m1_pre_topc(X0,sK3) != iProver_top
% 3.80/0.99      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 3.80/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_2610]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7947,plain,
% 3.80/0.99      ( m1_pre_topc(X0,sK2) != iProver_top
% 3.80/0.99      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.80/0.99      inference(global_propositional_subsumption,
% 3.80/0.99                [status(thm)],
% 3.80/0.99                [c_7803,c_28,c_2611,c_3117]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7953,plain,
% 3.80/0.99      ( m1_pre_topc(X0,sK2) != iProver_top
% 3.80/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) = iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_7947,c_1877]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_7959,plain,
% 3.80/0.99      ( m1_pre_topc(sK2,sK2) != iProver_top
% 3.80/0.99      | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_7953]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_14991,plain,
% 3.80/0.99      ( u1_struct_0(sK3) = u1_struct_0(sK2) ),
% 3.80/0.99      inference(global_propositional_subsumption,
% 3.80/0.99                [status(thm)],
% 3.80/0.99                [c_14904,c_27,c_53,c_7959]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_23,negated_conjecture,
% 3.80/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.80/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1862,plain,
% 3.80/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_15,plain,
% 3.80/0.99      ( v2_tex_2(X0,X1)
% 3.80/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.80/0.99      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.80/0.99      | ~ l1_pre_topc(X1) ),
% 3.80/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1868,plain,
% 3.80/0.99      ( v2_tex_2(X0,X1) = iProver_top
% 3.80/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.80/0.99      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.80/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3655,plain,
% 3.80/0.99      ( v2_tex_2(X0,X1) = iProver_top
% 3.80/0.99      | m1_pre_topc(X1,X2) != iProver_top
% 3.80/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.80/0.99      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X2))) = iProver_top
% 3.80/0.99      | l1_pre_topc(X1) != iProver_top
% 3.80/0.99      | l1_pre_topc(X2) != iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_1868,c_1875]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_24,negated_conjecture,
% 3.80/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.80/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1861,plain,
% 3.80/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_21,negated_conjecture,
% 3.80/0.99      ( sK4 = sK5 ),
% 3.80/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1882,plain,
% 3.80/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.80/0.99      inference(light_normalisation,[status(thm)],[c_1861,c_21]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_16,plain,
% 3.80/0.99      ( ~ v2_tex_2(X0,X1)
% 3.80/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.80/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.80/0.99      | ~ r1_tarski(X2,X0)
% 3.80/0.99      | ~ l1_pre_topc(X1)
% 3.80/0.99      | k9_subset_1(u1_struct_0(X1),X0,sK1(X1,X0,X2)) = X2 ),
% 3.80/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1867,plain,
% 3.80/0.99      ( k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X2)) = X2
% 3.80/0.99      | v2_tex_2(X1,X0) != iProver_top
% 3.80/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.80/0.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.80/0.99      | r1_tarski(X2,X1) != iProver_top
% 3.80/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_4355,plain,
% 3.80/0.99      ( k9_subset_1(u1_struct_0(sK2),sK5,sK1(sK2,sK5,X0)) = X0
% 3.80/0.99      | v2_tex_2(sK5,sK2) != iProver_top
% 3.80/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.80/0.99      | r1_tarski(X0,sK5) != iProver_top
% 3.80/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_1882,c_1867]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_20,negated_conjecture,
% 3.80/0.99      ( v2_tex_2(sK4,sK2) ),
% 3.80/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1863,plain,
% 3.80/0.99      ( v2_tex_2(sK4,sK2) = iProver_top ),
% 3.80/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1881,plain,
% 3.80/0.99      ( v2_tex_2(sK5,sK2) = iProver_top ),
% 3.80/0.99      inference(light_normalisation,[status(thm)],[c_1863,c_21]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_4584,plain,
% 3.80/0.99      ( r1_tarski(X0,sK5) != iProver_top
% 3.80/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.80/0.99      | k9_subset_1(u1_struct_0(sK2),sK5,sK1(sK2,sK5,X0)) = X0 ),
% 3.80/0.99      inference(global_propositional_subsumption,
% 3.80/0.99                [status(thm)],
% 3.80/0.99                [c_4355,c_27,c_1881]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_4585,plain,
% 3.80/0.99      ( k9_subset_1(u1_struct_0(sK2),sK5,sK1(sK2,sK5,X0)) = X0
% 3.80/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.80/0.99      | r1_tarski(X0,sK5) != iProver_top ),
% 3.80/0.99      inference(renaming,[status(thm)],[c_4584]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_9247,plain,
% 3.80/0.99      ( k9_subset_1(u1_struct_0(sK2),sK5,sK1(sK2,sK5,sK0(X0,X1))) = sK0(X0,X1)
% 3.80/0.99      | v2_tex_2(X1,X0) = iProver_top
% 3.80/0.99      | m1_pre_topc(X0,sK2) != iProver_top
% 3.80/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.80/0.99      | r1_tarski(sK0(X0,X1),sK5) != iProver_top
% 3.80/0.99      | l1_pre_topc(X0) != iProver_top
% 3.80/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_3655,c_4585]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_12657,plain,
% 3.80/0.99      ( l1_pre_topc(X0) != iProver_top
% 3.80/0.99      | r1_tarski(sK0(X0,X1),sK5) != iProver_top
% 3.80/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.80/0.99      | m1_pre_topc(X0,sK2) != iProver_top
% 3.80/0.99      | v2_tex_2(X1,X0) = iProver_top
% 3.80/0.99      | k9_subset_1(u1_struct_0(sK2),sK5,sK1(sK2,sK5,sK0(X0,X1))) = sK0(X0,X1) ),
% 3.80/0.99      inference(global_propositional_subsumption,
% 3.80/0.99                [status(thm)],
% 3.80/0.99                [c_9247,c_27]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_12658,plain,
% 3.80/0.99      ( k9_subset_1(u1_struct_0(sK2),sK5,sK1(sK2,sK5,sK0(X0,X1))) = sK0(X0,X1)
% 3.80/0.99      | v2_tex_2(X1,X0) = iProver_top
% 3.80/0.99      | m1_pre_topc(X0,sK2) != iProver_top
% 3.80/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.80/0.99      | r1_tarski(sK0(X0,X1),sK5) != iProver_top
% 3.80/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.80/0.99      inference(renaming,[status(thm)],[c_12657]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_12666,plain,
% 3.80/0.99      ( k9_subset_1(u1_struct_0(sK2),sK5,sK1(sK2,sK5,sK0(sK3,sK5))) = sK0(sK3,sK5)
% 3.80/0.99      | v2_tex_2(sK5,sK3) = iProver_top
% 3.80/0.99      | m1_pre_topc(sK3,sK2) != iProver_top
% 3.80/0.99      | r1_tarski(sK0(sK3,sK5),sK5) != iProver_top
% 3.80/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 3.80/0.99      inference(superposition,[status(thm)],[c_1862,c_12658]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_19,negated_conjecture,
% 3.80/0.99      ( ~ v2_tex_2(sK5,sK3) ),
% 3.80/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_543,plain,
% 3.80/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.80/0.99      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.80/0.99      | ~ l1_pre_topc(X1)
% 3.80/0.99      | sK3 != X1
% 3.80/0.99      | sK5 != X0 ),
% 3.80/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_19]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_544,plain,
% 3.80/0.99      ( m1_subset_1(sK0(sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.80/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.80/0.99      | ~ l1_pre_topc(sK3) ),
% 3.80/0.99      inference(unflattening,[status(thm)],[c_543]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_14,plain,
% 3.80/0.99      ( v2_tex_2(X0,X1)
% 3.80/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.80/0.99      | r1_tarski(sK0(X1,X0),X0)
% 3.80/0.99      | ~ l1_pre_topc(X1) ),
% 3.80/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_554,plain,
% 3.80/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.80/0.99      | r1_tarski(sK0(X1,X0),X0)
% 3.80/0.99      | ~ l1_pre_topc(X1)
% 3.80/0.99      | sK3 != X1
% 3.80/0.99      | sK5 != X0 ),
% 3.80/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_19]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_555,plain,
% 3.80/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.80/0.99      | r1_tarski(sK0(sK3,sK5),sK5)
% 3.80/0.99      | ~ l1_pre_topc(sK3) ),
% 3.80/0.99      inference(unflattening,[status(thm)],[c_554]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1888,plain,
% 3.80/0.99      ( v2_tex_2(sK5,sK2) ),
% 3.80/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1881]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1896,plain,
% 3.80/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.80/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1882]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2098,plain,
% 3.80/0.99      ( ~ m1_pre_topc(sK3,X0)
% 3.80/0.99      | m1_subset_1(sK0(sK3,sK5),k1_zfmisc_1(u1_struct_0(X0)))
% 3.80/0.99      | ~ m1_subset_1(sK0(sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.80/0.99      | ~ l1_pre_topc(X0) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2100,plain,
% 3.80/0.99      ( ~ m1_pre_topc(sK3,sK2)
% 3.80/0.99      | m1_subset_1(sK0(sK3,sK5),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.80/0.99      | ~ m1_subset_1(sK0(sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.80/0.99      | ~ l1_pre_topc(sK2) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_2098]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3332,plain,
% 3.80/0.99      ( m1_pre_topc(sK3,sK2) | ~ l1_pre_topc(sK3) ),
% 3.80/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3331]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_5907,plain,
% 3.80/0.99      ( ~ v2_tex_2(X0,X1)
% 3.80/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.80/0.99      | ~ m1_subset_1(sK0(sK3,sK5),k1_zfmisc_1(u1_struct_0(X1)))
% 3.80/0.99      | ~ r1_tarski(sK0(sK3,sK5),X0)
% 3.80/0.99      | ~ l1_pre_topc(X1)
% 3.80/0.99      | k9_subset_1(u1_struct_0(X1),X0,sK1(X1,X0,sK0(sK3,sK5))) = sK0(sK3,sK5) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_12614,plain,
% 3.80/0.99      ( ~ v2_tex_2(sK5,X0)
% 3.80/0.99      | ~ m1_subset_1(sK0(sK3,sK5),k1_zfmisc_1(u1_struct_0(X0)))
% 3.80/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 3.80/0.99      | ~ r1_tarski(sK0(sK3,sK5),sK5)
% 3.80/0.99      | ~ l1_pre_topc(X0)
% 3.80/0.99      | k9_subset_1(u1_struct_0(X0),sK5,sK1(X0,sK5,sK0(sK3,sK5))) = sK0(sK3,sK5) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_5907]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_12616,plain,
% 3.80/0.99      ( ~ v2_tex_2(sK5,sK2)
% 3.80/0.99      | ~ m1_subset_1(sK0(sK3,sK5),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.80/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.80/0.99      | ~ r1_tarski(sK0(sK3,sK5),sK5)
% 3.80/0.99      | ~ l1_pre_topc(sK2)
% 3.80/0.99      | k9_subset_1(u1_struct_0(sK2),sK5,sK1(sK2,sK5,sK0(sK3,sK5))) = sK0(sK3,sK5) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_12614]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_13646,plain,
% 3.80/0.99      ( k9_subset_1(u1_struct_0(sK2),sK5,sK1(sK2,sK5,sK0(sK3,sK5))) = sK0(sK3,sK5) ),
% 3.80/0.99      inference(global_propositional_subsumption,
% 3.80/0.99                [status(thm)],
% 3.80/0.99                [c_12666,c_26,c_25,c_23,c_544,c_555,c_1888,c_1896,c_2100,
% 3.80/0.99                 c_3332,c_12616]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_15000,plain,
% 3.80/0.99      ( k9_subset_1(u1_struct_0(sK3),sK5,sK1(sK2,sK5,sK0(sK3,sK5))) = sK0(sK3,sK5) ),
% 3.80/0.99      inference(demodulation,[status(thm)],[c_14991,c_13646]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_13,plain,
% 3.80/0.99      ( v2_tex_2(X0,X1)
% 3.80/0.99      | ~ v3_pre_topc(X2,X1)
% 3.80/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.80/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.80/0.99      | ~ l1_pre_topc(X1)
% 3.80/0.99      | k9_subset_1(u1_struct_0(X1),X0,X2) != sK0(X1,X0) ),
% 3.80/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1912,plain,
% 3.80/0.99      ( v2_tex_2(sK5,sK3)
% 3.80/0.99      | ~ v3_pre_topc(X0,sK3)
% 3.80/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.80/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.80/0.99      | ~ l1_pre_topc(sK3)
% 3.80/0.99      | k9_subset_1(u1_struct_0(sK3),sK5,X0) != sK0(sK3,sK5) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_9046,plain,
% 3.80/0.99      ( v2_tex_2(sK5,sK3)
% 3.80/0.99      | ~ v3_pre_topc(sK1(X0,sK5,sK0(sK3,sK5)),sK3)
% 3.80/0.99      | ~ m1_subset_1(sK1(X0,sK5,sK0(sK3,sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.80/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.80/0.99      | ~ l1_pre_topc(sK3)
% 3.80/0.99      | k9_subset_1(u1_struct_0(sK3),sK5,sK1(X0,sK5,sK0(sK3,sK5))) != sK0(sK3,sK5) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_1912]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_9050,plain,
% 3.80/0.99      ( v2_tex_2(sK5,sK3)
% 3.80/0.99      | ~ v3_pre_topc(sK1(sK2,sK5,sK0(sK3,sK5)),sK3)
% 3.80/0.99      | ~ m1_subset_1(sK1(sK2,sK5,sK0(sK3,sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.80/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.80/0.99      | ~ l1_pre_topc(sK3)
% 3.80/0.99      | k9_subset_1(u1_struct_0(sK3),sK5,sK1(sK2,sK5,sK0(sK3,sK5))) != sK0(sK3,sK5) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_9046]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_10,plain,
% 3.80/0.99      ( ~ v3_pre_topc(X0,X1)
% 3.80/0.99      | v3_pre_topc(X0,X2)
% 3.80/0.99      | ~ m1_pre_topc(X2,X1)
% 3.80/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 3.80/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.80/0.99      | ~ l1_pre_topc(X1) ),
% 3.80/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_1926,plain,
% 3.80/0.99      ( ~ v3_pre_topc(X0,X1)
% 3.80/0.99      | v3_pre_topc(X0,sK3)
% 3.80/0.99      | ~ m1_pre_topc(sK3,X1)
% 3.80/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.80/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.80/0.99      | ~ l1_pre_topc(X1) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_8681,plain,
% 3.80/0.99      ( ~ v3_pre_topc(sK1(X0,sK5,sK0(sK3,sK5)),X1)
% 3.80/0.99      | v3_pre_topc(sK1(X0,sK5,sK0(sK3,sK5)),sK3)
% 3.80/0.99      | ~ m1_pre_topc(sK3,X1)
% 3.80/0.99      | ~ m1_subset_1(sK1(X0,sK5,sK0(sK3,sK5)),k1_zfmisc_1(u1_struct_0(X1)))
% 3.80/0.99      | ~ m1_subset_1(sK1(X0,sK5,sK0(sK3,sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.80/0.99      | ~ l1_pre_topc(X1) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_1926]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_8702,plain,
% 3.80/0.99      ( ~ v3_pre_topc(sK1(sK2,sK5,sK0(sK3,sK5)),sK2)
% 3.80/0.99      | v3_pre_topc(sK1(sK2,sK5,sK0(sK3,sK5)),sK3)
% 3.80/0.99      | ~ m1_pre_topc(sK3,sK2)
% 3.80/0.99      | ~ m1_subset_1(sK1(sK2,sK5,sK0(sK3,sK5)),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.80/0.99      | ~ m1_subset_1(sK1(sK2,sK5,sK0(sK3,sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.80/0.99      | ~ l1_pre_topc(sK2) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_8681]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2107,plain,
% 3.80/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.80/0.99      | ~ m1_subset_1(sK1(X0,X2,X3),k1_zfmisc_1(u1_struct_0(X0)))
% 3.80/0.99      | m1_subset_1(sK1(X0,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
% 3.80/0.99      | ~ l1_pre_topc(X1) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_6871,plain,
% 3.80/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.80/0.99      | ~ m1_subset_1(sK1(X0,sK5,sK0(sK3,sK5)),k1_zfmisc_1(u1_struct_0(X0)))
% 3.80/0.99      | m1_subset_1(sK1(X0,sK5,sK0(sK3,sK5)),k1_zfmisc_1(u1_struct_0(X1)))
% 3.80/0.99      | ~ l1_pre_topc(X1) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_2107]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_8680,plain,
% 3.80/0.99      ( ~ m1_pre_topc(X0,sK3)
% 3.80/0.99      | ~ m1_subset_1(sK1(X0,sK5,sK0(sK3,sK5)),k1_zfmisc_1(u1_struct_0(X0)))
% 3.80/0.99      | m1_subset_1(sK1(X0,sK5,sK0(sK3,sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.80/0.99      | ~ l1_pre_topc(sK3) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_6871]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_8686,plain,
% 3.80/0.99      ( ~ m1_pre_topc(sK2,sK3)
% 3.80/0.99      | ~ m1_subset_1(sK1(sK2,sK5,sK0(sK3,sK5)),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.80/0.99      | m1_subset_1(sK1(sK2,sK5,sK0(sK3,sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.80/0.99      | ~ l1_pre_topc(sK3) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_8680]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_18,plain,
% 3.80/0.99      ( ~ v2_tex_2(X0,X1)
% 3.80/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.80/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.80/0.99      | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 3.80/0.99      | ~ r1_tarski(X2,X0)
% 3.80/0.99      | ~ l1_pre_topc(X1) ),
% 3.80/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3027,plain,
% 3.80/0.99      ( ~ v2_tex_2(sK5,X0)
% 3.80/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.80/0.99      | m1_subset_1(sK1(X0,sK5,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 3.80/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 3.80/0.99      | ~ r1_tarski(X1,sK5)
% 3.80/0.99      | ~ l1_pre_topc(X0) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_18]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_5393,plain,
% 3.80/0.99      ( ~ v2_tex_2(sK5,X0)
% 3.80/0.99      | m1_subset_1(sK1(X0,sK5,sK0(sK3,sK5)),k1_zfmisc_1(u1_struct_0(X0)))
% 3.80/0.99      | ~ m1_subset_1(sK0(sK3,sK5),k1_zfmisc_1(u1_struct_0(X0)))
% 3.80/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 3.80/0.99      | ~ r1_tarski(sK0(sK3,sK5),sK5)
% 3.80/0.99      | ~ l1_pre_topc(X0) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_3027]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_5395,plain,
% 3.80/0.99      ( ~ v2_tex_2(sK5,sK2)
% 3.80/0.99      | m1_subset_1(sK1(sK2,sK5,sK0(sK3,sK5)),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.80/0.99      | ~ m1_subset_1(sK0(sK3,sK5),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.80/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.80/0.99      | ~ r1_tarski(sK0(sK3,sK5),sK5)
% 3.80/0.99      | ~ l1_pre_topc(sK2) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_5393]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_17,plain,
% 3.80/0.99      ( ~ v2_tex_2(X0,X1)
% 3.80/0.99      | v3_pre_topc(sK1(X1,X0,X2),X1)
% 3.80/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.80/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.80/0.99      | ~ r1_tarski(X2,X0)
% 3.80/0.99      | ~ l1_pre_topc(X1) ),
% 3.80/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_3026,plain,
% 3.80/0.99      ( ~ v2_tex_2(sK5,X0)
% 3.80/0.99      | v3_pre_topc(sK1(X0,sK5,X1),X0)
% 3.80/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.80/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 3.80/0.99      | ~ r1_tarski(X1,sK5)
% 3.80/0.99      | ~ l1_pre_topc(X0) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_5381,plain,
% 3.80/0.99      ( ~ v2_tex_2(sK5,X0)
% 3.80/0.99      | v3_pre_topc(sK1(X0,sK5,sK0(sK3,sK5)),X0)
% 3.80/0.99      | ~ m1_subset_1(sK0(sK3,sK5),k1_zfmisc_1(u1_struct_0(X0)))
% 3.80/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 3.80/0.99      | ~ r1_tarski(sK0(sK3,sK5),sK5)
% 3.80/0.99      | ~ l1_pre_topc(X0) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_3026]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_5383,plain,
% 3.80/0.99      ( ~ v2_tex_2(sK5,sK2)
% 3.80/0.99      | v3_pre_topc(sK1(sK2,sK5,sK0(sK3,sK5)),sK2)
% 3.80/0.99      | ~ m1_subset_1(sK0(sK3,sK5),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.80/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.80/0.99      | ~ r1_tarski(sK0(sK3,sK5),sK5)
% 3.80/0.99      | ~ l1_pre_topc(sK2) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_5381]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2922,plain,
% 3.80/0.99      ( ~ m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 3.80/0.99      | m1_pre_topc(sK2,sK3)
% 3.80/0.99      | ~ l1_pre_topc(sK3) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2385,plain,
% 3.80/0.99      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 3.80/0.99      | ~ m1_pre_topc(X0,sK2)
% 3.80/0.99      | ~ l1_pre_topc(sK2) ),
% 3.80/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2384]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_2387,plain,
% 3.80/0.99      ( m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 3.80/0.99      | ~ m1_pre_topc(sK2,sK2)
% 3.80/0.99      | ~ l1_pre_topc(sK2) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_2385]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(c_52,plain,
% 3.80/0.99      ( m1_pre_topc(sK2,sK2) | ~ l1_pre_topc(sK2) ),
% 3.80/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 3.80/0.99  
% 3.80/0.99  cnf(contradiction,plain,
% 3.80/0.99      ( $false ),
% 3.80/0.99      inference(minisat,
% 3.80/0.99                [status(thm)],
% 3.80/0.99                [c_15000,c_9050,c_8702,c_8686,c_5395,c_5383,c_3332,
% 3.80/0.99                 c_2922,c_2387,c_2100,c_1896,c_1888,c_555,c_544,c_52,
% 3.80/0.99                 c_19,c_23,c_25,c_26]) ).
% 3.80/0.99  
% 3.80/0.99  
% 3.80/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.80/0.99  
% 3.80/0.99  ------                               Statistics
% 3.80/0.99  
% 3.80/0.99  ------ General
% 3.80/0.99  
% 3.80/0.99  abstr_ref_over_cycles:                  0
% 3.80/0.99  abstr_ref_under_cycles:                 0
% 3.80/0.99  gc_basic_clause_elim:                   0
% 3.80/0.99  forced_gc_time:                         0
% 3.80/0.99  parsing_time:                           0.007
% 3.80/0.99  unif_index_cands_time:                  0.
% 3.80/0.99  unif_index_add_time:                    0.
% 3.80/0.99  orderings_time:                         0.
% 3.80/0.99  out_proof_time:                         0.017
% 3.80/0.99  total_time:                             0.476
% 3.80/0.99  num_of_symbols:                         48
% 3.80/0.99  num_of_terms:                           13750
% 3.80/0.99  
% 3.80/0.99  ------ Preprocessing
% 3.80/0.99  
% 3.80/0.99  num_of_splits:                          0
% 3.80/0.99  num_of_split_atoms:                     0
% 3.80/0.99  num_of_reused_defs:                     0
% 3.80/0.99  num_eq_ax_congr_red:                    27
% 3.80/0.99  num_of_sem_filtered_clauses:            1
% 3.80/0.99  num_of_subtypes:                        0
% 3.80/0.99  monotx_restored_types:                  0
% 3.80/0.99  sat_num_of_epr_types:                   0
% 3.80/0.99  sat_num_of_non_cyclic_types:            0
% 3.80/0.99  sat_guarded_non_collapsed_types:        0
% 3.80/0.99  num_pure_diseq_elim:                    0
% 3.80/0.99  simp_replaced_by:                       0
% 3.80/0.99  res_preprocessed:                       127
% 3.80/0.99  prep_upred:                             0
% 3.80/0.99  prep_unflattend:                        24
% 3.80/0.99  smt_new_axioms:                         0
% 3.80/0.99  pred_elim_cands:                        6
% 3.80/0.99  pred_elim:                              0
% 3.80/0.99  pred_elim_cl:                           0
% 3.80/0.99  pred_elim_cycles:                       2
% 3.80/0.99  merged_defs:                            8
% 3.80/0.99  merged_defs_ncl:                        0
% 3.80/0.99  bin_hyper_res:                          8
% 3.80/0.99  prep_cycles:                            4
% 3.80/0.99  pred_elim_time:                         0.01
% 3.80/0.99  splitting_time:                         0.
% 3.80/0.99  sem_filter_time:                        0.
% 3.80/0.99  monotx_time:                            0.
% 3.80/0.99  subtype_inf_time:                       0.
% 3.80/0.99  
% 3.80/0.99  ------ Problem properties
% 3.80/0.99  
% 3.80/0.99  clauses:                                25
% 3.80/0.99  conjectures:                            8
% 3.80/0.99  epr:                                    9
% 3.80/0.99  horn:                                   23
% 3.80/0.99  ground:                                 8
% 3.80/0.99  unary:                                  9
% 3.80/0.99  binary:                                 3
% 3.80/0.99  lits:                                   72
% 3.80/0.99  lits_eq:                                5
% 3.80/0.99  fd_pure:                                0
% 3.80/0.99  fd_pseudo:                              0
% 3.80/0.99  fd_cond:                                0
% 3.80/0.99  fd_pseudo_cond:                         1
% 3.80/0.99  ac_symbols:                             0
% 3.80/0.99  
% 3.80/0.99  ------ Propositional Solver
% 3.80/0.99  
% 3.80/0.99  prop_solver_calls:                      32
% 3.80/0.99  prop_fast_solver_calls:                 1958
% 3.80/0.99  smt_solver_calls:                       0
% 3.80/0.99  smt_fast_solver_calls:                  0
% 3.80/0.99  prop_num_of_clauses:                    6131
% 3.80/0.99  prop_preprocess_simplified:             14720
% 3.80/0.99  prop_fo_subsumed:                       106
% 3.80/0.99  prop_solver_time:                       0.
% 3.80/0.99  smt_solver_time:                        0.
% 3.80/0.99  smt_fast_solver_time:                   0.
% 3.80/0.99  prop_fast_solver_time:                  0.
% 3.80/0.99  prop_unsat_core_time:                   0.
% 3.80/0.99  
% 3.80/0.99  ------ QBF
% 3.80/0.99  
% 3.80/0.99  qbf_q_res:                              0
% 3.80/0.99  qbf_num_tautologies:                    0
% 3.80/0.99  qbf_prep_cycles:                        0
% 3.80/0.99  
% 3.80/0.99  ------ BMC1
% 3.80/0.99  
% 3.80/0.99  bmc1_current_bound:                     -1
% 3.80/0.99  bmc1_last_solved_bound:                 -1
% 3.80/0.99  bmc1_unsat_core_size:                   -1
% 3.80/0.99  bmc1_unsat_core_parents_size:           -1
% 3.80/0.99  bmc1_merge_next_fun:                    0
% 3.80/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.80/0.99  
% 3.80/0.99  ------ Instantiation
% 3.80/0.99  
% 3.80/0.99  inst_num_of_clauses:                    1661
% 3.80/0.99  inst_num_in_passive:                    705
% 3.80/0.99  inst_num_in_active:                     808
% 3.80/0.99  inst_num_in_unprocessed:                148
% 3.80/0.99  inst_num_of_loops:                      950
% 3.80/0.99  inst_num_of_learning_restarts:          0
% 3.80/0.99  inst_num_moves_active_passive:          138
% 3.80/0.99  inst_lit_activity:                      0
% 3.80/0.99  inst_lit_activity_moves:                0
% 3.80/0.99  inst_num_tautologies:                   0
% 3.80/0.99  inst_num_prop_implied:                  0
% 3.80/0.99  inst_num_existing_simplified:           0
% 3.80/0.99  inst_num_eq_res_simplified:             0
% 3.80/0.99  inst_num_child_elim:                    0
% 3.80/0.99  inst_num_of_dismatching_blockings:      1220
% 3.80/0.99  inst_num_of_non_proper_insts:           2494
% 3.80/0.99  inst_num_of_duplicates:                 0
% 3.80/0.99  inst_inst_num_from_inst_to_res:         0
% 3.80/0.99  inst_dismatching_checking_time:         0.
% 3.80/0.99  
% 3.80/0.99  ------ Resolution
% 3.80/0.99  
% 3.80/0.99  res_num_of_clauses:                     0
% 3.80/0.99  res_num_in_passive:                     0
% 3.80/0.99  res_num_in_active:                      0
% 3.80/0.99  res_num_of_loops:                       131
% 3.80/0.99  res_forward_subset_subsumed:            189
% 3.80/0.99  res_backward_subset_subsumed:           2
% 3.80/0.99  res_forward_subsumed:                   0
% 3.80/0.99  res_backward_subsumed:                  0
% 3.80/0.99  res_forward_subsumption_resolution:     0
% 3.80/0.99  res_backward_subsumption_resolution:    0
% 3.80/0.99  res_clause_to_clause_subsumption:       1635
% 3.80/0.99  res_orphan_elimination:                 0
% 3.80/0.99  res_tautology_del:                      210
% 3.80/0.99  res_num_eq_res_simplified:              0
% 3.80/0.99  res_num_sel_changes:                    0
% 3.80/0.99  res_moves_from_active_to_pass:          0
% 3.80/0.99  
% 3.80/0.99  ------ Superposition
% 3.80/0.99  
% 3.80/0.99  sup_time_total:                         0.
% 3.80/0.99  sup_time_generating:                    0.
% 3.80/0.99  sup_time_sim_full:                      0.
% 3.80/0.99  sup_time_sim_immed:                     0.
% 3.80/0.99  
% 3.80/0.99  sup_num_of_clauses:                     394
% 3.80/0.99  sup_num_in_active:                      164
% 3.80/0.99  sup_num_in_passive:                     230
% 3.80/0.99  sup_num_of_loops:                       188
% 3.80/0.99  sup_fw_superposition:                   475
% 3.80/0.99  sup_bw_superposition:                   211
% 3.80/0.99  sup_immediate_simplified:               140
% 3.80/0.99  sup_given_eliminated:                   0
% 3.80/0.99  comparisons_done:                       0
% 3.80/0.99  comparisons_avoided:                    3
% 3.80/0.99  
% 3.80/0.99  ------ Simplifications
% 3.80/0.99  
% 3.80/0.99  
% 3.80/0.99  sim_fw_subset_subsumed:                 71
% 3.80/0.99  sim_bw_subset_subsumed:                 3
% 3.80/0.99  sim_fw_subsumed:                        58
% 3.80/0.99  sim_bw_subsumed:                        10
% 3.80/0.99  sim_fw_subsumption_res:                 0
% 3.80/0.99  sim_bw_subsumption_res:                 0
% 3.80/0.99  sim_tautology_del:                      42
% 3.80/0.99  sim_eq_tautology_del:                   9
% 3.80/0.99  sim_eq_res_simp:                        0
% 3.80/0.99  sim_fw_demodulated:                     0
% 3.80/0.99  sim_bw_demodulated:                     24
% 3.80/0.99  sim_light_normalised:                   8
% 3.80/0.99  sim_joinable_taut:                      0
% 3.80/0.99  sim_joinable_simp:                      0
% 3.80/0.99  sim_ac_normalised:                      0
% 3.80/0.99  sim_smt_subsumption:                    0
% 3.80/0.99  
%------------------------------------------------------------------------------
