%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1857+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:41 EST 2020

% Result     : CounterSatisfiable 2.67s
% Output     : Saturation 2.67s
% Verified   : 
% Statistics : Number of formulae       :  169 (6110 expanded)
%              Number of clauses        :  132 (1600 expanded)
%              Number of leaves         :   11 (1996 expanded)
%              Depth                    :   20
%              Number of atoms          :  779 (44183 expanded)
%              Number of equality atoms :  391 (12830 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   16 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
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

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

fof(f18,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
          & v3_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4
        & v3_pre_topc(sK1(X0,X1,X4),X0)
        & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
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

fof(f19,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f18,f17])).

fof(f27,plain,(
    ! [X4,X0,X1] :
      ( m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,conjecture,(
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

fof(f6,negated_conjecture,(
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
    inference(negated_conjecture,[],[f5])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f23,plain,(
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

fof(f22,plain,(
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

fof(f21,plain,(
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

fof(f20,plain,
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

fof(f24,plain,
    ( ~ v2_tex_2(sK5,sK3)
    & v2_tex_2(sK4,sK2)
    & sK4 = sK5
    & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK3)
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f13,f23,f22,f21,f20])).

fof(f36,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | r1_tarski(sK0(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f37,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f40,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f29,plain,(
    ! [X4,X0,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f39,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f24])).

fof(f43,plain,(
    ~ v2_tex_2(sK5,sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f42,plain,(
    v2_tex_2(sK4,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f41,plain,(
    sK4 = sK5 ),
    inference(cnf_transformation,[],[f24])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( v2_tex_2(X1,X0)
      | k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f28,plain,(
    ! [X4,X0,X1] :
      ( v3_pre_topc(sK1(X0,X1,X4),X0)
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_159,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | m1_subset_1(sK1(X2,X1,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_18,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_518,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | m1_subset_1(sK1(X2,X1,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_18])).

cnf(c_519,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v2_tex_2(X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_518])).

cnf(c_3,plain,
    ( r1_tarski(sK0(X0,X1),X1)
    | v2_tex_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_17,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_418,plain,
    ( r1_tarski(sK0(X0,X1),X1)
    | v2_tex_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_17])).

cnf(c_419,plain,
    ( r1_tarski(sK0(sK3,X0),X0)
    | v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unflattening,[status(thm)],[c_418])).

cnf(c_853,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v2_tex_2(X1,sK3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK1(sK2,X0,X2),k1_zfmisc_1(u1_struct_0(sK2)))
    | X1 != X0
    | sK0(sK3,X1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_519,c_419])).

cnf(c_854,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK1(sK2,X0,sK0(sK3,X0)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_853])).

cnf(c_1494,plain,
    ( v2_tex_2(X0,sK2) != iProver_top
    | v2_tex_2(X0,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK1(sK2,X0,sK0(sK3,X0)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(sK0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_854])).

cnf(c_14,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1507,plain,
    ( X0 = X1
    | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1973,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(X0,X1)
    | u1_struct_0(sK2) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_1507])).

cnf(c_8,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_30,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1974,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(X0,X1)
    | u1_struct_0(sK2) = X0
    | m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_1507])).

cnf(c_1991,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(X0,X1)
    | u1_struct_0(sK2) = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1974])).

cnf(c_2049,plain,
    ( u1_struct_0(sK2) = X0
    | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1973,c_18,c_30,c_1991])).

cnf(c_2050,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(X0,X1)
    | u1_struct_0(sK2) = X0 ),
    inference(renaming,[status(thm)],[c_2049])).

cnf(c_2055,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK2) ),
    inference(equality_resolution,[status(thm)],[c_2050])).

cnf(c_2699,plain,
    ( v2_tex_2(X0,sK2) != iProver_top
    | v2_tex_2(X0,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK1(sK2,X0,sK0(sK3,X0)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1494,c_2055])).

cnf(c_4,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_339,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_17])).

cnf(c_340,plain,
    ( v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unflattening,[status(thm)],[c_339])).

cnf(c_1502,plain,
    ( v2_tex_2(X0,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_340])).

cnf(c_2705,plain,
    ( v2_tex_2(X0,sK2) != iProver_top
    | v2_tex_2(X0,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK1(sK2,X0,sK0(sK3,X0)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2699,c_1502])).

cnf(c_375,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_18])).

cnf(c_376,plain,
    ( v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_375])).

cnf(c_1500,plain,
    ( v2_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_376])).

cnf(c_2422,plain,
    ( v2_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1500,c_2055])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | k9_subset_1(u1_struct_0(X2),X1,sK1(X2,X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_497,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | k9_subset_1(u1_struct_0(X2),X1,sK1(X2,X1,X0)) = X0
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_17])).

cnf(c_498,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v2_tex_2(X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | k9_subset_1(u1_struct_0(sK3),X1,sK1(sK3,X1,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_497])).

cnf(c_440,plain,
    ( r1_tarski(sK0(X0,X1),X1)
    | v2_tex_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_18])).

cnf(c_441,plain,
    ( r1_tarski(sK0(sK2,X0),X0)
    | v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_440])).

cnf(c_889,plain,
    ( v2_tex_2(X0,sK2)
    | ~ v2_tex_2(X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | X0 != X1
    | k9_subset_1(u1_struct_0(sK3),X1,sK1(sK3,X1,X2)) = X2
    | sK0(sK2,X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_498,c_441])).

cnf(c_890,plain,
    ( v2_tex_2(X0,sK2)
    | ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | k9_subset_1(u1_struct_0(sK3),X0,sK1(sK3,X0,sK0(sK2,X0))) = sK0(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_889])).

cnf(c_1493,plain,
    ( k9_subset_1(u1_struct_0(sK3),X0,sK1(sK3,X0,sK0(sK2,X0))) = sK0(sK2,X0)
    | v2_tex_2(X0,sK2) = iProver_top
    | v2_tex_2(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_890])).

cnf(c_891,plain,
    ( k9_subset_1(u1_struct_0(sK3),X0,sK1(sK3,X0,sK0(sK2,X0))) = sK0(sK2,X0)
    | v2_tex_2(X0,sK2) = iProver_top
    | v2_tex_2(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_890])).

cnf(c_2825,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_tex_2(X0,sK3) != iProver_top
    | v2_tex_2(X0,sK2) = iProver_top
    | k9_subset_1(u1_struct_0(sK3),X0,sK1(sK3,X0,sK0(sK2,X0))) = sK0(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1493,c_891,c_2422])).

cnf(c_2826,plain,
    ( k9_subset_1(u1_struct_0(sK3),X0,sK1(sK3,X0,sK0(sK2,X0))) = sK0(sK2,X0)
    | v2_tex_2(X0,sK2) = iProver_top
    | v2_tex_2(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2825])).

cnf(c_2831,plain,
    ( k9_subset_1(u1_struct_0(sK3),X0,sK1(sK3,X0,sK0(sK2,X0))) = sK0(sK2,X0)
    | v2_tex_2(X0,sK2) = iProver_top
    | v2_tex_2(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2826,c_2055])).

cnf(c_2841,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK0(sK2,X0),sK1(sK3,sK0(sK2,X0),sK0(sK2,sK0(sK2,X0)))) = sK0(sK2,sK0(sK2,X0))
    | v2_tex_2(X0,sK2) = iProver_top
    | v2_tex_2(sK0(sK2,X0),sK2) = iProver_top
    | v2_tex_2(sK0(sK2,X0),sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2422,c_2831])).

cnf(c_3342,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK0(sK2,sK1(sK2,X0,sK0(sK3,X0))),sK1(sK3,sK0(sK2,sK1(sK2,X0,sK0(sK3,X0))),sK0(sK2,sK0(sK2,sK1(sK2,X0,sK0(sK3,X0)))))) = sK0(sK2,sK0(sK2,sK1(sK2,X0,sK0(sK3,X0))))
    | v2_tex_2(X0,sK2) != iProver_top
    | v2_tex_2(X0,sK3) = iProver_top
    | v2_tex_2(sK1(sK2,X0,sK0(sK3,X0)),sK2) = iProver_top
    | v2_tex_2(sK0(sK2,sK1(sK2,X0,sK0(sK3,X0))),sK2) = iProver_top
    | v2_tex_2(sK0(sK2,sK1(sK2,X0,sK0(sK3,X0))),sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2705,c_2841])).

cnf(c_455,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | m1_subset_1(sK1(X2,X1,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_17])).

cnf(c_456,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v2_tex_2(X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK1(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unflattening,[status(thm)],[c_455])).

cnf(c_937,plain,
    ( v2_tex_2(X0,sK2)
    | ~ v2_tex_2(X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK1(sK3,X1,X2),k1_zfmisc_1(u1_struct_0(sK3)))
    | X0 != X1
    | sK0(sK2,X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_456,c_441])).

cnf(c_938,plain,
    ( v2_tex_2(X0,sK2)
    | ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK1(sK3,X0,sK0(sK2,X0)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unflattening,[status(thm)],[c_937])).

cnf(c_1491,plain,
    ( v2_tex_2(X0,sK2) = iProver_top
    | v2_tex_2(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK1(sK3,X0,sK0(sK2,X0)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_938])).

cnf(c_2194,plain,
    ( v2_tex_2(X0,sK2) = iProver_top
    | v2_tex_2(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK1(sK3,X0,sK0(sK2,X0)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2055,c_1491])).

cnf(c_2602,plain,
    ( m1_subset_1(sK1(sK3,X0,sK0(sK2,X0)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_tex_2(X0,sK3) != iProver_top
    | v2_tex_2(X0,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2194,c_2422])).

cnf(c_2603,plain,
    ( v2_tex_2(X0,sK2) = iProver_top
    | v2_tex_2(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK1(sK3,X0,sK0(sK2,X0)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(renaming,[status(thm)],[c_2602])).

cnf(c_3341,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK0(sK2,sK1(sK3,X0,sK0(sK2,X0))),sK1(sK3,sK0(sK2,sK1(sK3,X0,sK0(sK2,X0))),sK0(sK2,sK0(sK2,sK1(sK3,X0,sK0(sK2,X0)))))) = sK0(sK2,sK0(sK2,sK1(sK3,X0,sK0(sK2,X0))))
    | v2_tex_2(X0,sK2) = iProver_top
    | v2_tex_2(X0,sK3) != iProver_top
    | v2_tex_2(sK1(sK3,X0,sK0(sK2,X0)),sK2) = iProver_top
    | v2_tex_2(sK0(sK2,sK1(sK3,X0,sK0(sK2,X0))),sK2) = iProver_top
    | v2_tex_2(sK0(sK2,sK1(sK3,X0,sK0(sK2,X0))),sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2603,c_2841])).

cnf(c_3340,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK0(sK2,sK0(sK2,X0)),sK1(sK3,sK0(sK2,sK0(sK2,X0)),sK0(sK2,sK0(sK2,sK0(sK2,X0))))) = sK0(sK2,sK0(sK2,sK0(sK2,X0)))
    | v2_tex_2(X0,sK2) = iProver_top
    | v2_tex_2(sK0(sK2,X0),sK2) = iProver_top
    | v2_tex_2(sK0(sK2,sK0(sK2,X0)),sK2) = iProver_top
    | v2_tex_2(sK0(sK2,sK0(sK2,X0)),sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2422,c_2841])).

cnf(c_3339,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK0(sK2,sK0(sK3,X0)),sK1(sK3,sK0(sK2,sK0(sK3,X0)),sK0(sK2,sK0(sK2,sK0(sK3,X0))))) = sK0(sK2,sK0(sK2,sK0(sK3,X0)))
    | v2_tex_2(X0,sK3) = iProver_top
    | v2_tex_2(sK0(sK2,sK0(sK3,X0)),sK2) = iProver_top
    | v2_tex_2(sK0(sK2,sK0(sK3,X0)),sK3) != iProver_top
    | v2_tex_2(sK0(sK3,X0),sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1502,c_2841])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1504,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_560,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | k9_subset_1(u1_struct_0(X2),X1,sK1(X2,X1,X0)) = X0
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_18])).

cnf(c_561,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v2_tex_2(X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | k9_subset_1(u1_struct_0(sK2),X1,sK1(sK2,X1,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_560])).

cnf(c_805,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v2_tex_2(X1,sK3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | X1 != X0
    | k9_subset_1(u1_struct_0(sK2),X0,sK1(sK2,X0,X2)) = X2
    | sK0(sK3,X1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_561,c_419])).

cnf(c_806,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | k9_subset_1(u1_struct_0(sK2),X0,sK1(sK2,X0,sK0(sK3,X0))) = sK0(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_805])).

cnf(c_1496,plain,
    ( k9_subset_1(u1_struct_0(sK2),X0,sK1(sK2,X0,sK0(sK3,X0))) = sK0(sK3,X0)
    | v2_tex_2(X0,sK2) != iProver_top
    | v2_tex_2(X0,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_806])).

cnf(c_2901,plain,
    ( k9_subset_1(u1_struct_0(sK3),X0,sK1(sK2,X0,sK0(sK3,X0))) = sK0(sK3,X0)
    | v2_tex_2(X0,sK2) != iProver_top
    | v2_tex_2(X0,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1496,c_2055])).

cnf(c_2907,plain,
    ( k9_subset_1(u1_struct_0(sK3),X0,sK1(sK2,X0,sK0(sK3,X0))) = sK0(sK3,X0)
    | v2_tex_2(X0,sK2) != iProver_top
    | v2_tex_2(X0,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2901,c_1502])).

cnf(c_2911,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK5,sK1(sK2,sK5,sK0(sK3,sK5))) = sK0(sK3,sK5)
    | v2_tex_2(sK5,sK2) != iProver_top
    | v2_tex_2(sK5,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1504,c_2907])).

cnf(c_11,negated_conjecture,
    ( ~ v2_tex_2(sK5,sK3) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_24,plain,
    ( v2_tex_2(sK5,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_12,negated_conjecture,
    ( v2_tex_2(sK4,sK2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1505,plain,
    ( v2_tex_2(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_13,negated_conjecture,
    ( sK4 = sK5 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1511,plain,
    ( v2_tex_2(sK5,sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1505,c_13])).

cnf(c_3017,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK5,sK1(sK2,sK5,sK0(sK3,sK5))) = sK0(sK3,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2911,c_24,c_1511])).

cnf(c_2,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK0(X1,X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_354,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK0(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_17])).

cnf(c_355,plain,
    ( v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v3_pre_topc(X1,sK3)
    | k9_subset_1(u1_struct_0(sK3),X0,X1) != sK0(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_354])).

cnf(c_1501,plain,
    ( k9_subset_1(u1_struct_0(sK3),X0,X1) != sK0(sK3,X0)
    | v2_tex_2(X0,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_pre_topc(X1,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_355])).

cnf(c_3020,plain,
    ( v2_tex_2(sK5,sK3) = iProver_top
    | m1_subset_1(sK1(sK2,sK5,sK0(sK3,sK5)),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_pre_topc(sK1(sK2,sK5,sK0(sK3,sK5)),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3017,c_1501])).

cnf(c_22,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3032,plain,
    ( m1_subset_1(sK1(sK2,sK5,sK0(sK3,sK5)),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_pre_topc(sK1(sK2,sK5,sK0(sK3,sK5)),sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3020,c_22,c_24])).

cnf(c_3038,plain,
    ( v2_tex_2(sK5,sK2) != iProver_top
    | v2_tex_2(sK5,sK3) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_pre_topc(sK1(sK2,sK5,sK0(sK3,sK5)),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2705,c_3032])).

cnf(c_3327,plain,
    ( v3_pre_topc(sK1(sK2,sK5,sK0(sK3,sK5)),sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3038,c_22,c_24,c_1511])).

cnf(c_2840,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK0(sK3,X0),sK1(sK3,sK0(sK3,X0),sK0(sK2,sK0(sK3,X0)))) = sK0(sK2,sK0(sK3,X0))
    | v2_tex_2(X0,sK3) = iProver_top
    | v2_tex_2(sK0(sK3,X0),sK2) = iProver_top
    | v2_tex_2(sK0(sK3,X0),sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1502,c_2831])).

cnf(c_3094,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK0(sK3,sK5),sK1(sK3,sK0(sK3,sK5),sK0(sK2,sK0(sK3,sK5)))) = sK0(sK2,sK0(sK3,sK5))
    | v2_tex_2(sK0(sK3,sK5),sK2) = iProver_top
    | v2_tex_2(sK0(sK3,sK5),sK3) != iProver_top
    | v2_tex_2(sK5,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1504,c_2840])).

cnf(c_3173,plain,
    ( v2_tex_2(sK0(sK3,sK5),sK3) != iProver_top
    | v2_tex_2(sK0(sK3,sK5),sK2) = iProver_top
    | k9_subset_1(u1_struct_0(sK3),sK0(sK3,sK5),sK1(sK3,sK0(sK3,sK5),sK0(sK2,sK0(sK3,sK5)))) = sK0(sK2,sK0(sK3,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3094,c_24])).

cnf(c_3174,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK0(sK3,sK5),sK1(sK3,sK0(sK3,sK5),sK0(sK2,sK0(sK3,sK5)))) = sK0(sK2,sK0(sK3,sK5))
    | v2_tex_2(sK0(sK3,sK5),sK2) = iProver_top
    | v2_tex_2(sK0(sK3,sK5),sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_3173])).

cnf(c_3098,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK0(sK3,sK1(sK2,X0,sK0(sK3,X0))),sK1(sK3,sK0(sK3,sK1(sK2,X0,sK0(sK3,X0))),sK0(sK2,sK0(sK3,sK1(sK2,X0,sK0(sK3,X0)))))) = sK0(sK2,sK0(sK3,sK1(sK2,X0,sK0(sK3,X0))))
    | v2_tex_2(X0,sK2) != iProver_top
    | v2_tex_2(X0,sK3) = iProver_top
    | v2_tex_2(sK1(sK2,X0,sK0(sK3,X0)),sK3) = iProver_top
    | v2_tex_2(sK0(sK3,sK1(sK2,X0,sK0(sK3,X0))),sK2) = iProver_top
    | v2_tex_2(sK0(sK3,sK1(sK2,X0,sK0(sK3,X0))),sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2705,c_2840])).

cnf(c_3097,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK0(sK3,sK1(sK3,X0,sK0(sK2,X0))),sK1(sK3,sK0(sK3,sK1(sK3,X0,sK0(sK2,X0))),sK0(sK2,sK0(sK3,sK1(sK3,X0,sK0(sK2,X0)))))) = sK0(sK2,sK0(sK3,sK1(sK3,X0,sK0(sK2,X0))))
    | v2_tex_2(X0,sK2) = iProver_top
    | v2_tex_2(X0,sK3) != iProver_top
    | v2_tex_2(sK1(sK3,X0,sK0(sK2,X0)),sK3) = iProver_top
    | v2_tex_2(sK0(sK3,sK1(sK3,X0,sK0(sK2,X0))),sK2) = iProver_top
    | v2_tex_2(sK0(sK3,sK1(sK3,X0,sK0(sK2,X0))),sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2603,c_2840])).

cnf(c_3096,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK0(sK3,sK0(sK2,X0)),sK1(sK3,sK0(sK3,sK0(sK2,X0)),sK0(sK2,sK0(sK3,sK0(sK2,X0))))) = sK0(sK2,sK0(sK3,sK0(sK2,X0)))
    | v2_tex_2(X0,sK2) = iProver_top
    | v2_tex_2(sK0(sK2,X0),sK3) = iProver_top
    | v2_tex_2(sK0(sK3,sK0(sK2,X0)),sK2) = iProver_top
    | v2_tex_2(sK0(sK3,sK0(sK2,X0)),sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2422,c_2840])).

cnf(c_3095,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK0(sK3,sK0(sK3,X0)),sK1(sK3,sK0(sK3,sK0(sK3,X0)),sK0(sK2,sK0(sK3,sK0(sK3,X0))))) = sK0(sK2,sK0(sK3,sK0(sK3,X0)))
    | v2_tex_2(X0,sK3) = iProver_top
    | v2_tex_2(sK0(sK3,X0),sK3) = iProver_top
    | v2_tex_2(sK0(sK3,sK0(sK3,X0)),sK2) = iProver_top
    | v2_tex_2(sK0(sK3,sK0(sK3,X0)),sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1502,c_2840])).

cnf(c_2915,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK1(sK2,X0,sK0(sK3,X0)),sK1(sK2,sK1(sK2,X0,sK0(sK3,X0)),sK0(sK3,sK1(sK2,X0,sK0(sK3,X0))))) = sK0(sK3,sK1(sK2,X0,sK0(sK3,X0)))
    | v2_tex_2(X0,sK2) != iProver_top
    | v2_tex_2(X0,sK3) = iProver_top
    | v2_tex_2(sK1(sK2,X0,sK0(sK3,X0)),sK2) != iProver_top
    | v2_tex_2(sK1(sK2,X0,sK0(sK3,X0)),sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2705,c_2907])).

cnf(c_2914,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK1(sK3,X0,sK0(sK2,X0)),sK1(sK2,sK1(sK3,X0,sK0(sK2,X0)),sK0(sK3,sK1(sK3,X0,sK0(sK2,X0))))) = sK0(sK3,sK1(sK3,X0,sK0(sK2,X0)))
    | v2_tex_2(X0,sK2) = iProver_top
    | v2_tex_2(X0,sK3) != iProver_top
    | v2_tex_2(sK1(sK3,X0,sK0(sK2,X0)),sK2) != iProver_top
    | v2_tex_2(sK1(sK3,X0,sK0(sK2,X0)),sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2603,c_2907])).

cnf(c_2913,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK0(sK2,X0),sK1(sK2,sK0(sK2,X0),sK0(sK3,sK0(sK2,X0)))) = sK0(sK3,sK0(sK2,X0))
    | v2_tex_2(X0,sK2) = iProver_top
    | v2_tex_2(sK0(sK2,X0),sK2) != iProver_top
    | v2_tex_2(sK0(sK2,X0),sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2422,c_2907])).

cnf(c_2912,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK0(sK3,X0),sK1(sK2,sK0(sK3,X0),sK0(sK3,sK0(sK3,X0)))) = sK0(sK3,sK0(sK3,X0))
    | v2_tex_2(X0,sK3) = iProver_top
    | v2_tex_2(sK0(sK3,X0),sK2) != iProver_top
    | v2_tex_2(sK0(sK3,X0),sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1502,c_2907])).

cnf(c_2843,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK1(sK2,X0,sK0(sK3,X0)),sK1(sK3,sK1(sK2,X0,sK0(sK3,X0)),sK0(sK2,sK1(sK2,X0,sK0(sK3,X0))))) = sK0(sK2,sK1(sK2,X0,sK0(sK3,X0)))
    | v2_tex_2(X0,sK2) != iProver_top
    | v2_tex_2(X0,sK3) = iProver_top
    | v2_tex_2(sK1(sK2,X0,sK0(sK3,X0)),sK2) = iProver_top
    | v2_tex_2(sK1(sK2,X0,sK0(sK3,X0)),sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2705,c_2831])).

cnf(c_2842,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK1(sK3,X0,sK0(sK2,X0)),sK1(sK3,sK1(sK3,X0,sK0(sK2,X0)),sK0(sK2,sK1(sK3,X0,sK0(sK2,X0))))) = sK0(sK2,sK1(sK3,X0,sK0(sK2,X0)))
    | v2_tex_2(X0,sK2) = iProver_top
    | v2_tex_2(X0,sK3) != iProver_top
    | v2_tex_2(sK1(sK3,X0,sK0(sK2,X0)),sK2) = iProver_top
    | v2_tex_2(sK1(sK3,X0,sK0(sK2,X0)),sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2603,c_2831])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | v3_pre_topc(sK1(X2,X1,X0),X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_539,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | v3_pre_topc(sK1(X2,X1,X0),X2)
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_18])).

cnf(c_540,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v2_tex_2(X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | v3_pre_topc(sK1(sK2,X1,X0),sK2) ),
    inference(unflattening,[status(thm)],[c_539])).

cnf(c_829,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v2_tex_2(X1,sK3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | v3_pre_topc(sK1(sK2,X0,X2),sK2)
    | X1 != X0
    | sK0(sK3,X1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_540,c_419])).

cnf(c_830,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | v3_pre_topc(sK1(sK2,X0,sK0(sK3,X0)),sK2) ),
    inference(unflattening,[status(thm)],[c_829])).

cnf(c_1495,plain,
    ( v2_tex_2(X0,sK2) != iProver_top
    | v2_tex_2(X0,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v3_pre_topc(sK1(sK2,X0,sK0(sK3,X0)),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_830])).

cnf(c_2688,plain,
    ( v2_tex_2(X0,sK2) != iProver_top
    | v2_tex_2(X0,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_pre_topc(sK1(sK2,X0,sK0(sK3,X0)),sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1495,c_2055])).

cnf(c_2694,plain,
    ( v2_tex_2(X0,sK2) != iProver_top
    | v2_tex_2(X0,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_pre_topc(sK1(sK2,X0,sK0(sK3,X0)),sK2) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2688,c_1502])).

cnf(c_390,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK0(X1,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_18])).

cnf(c_391,plain,
    ( v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v3_pre_topc(X1,sK2)
    | k9_subset_1(u1_struct_0(sK2),X0,X1) != sK0(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_390])).

cnf(c_1499,plain,
    ( k9_subset_1(u1_struct_0(sK2),X0,X1) != sK0(sK2,X0)
    | v2_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v3_pre_topc(X1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_391])).

cnf(c_2542,plain,
    ( k9_subset_1(u1_struct_0(sK3),X0,X1) != sK0(sK2,X0)
    | v2_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_pre_topc(X1,sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1499,c_2055])).

cnf(c_476,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | v3_pre_topc(sK1(X2,X1,X0),X2)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_17])).

cnf(c_477,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v2_tex_2(X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | v3_pre_topc(sK1(sK3,X1,X0),sK3) ),
    inference(unflattening,[status(thm)],[c_476])).

cnf(c_913,plain,
    ( v2_tex_2(X0,sK2)
    | ~ v2_tex_2(X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | v3_pre_topc(sK1(sK3,X1,X2),sK3)
    | X0 != X1
    | sK0(sK2,X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_477,c_441])).

cnf(c_914,plain,
    ( v2_tex_2(X0,sK2)
    | ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | v3_pre_topc(sK1(sK3,X0,sK0(sK2,X0)),sK3) ),
    inference(unflattening,[status(thm)],[c_913])).

cnf(c_1492,plain,
    ( v2_tex_2(X0,sK2) = iProver_top
    | v2_tex_2(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_pre_topc(sK1(sK3,X0,sK0(sK2,X0)),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_914])).

cnf(c_2409,plain,
    ( v2_tex_2(X0,sK2) = iProver_top
    | v2_tex_2(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_pre_topc(sK1(sK3,X0,sK0(sK2,X0)),sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1492,c_2055])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X0
    | g1_pre_topc(X3,X2) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1508,plain,
    ( X0 = X1
    | g1_pre_topc(X2,X0) != g1_pre_topc(X3,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2027,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(sK2) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_1508])).

cnf(c_19,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_29,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_31,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_2028,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(sK2) = X1
    | m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_1508])).

cnf(c_2176,plain,
    ( u1_pre_topc(sK2) = X1
    | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2027,c_19,c_31,c_2028])).

cnf(c_2177,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(sK2) = X1 ),
    inference(renaming,[status(thm)],[c_2176])).

cnf(c_2182,plain,
    ( u1_pre_topc(sK3) = u1_pre_topc(sK2) ),
    inference(equality_resolution,[status(thm)],[c_2177])).

cnf(c_2184,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(sK3) = X1 ),
    inference(demodulation,[status(thm)],[c_2182,c_2177])).

cnf(c_2057,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(X0,X1)
    | u1_struct_0(sK3) = X0 ),
    inference(demodulation,[status(thm)],[c_2055,c_2050])).

cnf(c_411,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_17])).

cnf(c_412,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    inference(unflattening,[status(thm)],[c_411])).

cnf(c_1498,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_412])).

cnf(c_1506,plain,
    ( v2_tex_2(sK5,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).


%------------------------------------------------------------------------------
