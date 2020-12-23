%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:47 EST 2020

% Result     : CounterSatisfiable 2.49s
% Output     : Saturation 2.49s
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
fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

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
    inference(nnf_transformation,[],[f11])).

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

fof(f30,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f34,plain,(
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

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f32,plain,(
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

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( v2_tex_2(X1,X0)
      | k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f31,plain,(
    ! [X4,X0,X1] :
      ( v3_pre_topc(sK1(X0,X1,X4),X0)
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f9])).

cnf(c_159,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | m1_subset_1(sK1(X2,X1,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f30])).

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
    inference(resolution_lifted,[status(thm)],[c_10,c_18])).

cnf(c_519,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v2_tex_2(X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_518])).

cnf(c_6,plain,
    ( r1_tarski(sK0(X0,X1),X1)
    | v2_tex_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_17,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_411,plain,
    ( r1_tarski(sK0(X0,X1),X1)
    | v2_tex_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_17])).

cnf(c_412,plain,
    ( r1_tarski(sK0(sK3,X0),X0)
    | v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unflattening,[status(thm)],[c_411])).

cnf(c_853,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v2_tex_2(X1,sK3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK1(sK2,X0,X2),k1_zfmisc_1(u1_struct_0(sK2)))
    | X1 != X0
    | sK0(sK3,X1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_519,c_412])).

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

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_1507,plain,
    ( X0 = X1
    | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1973,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(X0,X1)
    | u1_struct_0(sK2) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_1507])).

cnf(c_2,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_48,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

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
    inference(global_propositional_subsumption,[status(thm)],[c_1973,c_18,c_48,c_1991])).

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

cnf(c_7,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_339,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_17])).

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
    inference(resolution_lifted,[status(thm)],[c_7,c_18])).

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

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | k9_subset_1(u1_struct_0(X2),X1,sK1(X2,X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_497,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | k9_subset_1(u1_struct_0(X2),X1,sK1(X2,X1,X0)) = X0
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_17])).

cnf(c_498,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v2_tex_2(X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | k9_subset_1(u1_struct_0(sK3),X1,sK1(sK3,X1,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_497])).

cnf(c_433,plain,
    ( r1_tarski(sK0(X0,X1),X1)
    | v2_tex_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_18])).

cnf(c_434,plain,
    ( r1_tarski(sK0(sK2,X0),X0)
    | v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_433])).

cnf(c_889,plain,
    ( v2_tex_2(X0,sK2)
    | ~ v2_tex_2(X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | X0 != X1
    | k9_subset_1(u1_struct_0(sK3),X1,sK1(sK3,X1,X2)) = X2
    | sK0(sK2,X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_498,c_434])).

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
    inference(resolution_lifted,[status(thm)],[c_10,c_17])).

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
    inference(resolution_lifted,[status(thm)],[c_456,c_434])).

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
    inference(resolution_lifted,[status(thm)],[c_8,c_18])).

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
    inference(resolution_lifted,[status(thm)],[c_561,c_412])).

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

cnf(c_5,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK0(X1,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_354,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK0(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_17])).

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

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | v3_pre_topc(sK1(X2,X1,X0),X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_539,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | v3_pre_topc(sK1(X2,X1,X0),X2)
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_18])).

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
    inference(resolution_lifted,[status(thm)],[c_540,c_412])).

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
    inference(resolution_lifted,[status(thm)],[c_5,c_18])).

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
    inference(resolution_lifted,[status(thm)],[c_9,c_17])).

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
    inference(resolution_lifted,[status(thm)],[c_477,c_434])).

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

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X0
    | g1_pre_topc(X3,X2) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_1508,plain,
    ( X0 = X1
    | g1_pre_topc(X2,X0) != g1_pre_topc(X3,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2027,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(sK2) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_1508])).

cnf(c_19,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_47,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_49,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_47])).

cnf(c_2028,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(sK2) = X1
    | m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_1508])).

cnf(c_2176,plain,
    ( u1_pre_topc(sK2) = X1
    | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2027,c_19,c_49,c_2028])).

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

cnf(c_426,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_17])).

cnf(c_427,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    inference(unflattening,[status(thm)],[c_426])).

cnf(c_1498,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_427])).

cnf(c_1506,plain,
    ( v2_tex_2(sK5,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:02:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.49/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.00  
% 2.49/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.49/1.00  
% 2.49/1.00  ------  iProver source info
% 2.49/1.00  
% 2.49/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.49/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.49/1.00  git: non_committed_changes: false
% 2.49/1.00  git: last_make_outside_of_git: false
% 2.49/1.00  
% 2.49/1.00  ------ 
% 2.49/1.00  
% 2.49/1.00  ------ Input Options
% 2.49/1.00  
% 2.49/1.00  --out_options                           all
% 2.49/1.00  --tptp_safe_out                         true
% 2.49/1.00  --problem_path                          ""
% 2.49/1.00  --include_path                          ""
% 2.49/1.00  --clausifier                            res/vclausify_rel
% 2.49/1.00  --clausifier_options                    --mode clausify
% 2.49/1.00  --stdin                                 false
% 2.49/1.00  --stats_out                             all
% 2.49/1.00  
% 2.49/1.00  ------ General Options
% 2.49/1.00  
% 2.49/1.00  --fof                                   false
% 2.49/1.00  --time_out_real                         305.
% 2.49/1.00  --time_out_virtual                      -1.
% 2.49/1.00  --symbol_type_check                     false
% 2.49/1.00  --clausify_out                          false
% 2.49/1.00  --sig_cnt_out                           false
% 2.49/1.00  --trig_cnt_out                          false
% 2.49/1.00  --trig_cnt_out_tolerance                1.
% 2.49/1.00  --trig_cnt_out_sk_spl                   false
% 2.49/1.00  --abstr_cl_out                          false
% 2.49/1.00  
% 2.49/1.00  ------ Global Options
% 2.49/1.00  
% 2.49/1.00  --schedule                              default
% 2.49/1.00  --add_important_lit                     false
% 2.49/1.00  --prop_solver_per_cl                    1000
% 2.49/1.00  --min_unsat_core                        false
% 2.49/1.00  --soft_assumptions                      false
% 2.49/1.00  --soft_lemma_size                       3
% 2.49/1.00  --prop_impl_unit_size                   0
% 2.49/1.00  --prop_impl_unit                        []
% 2.49/1.00  --share_sel_clauses                     true
% 2.49/1.00  --reset_solvers                         false
% 2.49/1.00  --bc_imp_inh                            [conj_cone]
% 2.49/1.00  --conj_cone_tolerance                   3.
% 2.49/1.00  --extra_neg_conj                        none
% 2.49/1.00  --large_theory_mode                     true
% 2.49/1.00  --prolific_symb_bound                   200
% 2.49/1.00  --lt_threshold                          2000
% 2.49/1.00  --clause_weak_htbl                      true
% 2.49/1.00  --gc_record_bc_elim                     false
% 2.49/1.00  
% 2.49/1.00  ------ Preprocessing Options
% 2.49/1.00  
% 2.49/1.00  --preprocessing_flag                    true
% 2.49/1.00  --time_out_prep_mult                    0.1
% 2.49/1.00  --splitting_mode                        input
% 2.49/1.00  --splitting_grd                         true
% 2.49/1.00  --splitting_cvd                         false
% 2.49/1.00  --splitting_cvd_svl                     false
% 2.49/1.00  --splitting_nvd                         32
% 2.49/1.00  --sub_typing                            true
% 2.49/1.00  --prep_gs_sim                           true
% 2.49/1.00  --prep_unflatten                        true
% 2.49/1.00  --prep_res_sim                          true
% 2.49/1.00  --prep_upred                            true
% 2.49/1.00  --prep_sem_filter                       exhaustive
% 2.49/1.00  --prep_sem_filter_out                   false
% 2.49/1.00  --pred_elim                             true
% 2.49/1.00  --res_sim_input                         true
% 2.49/1.00  --eq_ax_congr_red                       true
% 2.49/1.00  --pure_diseq_elim                       true
% 2.49/1.00  --brand_transform                       false
% 2.49/1.00  --non_eq_to_eq                          false
% 2.49/1.00  --prep_def_merge                        true
% 2.49/1.00  --prep_def_merge_prop_impl              false
% 2.49/1.00  --prep_def_merge_mbd                    true
% 2.49/1.00  --prep_def_merge_tr_red                 false
% 2.49/1.00  --prep_def_merge_tr_cl                  false
% 2.49/1.00  --smt_preprocessing                     true
% 2.49/1.00  --smt_ac_axioms                         fast
% 2.49/1.00  --preprocessed_out                      false
% 2.49/1.00  --preprocessed_stats                    false
% 2.49/1.00  
% 2.49/1.00  ------ Abstraction refinement Options
% 2.49/1.00  
% 2.49/1.00  --abstr_ref                             []
% 2.49/1.00  --abstr_ref_prep                        false
% 2.49/1.00  --abstr_ref_until_sat                   false
% 2.49/1.00  --abstr_ref_sig_restrict                funpre
% 2.49/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.49/1.00  --abstr_ref_under                       []
% 2.49/1.00  
% 2.49/1.00  ------ SAT Options
% 2.49/1.00  
% 2.49/1.00  --sat_mode                              false
% 2.49/1.00  --sat_fm_restart_options                ""
% 2.49/1.00  --sat_gr_def                            false
% 2.49/1.00  --sat_epr_types                         true
% 2.49/1.00  --sat_non_cyclic_types                  false
% 2.49/1.00  --sat_finite_models                     false
% 2.49/1.00  --sat_fm_lemmas                         false
% 2.49/1.00  --sat_fm_prep                           false
% 2.49/1.00  --sat_fm_uc_incr                        true
% 2.49/1.00  --sat_out_model                         small
% 2.49/1.00  --sat_out_clauses                       false
% 2.49/1.00  
% 2.49/1.00  ------ QBF Options
% 2.49/1.00  
% 2.49/1.00  --qbf_mode                              false
% 2.49/1.00  --qbf_elim_univ                         false
% 2.49/1.00  --qbf_dom_inst                          none
% 2.49/1.00  --qbf_dom_pre_inst                      false
% 2.49/1.00  --qbf_sk_in                             false
% 2.49/1.00  --qbf_pred_elim                         true
% 2.49/1.00  --qbf_split                             512
% 2.49/1.00  
% 2.49/1.00  ------ BMC1 Options
% 2.49/1.00  
% 2.49/1.00  --bmc1_incremental                      false
% 2.49/1.00  --bmc1_axioms                           reachable_all
% 2.49/1.00  --bmc1_min_bound                        0
% 2.49/1.00  --bmc1_max_bound                        -1
% 2.49/1.00  --bmc1_max_bound_default                -1
% 2.49/1.00  --bmc1_symbol_reachability              true
% 2.49/1.00  --bmc1_property_lemmas                  false
% 2.49/1.00  --bmc1_k_induction                      false
% 2.49/1.00  --bmc1_non_equiv_states                 false
% 2.49/1.00  --bmc1_deadlock                         false
% 2.49/1.00  --bmc1_ucm                              false
% 2.49/1.00  --bmc1_add_unsat_core                   none
% 2.49/1.00  --bmc1_unsat_core_children              false
% 2.49/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.49/1.00  --bmc1_out_stat                         full
% 2.49/1.00  --bmc1_ground_init                      false
% 2.49/1.00  --bmc1_pre_inst_next_state              false
% 2.49/1.00  --bmc1_pre_inst_state                   false
% 2.49/1.00  --bmc1_pre_inst_reach_state             false
% 2.49/1.00  --bmc1_out_unsat_core                   false
% 2.49/1.00  --bmc1_aig_witness_out                  false
% 2.49/1.00  --bmc1_verbose                          false
% 2.49/1.00  --bmc1_dump_clauses_tptp                false
% 2.49/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.49/1.00  --bmc1_dump_file                        -
% 2.49/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.49/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.49/1.00  --bmc1_ucm_extend_mode                  1
% 2.49/1.00  --bmc1_ucm_init_mode                    2
% 2.49/1.00  --bmc1_ucm_cone_mode                    none
% 2.49/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.49/1.00  --bmc1_ucm_relax_model                  4
% 2.49/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.49/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.49/1.00  --bmc1_ucm_layered_model                none
% 2.49/1.00  --bmc1_ucm_max_lemma_size               10
% 2.49/1.00  
% 2.49/1.00  ------ AIG Options
% 2.49/1.00  
% 2.49/1.00  --aig_mode                              false
% 2.49/1.00  
% 2.49/1.00  ------ Instantiation Options
% 2.49/1.00  
% 2.49/1.00  --instantiation_flag                    true
% 2.49/1.00  --inst_sos_flag                         false
% 2.49/1.00  --inst_sos_phase                        true
% 2.49/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.49/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.49/1.00  --inst_lit_sel_side                     num_symb
% 2.49/1.00  --inst_solver_per_active                1400
% 2.49/1.00  --inst_solver_calls_frac                1.
% 2.49/1.00  --inst_passive_queue_type               priority_queues
% 2.49/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.49/1.00  --inst_passive_queues_freq              [25;2]
% 2.49/1.00  --inst_dismatching                      true
% 2.49/1.00  --inst_eager_unprocessed_to_passive     true
% 2.49/1.00  --inst_prop_sim_given                   true
% 2.49/1.00  --inst_prop_sim_new                     false
% 2.49/1.00  --inst_subs_new                         false
% 2.49/1.00  --inst_eq_res_simp                      false
% 2.49/1.00  --inst_subs_given                       false
% 2.49/1.00  --inst_orphan_elimination               true
% 2.49/1.00  --inst_learning_loop_flag               true
% 2.49/1.00  --inst_learning_start                   3000
% 2.49/1.00  --inst_learning_factor                  2
% 2.49/1.00  --inst_start_prop_sim_after_learn       3
% 2.49/1.00  --inst_sel_renew                        solver
% 2.49/1.00  --inst_lit_activity_flag                true
% 2.49/1.00  --inst_restr_to_given                   false
% 2.49/1.00  --inst_activity_threshold               500
% 2.49/1.00  --inst_out_proof                        true
% 2.49/1.00  
% 2.49/1.00  ------ Resolution Options
% 2.49/1.00  
% 2.49/1.00  --resolution_flag                       true
% 2.49/1.00  --res_lit_sel                           adaptive
% 2.49/1.00  --res_lit_sel_side                      none
% 2.49/1.00  --res_ordering                          kbo
% 2.49/1.00  --res_to_prop_solver                    active
% 2.49/1.00  --res_prop_simpl_new                    false
% 2.49/1.00  --res_prop_simpl_given                  true
% 2.49/1.00  --res_passive_queue_type                priority_queues
% 2.49/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.49/1.00  --res_passive_queues_freq               [15;5]
% 2.49/1.00  --res_forward_subs                      full
% 2.49/1.00  --res_backward_subs                     full
% 2.49/1.00  --res_forward_subs_resolution           true
% 2.49/1.00  --res_backward_subs_resolution          true
% 2.49/1.00  --res_orphan_elimination                true
% 2.49/1.00  --res_time_limit                        2.
% 2.49/1.00  --res_out_proof                         true
% 2.49/1.00  
% 2.49/1.00  ------ Superposition Options
% 2.49/1.00  
% 2.49/1.00  --superposition_flag                    true
% 2.49/1.00  --sup_passive_queue_type                priority_queues
% 2.49/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.49/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.49/1.00  --demod_completeness_check              fast
% 2.49/1.00  --demod_use_ground                      true
% 2.49/1.00  --sup_to_prop_solver                    passive
% 2.49/1.00  --sup_prop_simpl_new                    true
% 2.49/1.00  --sup_prop_simpl_given                  true
% 2.49/1.00  --sup_fun_splitting                     false
% 2.49/1.00  --sup_smt_interval                      50000
% 2.49/1.00  
% 2.49/1.00  ------ Superposition Simplification Setup
% 2.49/1.00  
% 2.49/1.00  --sup_indices_passive                   []
% 2.49/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.49/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/1.00  --sup_full_bw                           [BwDemod]
% 2.49/1.00  --sup_immed_triv                        [TrivRules]
% 2.49/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.49/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/1.00  --sup_immed_bw_main                     []
% 2.49/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.49/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.49/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.49/1.00  
% 2.49/1.00  ------ Combination Options
% 2.49/1.00  
% 2.49/1.00  --comb_res_mult                         3
% 2.49/1.00  --comb_sup_mult                         2
% 2.49/1.00  --comb_inst_mult                        10
% 2.49/1.00  
% 2.49/1.00  ------ Debug Options
% 2.49/1.00  
% 2.49/1.00  --dbg_backtrace                         false
% 2.49/1.00  --dbg_dump_prop_clauses                 false
% 2.49/1.00  --dbg_dump_prop_clauses_file            -
% 2.49/1.00  --dbg_out_stat                          false
% 2.49/1.00  ------ Parsing...
% 2.49/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.49/1.00  
% 2.49/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 2.49/1.00  
% 2.49/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.49/1.00  
% 2.49/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.49/1.00  ------ Proving...
% 2.49/1.00  ------ Problem Properties 
% 2.49/1.00  
% 2.49/1.00  
% 2.49/1.00  clauses                                 20
% 2.49/1.00  conjectures                             6
% 2.49/1.00  EPR                                     3
% 2.49/1.01  Horn                                    12
% 2.49/1.01  unary                                   8
% 2.49/1.01  binary                                  0
% 2.49/1.01  lits                                    66
% 2.49/1.01  lits eq                                 10
% 2.49/1.01  fd_pure                                 0
% 2.49/1.01  fd_pseudo                               0
% 2.49/1.01  fd_cond                                 0
% 2.49/1.01  fd_pseudo_cond                          2
% 2.49/1.01  AC symbols                              0
% 2.49/1.01  
% 2.49/1.01  ------ Schedule dynamic 5 is on 
% 2.49/1.01  
% 2.49/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.49/1.01  
% 2.49/1.01  
% 2.49/1.01  ------ 
% 2.49/1.01  Current options:
% 2.49/1.01  ------ 
% 2.49/1.01  
% 2.49/1.01  ------ Input Options
% 2.49/1.01  
% 2.49/1.01  --out_options                           all
% 2.49/1.01  --tptp_safe_out                         true
% 2.49/1.01  --problem_path                          ""
% 2.49/1.01  --include_path                          ""
% 2.49/1.01  --clausifier                            res/vclausify_rel
% 2.49/1.01  --clausifier_options                    --mode clausify
% 2.49/1.01  --stdin                                 false
% 2.49/1.01  --stats_out                             all
% 2.49/1.01  
% 2.49/1.01  ------ General Options
% 2.49/1.01  
% 2.49/1.01  --fof                                   false
% 2.49/1.01  --time_out_real                         305.
% 2.49/1.01  --time_out_virtual                      -1.
% 2.49/1.01  --symbol_type_check                     false
% 2.49/1.01  --clausify_out                          false
% 2.49/1.01  --sig_cnt_out                           false
% 2.49/1.01  --trig_cnt_out                          false
% 2.49/1.01  --trig_cnt_out_tolerance                1.
% 2.49/1.01  --trig_cnt_out_sk_spl                   false
% 2.49/1.01  --abstr_cl_out                          false
% 2.49/1.01  
% 2.49/1.01  ------ Global Options
% 2.49/1.01  
% 2.49/1.01  --schedule                              default
% 2.49/1.01  --add_important_lit                     false
% 2.49/1.01  --prop_solver_per_cl                    1000
% 2.49/1.01  --min_unsat_core                        false
% 2.49/1.01  --soft_assumptions                      false
% 2.49/1.01  --soft_lemma_size                       3
% 2.49/1.01  --prop_impl_unit_size                   0
% 2.49/1.01  --prop_impl_unit                        []
% 2.49/1.01  --share_sel_clauses                     true
% 2.49/1.01  --reset_solvers                         false
% 2.49/1.01  --bc_imp_inh                            [conj_cone]
% 2.49/1.01  --conj_cone_tolerance                   3.
% 2.49/1.01  --extra_neg_conj                        none
% 2.49/1.01  --large_theory_mode                     true
% 2.49/1.01  --prolific_symb_bound                   200
% 2.49/1.01  --lt_threshold                          2000
% 2.49/1.01  --clause_weak_htbl                      true
% 2.49/1.01  --gc_record_bc_elim                     false
% 2.49/1.01  
% 2.49/1.01  ------ Preprocessing Options
% 2.49/1.01  
% 2.49/1.01  --preprocessing_flag                    true
% 2.49/1.01  --time_out_prep_mult                    0.1
% 2.49/1.01  --splitting_mode                        input
% 2.49/1.01  --splitting_grd                         true
% 2.49/1.01  --splitting_cvd                         false
% 2.49/1.01  --splitting_cvd_svl                     false
% 2.49/1.01  --splitting_nvd                         32
% 2.49/1.01  --sub_typing                            true
% 2.49/1.01  --prep_gs_sim                           true
% 2.49/1.01  --prep_unflatten                        true
% 2.49/1.01  --prep_res_sim                          true
% 2.49/1.01  --prep_upred                            true
% 2.49/1.01  --prep_sem_filter                       exhaustive
% 2.49/1.01  --prep_sem_filter_out                   false
% 2.49/1.01  --pred_elim                             true
% 2.49/1.01  --res_sim_input                         true
% 2.49/1.01  --eq_ax_congr_red                       true
% 2.49/1.01  --pure_diseq_elim                       true
% 2.49/1.01  --brand_transform                       false
% 2.49/1.01  --non_eq_to_eq                          false
% 2.49/1.01  --prep_def_merge                        true
% 2.49/1.01  --prep_def_merge_prop_impl              false
% 2.49/1.01  --prep_def_merge_mbd                    true
% 2.49/1.01  --prep_def_merge_tr_red                 false
% 2.49/1.01  --prep_def_merge_tr_cl                  false
% 2.49/1.01  --smt_preprocessing                     true
% 2.49/1.01  --smt_ac_axioms                         fast
% 2.49/1.01  --preprocessed_out                      false
% 2.49/1.01  --preprocessed_stats                    false
% 2.49/1.01  
% 2.49/1.01  ------ Abstraction refinement Options
% 2.49/1.01  
% 2.49/1.01  --abstr_ref                             []
% 2.49/1.01  --abstr_ref_prep                        false
% 2.49/1.01  --abstr_ref_until_sat                   false
% 2.49/1.01  --abstr_ref_sig_restrict                funpre
% 2.49/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.49/1.01  --abstr_ref_under                       []
% 2.49/1.01  
% 2.49/1.01  ------ SAT Options
% 2.49/1.01  
% 2.49/1.01  --sat_mode                              false
% 2.49/1.01  --sat_fm_restart_options                ""
% 2.49/1.01  --sat_gr_def                            false
% 2.49/1.01  --sat_epr_types                         true
% 2.49/1.01  --sat_non_cyclic_types                  false
% 2.49/1.01  --sat_finite_models                     false
% 2.49/1.01  --sat_fm_lemmas                         false
% 2.49/1.01  --sat_fm_prep                           false
% 2.49/1.01  --sat_fm_uc_incr                        true
% 2.49/1.01  --sat_out_model                         small
% 2.49/1.01  --sat_out_clauses                       false
% 2.49/1.01  
% 2.49/1.01  ------ QBF Options
% 2.49/1.01  
% 2.49/1.01  --qbf_mode                              false
% 2.49/1.01  --qbf_elim_univ                         false
% 2.49/1.01  --qbf_dom_inst                          none
% 2.49/1.01  --qbf_dom_pre_inst                      false
% 2.49/1.01  --qbf_sk_in                             false
% 2.49/1.01  --qbf_pred_elim                         true
% 2.49/1.01  --qbf_split                             512
% 2.49/1.01  
% 2.49/1.01  ------ BMC1 Options
% 2.49/1.01  
% 2.49/1.01  --bmc1_incremental                      false
% 2.49/1.01  --bmc1_axioms                           reachable_all
% 2.49/1.01  --bmc1_min_bound                        0
% 2.49/1.01  --bmc1_max_bound                        -1
% 2.49/1.01  --bmc1_max_bound_default                -1
% 2.49/1.01  --bmc1_symbol_reachability              true
% 2.49/1.01  --bmc1_property_lemmas                  false
% 2.49/1.01  --bmc1_k_induction                      false
% 2.49/1.01  --bmc1_non_equiv_states                 false
% 2.49/1.01  --bmc1_deadlock                         false
% 2.49/1.01  --bmc1_ucm                              false
% 2.49/1.01  --bmc1_add_unsat_core                   none
% 2.49/1.01  --bmc1_unsat_core_children              false
% 2.49/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.49/1.01  --bmc1_out_stat                         full
% 2.49/1.01  --bmc1_ground_init                      false
% 2.49/1.01  --bmc1_pre_inst_next_state              false
% 2.49/1.01  --bmc1_pre_inst_state                   false
% 2.49/1.01  --bmc1_pre_inst_reach_state             false
% 2.49/1.01  --bmc1_out_unsat_core                   false
% 2.49/1.01  --bmc1_aig_witness_out                  false
% 2.49/1.01  --bmc1_verbose                          false
% 2.49/1.01  --bmc1_dump_clauses_tptp                false
% 2.49/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.49/1.01  --bmc1_dump_file                        -
% 2.49/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.49/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.49/1.01  --bmc1_ucm_extend_mode                  1
% 2.49/1.01  --bmc1_ucm_init_mode                    2
% 2.49/1.01  --bmc1_ucm_cone_mode                    none
% 2.49/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.49/1.01  --bmc1_ucm_relax_model                  4
% 2.49/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.49/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.49/1.01  --bmc1_ucm_layered_model                none
% 2.49/1.01  --bmc1_ucm_max_lemma_size               10
% 2.49/1.01  
% 2.49/1.01  ------ AIG Options
% 2.49/1.01  
% 2.49/1.01  --aig_mode                              false
% 2.49/1.01  
% 2.49/1.01  ------ Instantiation Options
% 2.49/1.01  
% 2.49/1.01  --instantiation_flag                    true
% 2.49/1.01  --inst_sos_flag                         false
% 2.49/1.01  --inst_sos_phase                        true
% 2.49/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.49/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.49/1.01  --inst_lit_sel_side                     none
% 2.49/1.01  --inst_solver_per_active                1400
% 2.49/1.01  --inst_solver_calls_frac                1.
% 2.49/1.01  --inst_passive_queue_type               priority_queues
% 2.49/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.49/1.01  --inst_passive_queues_freq              [25;2]
% 2.49/1.01  --inst_dismatching                      true
% 2.49/1.01  --inst_eager_unprocessed_to_passive     true
% 2.49/1.01  --inst_prop_sim_given                   true
% 2.49/1.01  --inst_prop_sim_new                     false
% 2.49/1.01  --inst_subs_new                         false
% 2.49/1.01  --inst_eq_res_simp                      false
% 2.49/1.01  --inst_subs_given                       false
% 2.49/1.01  --inst_orphan_elimination               true
% 2.49/1.01  --inst_learning_loop_flag               true
% 2.49/1.01  --inst_learning_start                   3000
% 2.49/1.01  --inst_learning_factor                  2
% 2.49/1.01  --inst_start_prop_sim_after_learn       3
% 2.49/1.01  --inst_sel_renew                        solver
% 2.49/1.01  --inst_lit_activity_flag                true
% 2.49/1.01  --inst_restr_to_given                   false
% 2.49/1.01  --inst_activity_threshold               500
% 2.49/1.01  --inst_out_proof                        true
% 2.49/1.01  
% 2.49/1.01  ------ Resolution Options
% 2.49/1.01  
% 2.49/1.01  --resolution_flag                       false
% 2.49/1.01  --res_lit_sel                           adaptive
% 2.49/1.01  --res_lit_sel_side                      none
% 2.49/1.01  --res_ordering                          kbo
% 2.49/1.01  --res_to_prop_solver                    active
% 2.49/1.01  --res_prop_simpl_new                    false
% 2.49/1.01  --res_prop_simpl_given                  true
% 2.49/1.01  --res_passive_queue_type                priority_queues
% 2.49/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.49/1.01  --res_passive_queues_freq               [15;5]
% 2.49/1.01  --res_forward_subs                      full
% 2.49/1.01  --res_backward_subs                     full
% 2.49/1.01  --res_forward_subs_resolution           true
% 2.49/1.01  --res_backward_subs_resolution          true
% 2.49/1.01  --res_orphan_elimination                true
% 2.49/1.01  --res_time_limit                        2.
% 2.49/1.01  --res_out_proof                         true
% 2.49/1.01  
% 2.49/1.01  ------ Superposition Options
% 2.49/1.01  
% 2.49/1.01  --superposition_flag                    true
% 2.49/1.01  --sup_passive_queue_type                priority_queues
% 2.49/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.49/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.49/1.01  --demod_completeness_check              fast
% 2.49/1.01  --demod_use_ground                      true
% 2.49/1.01  --sup_to_prop_solver                    passive
% 2.49/1.01  --sup_prop_simpl_new                    true
% 2.49/1.01  --sup_prop_simpl_given                  true
% 2.49/1.01  --sup_fun_splitting                     false
% 2.49/1.01  --sup_smt_interval                      50000
% 2.49/1.01  
% 2.49/1.01  ------ Superposition Simplification Setup
% 2.49/1.01  
% 2.49/1.01  --sup_indices_passive                   []
% 2.49/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.49/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/1.01  --sup_full_bw                           [BwDemod]
% 2.49/1.01  --sup_immed_triv                        [TrivRules]
% 2.49/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.49/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/1.01  --sup_immed_bw_main                     []
% 2.49/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.49/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.49/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.49/1.01  
% 2.49/1.01  ------ Combination Options
% 2.49/1.01  
% 2.49/1.01  --comb_res_mult                         3
% 2.49/1.01  --comb_sup_mult                         2
% 2.49/1.01  --comb_inst_mult                        10
% 2.49/1.01  
% 2.49/1.01  ------ Debug Options
% 2.49/1.01  
% 2.49/1.01  --dbg_backtrace                         false
% 2.49/1.01  --dbg_dump_prop_clauses                 false
% 2.49/1.01  --dbg_dump_prop_clauses_file            -
% 2.49/1.01  --dbg_out_stat                          false
% 2.49/1.01  
% 2.49/1.01  
% 2.49/1.01  
% 2.49/1.01  
% 2.49/1.01  ------ Proving...
% 2.49/1.01  
% 2.49/1.01  
% 2.49/1.01  % SZS status CounterSatisfiable for theBenchmark.p
% 2.49/1.01  
% 2.49/1.01  % SZS output start Saturation for theBenchmark.p
% 2.49/1.01  
% 2.49/1.01  fof(f4,axiom,(
% 2.49/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 2.49/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/1.01  
% 2.49/1.01  fof(f10,plain,(
% 2.49/1.01    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.49/1.01    inference(ennf_transformation,[],[f4])).
% 2.49/1.01  
% 2.49/1.01  fof(f11,plain,(
% 2.49/1.01    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.49/1.01    inference(flattening,[],[f10])).
% 2.49/1.01  
% 2.49/1.01  fof(f15,plain,(
% 2.49/1.01    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.49/1.01    inference(nnf_transformation,[],[f11])).
% 2.49/1.01  
% 2.49/1.01  fof(f16,plain,(
% 2.49/1.01    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v3_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.49/1.01    inference(rectify,[],[f15])).
% 2.49/1.01  
% 2.49/1.01  fof(f18,plain,(
% 2.49/1.01    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v3_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4 & v3_pre_topc(sK1(X0,X1,X4),X0) & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.49/1.01    introduced(choice_axiom,[])).
% 2.49/1.01  
% 2.49/1.01  fof(f17,plain,(
% 2.49/1.01    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.49/1.01    introduced(choice_axiom,[])).
% 2.49/1.01  
% 2.49/1.01  fof(f19,plain,(
% 2.49/1.01    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4 & v3_pre_topc(sK1(X0,X1,X4),X0) & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.49/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f18,f17])).
% 2.49/1.01  
% 2.49/1.01  fof(f30,plain,(
% 2.49/1.01    ( ! [X4,X0,X1] : (m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.49/1.01    inference(cnf_transformation,[],[f19])).
% 2.49/1.01  
% 2.49/1.01  fof(f5,conjecture,(
% 2.49/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v2_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v2_tex_2(X3,X1))))))),
% 2.49/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/1.01  
% 2.49/1.01  fof(f6,negated_conjecture,(
% 2.49/1.01    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v2_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v2_tex_2(X3,X1))))))),
% 2.49/1.01    inference(negated_conjecture,[],[f5])).
% 2.49/1.01  
% 2.49/1.01  fof(f12,plain,(
% 2.49/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v2_tex_2(X3,X1) & (v2_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 2.49/1.01    inference(ennf_transformation,[],[f6])).
% 2.49/1.01  
% 2.49/1.01  fof(f13,plain,(
% 2.49/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v2_tex_2(X3,X1) & v2_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 2.49/1.01    inference(flattening,[],[f12])).
% 2.49/1.01  
% 2.49/1.01  fof(f23,plain,(
% 2.49/1.01    ( ! [X2,X0,X1] : (? [X3] : (~v2_tex_2(X3,X1) & v2_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v2_tex_2(sK5,X1) & v2_tex_2(X2,X0) & sK5 = X2 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 2.49/1.01    introduced(choice_axiom,[])).
% 2.49/1.01  
% 2.49/1.01  fof(f22,plain,(
% 2.49/1.01    ( ! [X0,X1] : (? [X2] : (? [X3] : (~v2_tex_2(X3,X1) & v2_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X3] : (~v2_tex_2(X3,X1) & v2_tex_2(sK4,X0) & sK4 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.49/1.01    introduced(choice_axiom,[])).
% 2.49/1.01  
% 2.49/1.01  fof(f21,plain,(
% 2.49/1.01    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~v2_tex_2(X3,X1) & v2_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) => (? [X2] : (? [X3] : (~v2_tex_2(X3,sK3) & v2_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(sK3))) )),
% 2.49/1.01    introduced(choice_axiom,[])).
% 2.49/1.01  
% 2.49/1.01  fof(f20,plain,(
% 2.49/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v2_tex_2(X3,X1) & v2_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (~v2_tex_2(X3,X1) & v2_tex_2(X2,sK2) & X2 = X3 & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(X1)) & l1_pre_topc(sK2))),
% 2.49/1.01    introduced(choice_axiom,[])).
% 2.49/1.01  
% 2.49/1.01  fof(f24,plain,(
% 2.49/1.01    (((~v2_tex_2(sK5,sK3) & v2_tex_2(sK4,sK2) & sK4 = sK5 & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK3)) & l1_pre_topc(sK2)),
% 2.49/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f13,f23,f22,f21,f20])).
% 2.49/1.01  
% 2.49/1.01  fof(f36,plain,(
% 2.49/1.01    l1_pre_topc(sK2)),
% 2.49/1.01    inference(cnf_transformation,[],[f24])).
% 2.49/1.01  
% 2.49/1.01  fof(f34,plain,(
% 2.49/1.01    ( ! [X0,X1] : (v2_tex_2(X1,X0) | r1_tarski(sK0(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.49/1.01    inference(cnf_transformation,[],[f19])).
% 2.49/1.01  
% 2.49/1.01  fof(f37,plain,(
% 2.49/1.01    l1_pre_topc(sK3)),
% 2.49/1.01    inference(cnf_transformation,[],[f24])).
% 2.49/1.01  
% 2.49/1.01  fof(f40,plain,(
% 2.49/1.01    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),
% 2.49/1.01    inference(cnf_transformation,[],[f24])).
% 2.49/1.01  
% 2.49/1.01  fof(f3,axiom,(
% 2.49/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 2.49/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/1.01  
% 2.49/1.01  fof(f9,plain,(
% 2.49/1.01    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.49/1.01    inference(ennf_transformation,[],[f3])).
% 2.49/1.01  
% 2.49/1.01  fof(f28,plain,(
% 2.49/1.01    ( ! [X2,X0,X3,X1] : (X0 = X2 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.49/1.01    inference(cnf_transformation,[],[f9])).
% 2.49/1.01  
% 2.49/1.01  fof(f2,axiom,(
% 2.49/1.01    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.49/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/1.01  
% 2.49/1.01  fof(f8,plain,(
% 2.49/1.01    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.49/1.01    inference(ennf_transformation,[],[f2])).
% 2.49/1.01  
% 2.49/1.01  fof(f27,plain,(
% 2.49/1.01    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.49/1.01    inference(cnf_transformation,[],[f8])).
% 2.49/1.01  
% 2.49/1.01  fof(f33,plain,(
% 2.49/1.01    ( ! [X0,X1] : (v2_tex_2(X1,X0) | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.49/1.01    inference(cnf_transformation,[],[f19])).
% 2.49/1.01  
% 2.49/1.01  fof(f32,plain,(
% 2.49/1.01    ( ! [X4,X0,X1] : (k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4 | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.49/1.01    inference(cnf_transformation,[],[f19])).
% 2.49/1.01  
% 2.49/1.01  fof(f39,plain,(
% 2.49/1.01    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))),
% 2.49/1.01    inference(cnf_transformation,[],[f24])).
% 2.49/1.01  
% 2.49/1.01  fof(f43,plain,(
% 2.49/1.01    ~v2_tex_2(sK5,sK3)),
% 2.49/1.01    inference(cnf_transformation,[],[f24])).
% 2.49/1.01  
% 2.49/1.01  fof(f42,plain,(
% 2.49/1.01    v2_tex_2(sK4,sK2)),
% 2.49/1.01    inference(cnf_transformation,[],[f24])).
% 2.49/1.01  
% 2.49/1.01  fof(f41,plain,(
% 2.49/1.01    sK4 = sK5),
% 2.49/1.01    inference(cnf_transformation,[],[f24])).
% 2.49/1.01  
% 2.49/1.01  fof(f35,plain,(
% 2.49/1.01    ( ! [X0,X3,X1] : (v2_tex_2(X1,X0) | k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.49/1.01    inference(cnf_transformation,[],[f19])).
% 2.49/1.01  
% 2.49/1.01  fof(f31,plain,(
% 2.49/1.01    ( ! [X4,X0,X1] : (v3_pre_topc(sK1(X0,X1,X4),X0) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.49/1.01    inference(cnf_transformation,[],[f19])).
% 2.49/1.01  
% 2.49/1.01  fof(f29,plain,(
% 2.49/1.01    ( ! [X2,X0,X3,X1] : (X1 = X3 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.49/1.01    inference(cnf_transformation,[],[f9])).
% 2.49/1.01  
% 2.49/1.01  cnf(c_159,plain,( X0_2 = X0_2 ),theory(equality) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_10,plain,
% 2.49/1.01      ( ~ r1_tarski(X0,X1)
% 2.49/1.01      | ~ v2_tex_2(X1,X2)
% 2.49/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.49/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 2.49/1.01      | m1_subset_1(sK1(X2,X1,X0),k1_zfmisc_1(u1_struct_0(X2)))
% 2.49/1.01      | ~ l1_pre_topc(X2) ),
% 2.49/1.01      inference(cnf_transformation,[],[f30]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_18,negated_conjecture,
% 2.49/1.01      ( l1_pre_topc(sK2) ),
% 2.49/1.01      inference(cnf_transformation,[],[f36]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_518,plain,
% 2.49/1.01      ( ~ r1_tarski(X0,X1)
% 2.49/1.01      | ~ v2_tex_2(X1,X2)
% 2.49/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.49/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 2.49/1.01      | m1_subset_1(sK1(X2,X1,X0),k1_zfmisc_1(u1_struct_0(X2)))
% 2.49/1.01      | sK2 != X2 ),
% 2.49/1.01      inference(resolution_lifted,[status(thm)],[c_10,c_18]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_519,plain,
% 2.49/1.01      ( ~ r1_tarski(X0,X1)
% 2.49/1.01      | ~ v2_tex_2(X1,sK2)
% 2.49/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.49/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.49/1.01      | m1_subset_1(sK1(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.49/1.01      inference(unflattening,[status(thm)],[c_518]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_6,plain,
% 2.49/1.01      ( r1_tarski(sK0(X0,X1),X1)
% 2.49/1.01      | v2_tex_2(X1,X0)
% 2.49/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.49/1.01      | ~ l1_pre_topc(X0) ),
% 2.49/1.01      inference(cnf_transformation,[],[f34]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_17,negated_conjecture,
% 2.49/1.01      ( l1_pre_topc(sK3) ),
% 2.49/1.01      inference(cnf_transformation,[],[f37]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_411,plain,
% 2.49/1.01      ( r1_tarski(sK0(X0,X1),X1)
% 2.49/1.01      | v2_tex_2(X1,X0)
% 2.49/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.49/1.01      | sK3 != X0 ),
% 2.49/1.01      inference(resolution_lifted,[status(thm)],[c_6,c_17]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_412,plain,
% 2.49/1.01      ( r1_tarski(sK0(sK3,X0),X0)
% 2.49/1.01      | v2_tex_2(X0,sK3)
% 2.49/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.49/1.01      inference(unflattening,[status(thm)],[c_411]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_853,plain,
% 2.49/1.01      ( ~ v2_tex_2(X0,sK2)
% 2.49/1.01      | v2_tex_2(X1,sK3)
% 2.49/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.49/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.49/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.49/1.01      | m1_subset_1(sK1(sK2,X0,X2),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.49/1.01      | X1 != X0
% 2.49/1.01      | sK0(sK3,X1) != X2 ),
% 2.49/1.01      inference(resolution_lifted,[status(thm)],[c_519,c_412]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_854,plain,
% 2.49/1.01      ( ~ v2_tex_2(X0,sK2)
% 2.49/1.01      | v2_tex_2(X0,sK3)
% 2.49/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.49/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.49/1.01      | m1_subset_1(sK1(sK2,X0,sK0(sK3,X0)),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.49/1.01      | ~ m1_subset_1(sK0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.49/1.01      inference(unflattening,[status(thm)],[c_853]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1494,plain,
% 2.49/1.01      ( v2_tex_2(X0,sK2) != iProver_top
% 2.49/1.01      | v2_tex_2(X0,sK3) = iProver_top
% 2.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.49/1.01      | m1_subset_1(sK1(sK2,X0,sK0(sK3,X0)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 2.49/1.01      | m1_subset_1(sK0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_854]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_14,negated_conjecture,
% 2.49/1.01      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
% 2.49/1.01      inference(cnf_transformation,[],[f40]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_4,plain,
% 2.49/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.49/1.01      | X2 = X1
% 2.49/1.01      | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
% 2.49/1.01      inference(cnf_transformation,[],[f28]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1507,plain,
% 2.49/1.01      ( X0 = X1
% 2.49/1.01      | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
% 2.49/1.01      | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1973,plain,
% 2.49/1.01      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(X0,X1)
% 2.49/1.01      | u1_struct_0(sK2) = X0
% 2.49/1.01      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.49/1.01      inference(superposition,[status(thm)],[c_14,c_1507]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2,plain,
% 2.49/1.01      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.49/1.01      | ~ l1_pre_topc(X0) ),
% 2.49/1.01      inference(cnf_transformation,[],[f27]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_48,plain,
% 2.49/1.01      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 2.49/1.01      | ~ l1_pre_topc(sK2) ),
% 2.49/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1974,plain,
% 2.49/1.01      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(X0,X1)
% 2.49/1.01      | u1_struct_0(sK2) = X0
% 2.49/1.01      | m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
% 2.49/1.01      inference(superposition,[status(thm)],[c_14,c_1507]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1991,plain,
% 2.49/1.01      ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 2.49/1.01      | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(X0,X1)
% 2.49/1.01      | u1_struct_0(sK2) = X0 ),
% 2.49/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_1974]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2049,plain,
% 2.49/1.01      ( u1_struct_0(sK2) = X0
% 2.49/1.01      | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(X0,X1) ),
% 2.49/1.01      inference(global_propositional_subsumption,
% 2.49/1.01                [status(thm)],
% 2.49/1.01                [c_1973,c_18,c_48,c_1991]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2050,plain,
% 2.49/1.01      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(X0,X1)
% 2.49/1.01      | u1_struct_0(sK2) = X0 ),
% 2.49/1.01      inference(renaming,[status(thm)],[c_2049]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2055,plain,
% 2.49/1.01      ( u1_struct_0(sK3) = u1_struct_0(sK2) ),
% 2.49/1.01      inference(equality_resolution,[status(thm)],[c_2050]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2699,plain,
% 2.49/1.01      ( v2_tex_2(X0,sK2) != iProver_top
% 2.49/1.01      | v2_tex_2(X0,sK3) = iProver_top
% 2.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.49/1.01      | m1_subset_1(sK1(sK2,X0,sK0(sK3,X0)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 2.49/1.01      | m1_subset_1(sK0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.49/1.01      inference(light_normalisation,[status(thm)],[c_1494,c_2055]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_7,plain,
% 2.49/1.01      ( v2_tex_2(X0,X1)
% 2.49/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.49/1.01      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.49/1.01      | ~ l1_pre_topc(X1) ),
% 2.49/1.01      inference(cnf_transformation,[],[f33]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_339,plain,
% 2.49/1.01      ( v2_tex_2(X0,X1)
% 2.49/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.49/1.01      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.49/1.01      | sK3 != X1 ),
% 2.49/1.01      inference(resolution_lifted,[status(thm)],[c_7,c_17]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_340,plain,
% 2.49/1.01      ( v2_tex_2(X0,sK3)
% 2.49/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.49/1.01      | m1_subset_1(sK0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.49/1.01      inference(unflattening,[status(thm)],[c_339]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1502,plain,
% 2.49/1.01      ( v2_tex_2(X0,sK3) = iProver_top
% 2.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.49/1.01      | m1_subset_1(sK0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_340]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2705,plain,
% 2.49/1.01      ( v2_tex_2(X0,sK2) != iProver_top
% 2.49/1.01      | v2_tex_2(X0,sK3) = iProver_top
% 2.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.49/1.01      | m1_subset_1(sK1(sK2,X0,sK0(sK3,X0)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.49/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_2699,c_1502]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_375,plain,
% 2.49/1.01      ( v2_tex_2(X0,X1)
% 2.49/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.49/1.01      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.49/1.01      | sK2 != X1 ),
% 2.49/1.01      inference(resolution_lifted,[status(thm)],[c_7,c_18]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_376,plain,
% 2.49/1.01      ( v2_tex_2(X0,sK2)
% 2.49/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.49/1.01      | m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.49/1.01      inference(unflattening,[status(thm)],[c_375]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1500,plain,
% 2.49/1.01      ( v2_tex_2(X0,sK2) = iProver_top
% 2.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.49/1.01      | m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_376]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2422,plain,
% 2.49/1.01      ( v2_tex_2(X0,sK2) = iProver_top
% 2.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.49/1.01      | m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.49/1.01      inference(light_normalisation,[status(thm)],[c_1500,c_2055]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_8,plain,
% 2.49/1.01      ( ~ r1_tarski(X0,X1)
% 2.49/1.01      | ~ v2_tex_2(X1,X2)
% 2.49/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.49/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 2.49/1.01      | ~ l1_pre_topc(X2)
% 2.49/1.01      | k9_subset_1(u1_struct_0(X2),X1,sK1(X2,X1,X0)) = X0 ),
% 2.49/1.01      inference(cnf_transformation,[],[f32]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_497,plain,
% 2.49/1.01      ( ~ r1_tarski(X0,X1)
% 2.49/1.01      | ~ v2_tex_2(X1,X2)
% 2.49/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.49/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 2.49/1.01      | k9_subset_1(u1_struct_0(X2),X1,sK1(X2,X1,X0)) = X0
% 2.49/1.01      | sK3 != X2 ),
% 2.49/1.01      inference(resolution_lifted,[status(thm)],[c_8,c_17]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_498,plain,
% 2.49/1.01      ( ~ r1_tarski(X0,X1)
% 2.49/1.01      | ~ v2_tex_2(X1,sK3)
% 2.49/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.49/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.49/1.01      | k9_subset_1(u1_struct_0(sK3),X1,sK1(sK3,X1,X0)) = X0 ),
% 2.49/1.01      inference(unflattening,[status(thm)],[c_497]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_433,plain,
% 2.49/1.01      ( r1_tarski(sK0(X0,X1),X1)
% 2.49/1.01      | v2_tex_2(X1,X0)
% 2.49/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.49/1.01      | sK2 != X0 ),
% 2.49/1.01      inference(resolution_lifted,[status(thm)],[c_6,c_18]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_434,plain,
% 2.49/1.01      ( r1_tarski(sK0(sK2,X0),X0)
% 2.49/1.01      | v2_tex_2(X0,sK2)
% 2.49/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.49/1.01      inference(unflattening,[status(thm)],[c_433]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_889,plain,
% 2.49/1.01      ( v2_tex_2(X0,sK2)
% 2.49/1.01      | ~ v2_tex_2(X1,sK3)
% 2.49/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.49/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.49/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.49/1.01      | X0 != X1
% 2.49/1.01      | k9_subset_1(u1_struct_0(sK3),X1,sK1(sK3,X1,X2)) = X2
% 2.49/1.01      | sK0(sK2,X0) != X2 ),
% 2.49/1.01      inference(resolution_lifted,[status(thm)],[c_498,c_434]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_890,plain,
% 2.49/1.01      ( v2_tex_2(X0,sK2)
% 2.49/1.01      | ~ v2_tex_2(X0,sK3)
% 2.49/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.49/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.49/1.01      | ~ m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.49/1.01      | k9_subset_1(u1_struct_0(sK3),X0,sK1(sK3,X0,sK0(sK2,X0))) = sK0(sK2,X0) ),
% 2.49/1.01      inference(unflattening,[status(thm)],[c_889]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1493,plain,
% 2.49/1.01      ( k9_subset_1(u1_struct_0(sK3),X0,sK1(sK3,X0,sK0(sK2,X0))) = sK0(sK2,X0)
% 2.49/1.01      | v2_tex_2(X0,sK2) = iProver_top
% 2.49/1.01      | v2_tex_2(X0,sK3) != iProver_top
% 2.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.49/1.01      | m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_890]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_891,plain,
% 2.49/1.01      ( k9_subset_1(u1_struct_0(sK3),X0,sK1(sK3,X0,sK0(sK2,X0))) = sK0(sK2,X0)
% 2.49/1.01      | v2_tex_2(X0,sK2) = iProver_top
% 2.49/1.01      | v2_tex_2(X0,sK3) != iProver_top
% 2.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.49/1.01      | m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_890]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2825,plain,
% 2.49/1.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.49/1.01      | v2_tex_2(X0,sK3) != iProver_top
% 2.49/1.01      | v2_tex_2(X0,sK2) = iProver_top
% 2.49/1.01      | k9_subset_1(u1_struct_0(sK3),X0,sK1(sK3,X0,sK0(sK2,X0))) = sK0(sK2,X0) ),
% 2.49/1.01      inference(global_propositional_subsumption,
% 2.49/1.01                [status(thm)],
% 2.49/1.01                [c_1493,c_891,c_2422]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2826,plain,
% 2.49/1.01      ( k9_subset_1(u1_struct_0(sK3),X0,sK1(sK3,X0,sK0(sK2,X0))) = sK0(sK2,X0)
% 2.49/1.01      | v2_tex_2(X0,sK2) = iProver_top
% 2.49/1.01      | v2_tex_2(X0,sK3) != iProver_top
% 2.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.49/1.01      inference(renaming,[status(thm)],[c_2825]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2831,plain,
% 2.49/1.01      ( k9_subset_1(u1_struct_0(sK3),X0,sK1(sK3,X0,sK0(sK2,X0))) = sK0(sK2,X0)
% 2.49/1.01      | v2_tex_2(X0,sK2) = iProver_top
% 2.49/1.01      | v2_tex_2(X0,sK3) != iProver_top
% 2.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.49/1.01      inference(light_normalisation,[status(thm)],[c_2826,c_2055]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2841,plain,
% 2.49/1.01      ( k9_subset_1(u1_struct_0(sK3),sK0(sK2,X0),sK1(sK3,sK0(sK2,X0),sK0(sK2,sK0(sK2,X0)))) = sK0(sK2,sK0(sK2,X0))
% 2.49/1.01      | v2_tex_2(X0,sK2) = iProver_top
% 2.49/1.01      | v2_tex_2(sK0(sK2,X0),sK2) = iProver_top
% 2.49/1.01      | v2_tex_2(sK0(sK2,X0),sK3) != iProver_top
% 2.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.49/1.01      inference(superposition,[status(thm)],[c_2422,c_2831]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_3342,plain,
% 2.49/1.01      ( k9_subset_1(u1_struct_0(sK3),sK0(sK2,sK1(sK2,X0,sK0(sK3,X0))),sK1(sK3,sK0(sK2,sK1(sK2,X0,sK0(sK3,X0))),sK0(sK2,sK0(sK2,sK1(sK2,X0,sK0(sK3,X0)))))) = sK0(sK2,sK0(sK2,sK1(sK2,X0,sK0(sK3,X0))))
% 2.49/1.01      | v2_tex_2(X0,sK2) != iProver_top
% 2.49/1.01      | v2_tex_2(X0,sK3) = iProver_top
% 2.49/1.01      | v2_tex_2(sK1(sK2,X0,sK0(sK3,X0)),sK2) = iProver_top
% 2.49/1.01      | v2_tex_2(sK0(sK2,sK1(sK2,X0,sK0(sK3,X0))),sK2) = iProver_top
% 2.49/1.01      | v2_tex_2(sK0(sK2,sK1(sK2,X0,sK0(sK3,X0))),sK3) != iProver_top
% 2.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.49/1.01      inference(superposition,[status(thm)],[c_2705,c_2841]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_455,plain,
% 2.49/1.01      ( ~ r1_tarski(X0,X1)
% 2.49/1.01      | ~ v2_tex_2(X1,X2)
% 2.49/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.49/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 2.49/1.01      | m1_subset_1(sK1(X2,X1,X0),k1_zfmisc_1(u1_struct_0(X2)))
% 2.49/1.01      | sK3 != X2 ),
% 2.49/1.01      inference(resolution_lifted,[status(thm)],[c_10,c_17]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_456,plain,
% 2.49/1.01      ( ~ r1_tarski(X0,X1)
% 2.49/1.01      | ~ v2_tex_2(X1,sK3)
% 2.49/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.49/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.49/1.01      | m1_subset_1(sK1(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.49/1.01      inference(unflattening,[status(thm)],[c_455]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_937,plain,
% 2.49/1.01      ( v2_tex_2(X0,sK2)
% 2.49/1.01      | ~ v2_tex_2(X1,sK3)
% 2.49/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.49/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.49/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.49/1.01      | m1_subset_1(sK1(sK3,X1,X2),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.49/1.01      | X0 != X1
% 2.49/1.01      | sK0(sK2,X0) != X2 ),
% 2.49/1.01      inference(resolution_lifted,[status(thm)],[c_456,c_434]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_938,plain,
% 2.49/1.01      ( v2_tex_2(X0,sK2)
% 2.49/1.01      | ~ v2_tex_2(X0,sK3)
% 2.49/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.49/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.49/1.01      | m1_subset_1(sK1(sK3,X0,sK0(sK2,X0)),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.49/1.01      | ~ m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.49/1.01      inference(unflattening,[status(thm)],[c_937]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1491,plain,
% 2.49/1.01      ( v2_tex_2(X0,sK2) = iProver_top
% 2.49/1.01      | v2_tex_2(X0,sK3) != iProver_top
% 2.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.49/1.01      | m1_subset_1(sK1(sK3,X0,sK0(sK2,X0)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 2.49/1.01      | m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_938]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2194,plain,
% 2.49/1.01      ( v2_tex_2(X0,sK2) = iProver_top
% 2.49/1.01      | v2_tex_2(X0,sK3) != iProver_top
% 2.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.49/1.01      | m1_subset_1(sK1(sK3,X0,sK0(sK2,X0)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 2.49/1.01      | m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.49/1.01      inference(demodulation,[status(thm)],[c_2055,c_1491]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2602,plain,
% 2.49/1.01      ( m1_subset_1(sK1(sK3,X0,sK0(sK2,X0)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 2.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.49/1.01      | v2_tex_2(X0,sK3) != iProver_top
% 2.49/1.01      | v2_tex_2(X0,sK2) = iProver_top ),
% 2.49/1.01      inference(global_propositional_subsumption,[status(thm)],[c_2194,c_2422]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2603,plain,
% 2.49/1.01      ( v2_tex_2(X0,sK2) = iProver_top
% 2.49/1.01      | v2_tex_2(X0,sK3) != iProver_top
% 2.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.49/1.01      | m1_subset_1(sK1(sK3,X0,sK0(sK2,X0)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.49/1.01      inference(renaming,[status(thm)],[c_2602]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_3341,plain,
% 2.49/1.01      ( k9_subset_1(u1_struct_0(sK3),sK0(sK2,sK1(sK3,X0,sK0(sK2,X0))),sK1(sK3,sK0(sK2,sK1(sK3,X0,sK0(sK2,X0))),sK0(sK2,sK0(sK2,sK1(sK3,X0,sK0(sK2,X0)))))) = sK0(sK2,sK0(sK2,sK1(sK3,X0,sK0(sK2,X0))))
% 2.49/1.01      | v2_tex_2(X0,sK2) = iProver_top
% 2.49/1.01      | v2_tex_2(X0,sK3) != iProver_top
% 2.49/1.01      | v2_tex_2(sK1(sK3,X0,sK0(sK2,X0)),sK2) = iProver_top
% 2.49/1.01      | v2_tex_2(sK0(sK2,sK1(sK3,X0,sK0(sK2,X0))),sK2) = iProver_top
% 2.49/1.01      | v2_tex_2(sK0(sK2,sK1(sK3,X0,sK0(sK2,X0))),sK3) != iProver_top
% 2.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.49/1.01      inference(superposition,[status(thm)],[c_2603,c_2841]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_3340,plain,
% 2.49/1.01      ( k9_subset_1(u1_struct_0(sK3),sK0(sK2,sK0(sK2,X0)),sK1(sK3,sK0(sK2,sK0(sK2,X0)),sK0(sK2,sK0(sK2,sK0(sK2,X0))))) = sK0(sK2,sK0(sK2,sK0(sK2,X0)))
% 2.49/1.01      | v2_tex_2(X0,sK2) = iProver_top
% 2.49/1.01      | v2_tex_2(sK0(sK2,X0),sK2) = iProver_top
% 2.49/1.01      | v2_tex_2(sK0(sK2,sK0(sK2,X0)),sK2) = iProver_top
% 2.49/1.01      | v2_tex_2(sK0(sK2,sK0(sK2,X0)),sK3) != iProver_top
% 2.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.49/1.01      inference(superposition,[status(thm)],[c_2422,c_2841]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_3339,plain,
% 2.49/1.01      ( k9_subset_1(u1_struct_0(sK3),sK0(sK2,sK0(sK3,X0)),sK1(sK3,sK0(sK2,sK0(sK3,X0)),sK0(sK2,sK0(sK2,sK0(sK3,X0))))) = sK0(sK2,sK0(sK2,sK0(sK3,X0)))
% 2.49/1.01      | v2_tex_2(X0,sK3) = iProver_top
% 2.49/1.01      | v2_tex_2(sK0(sK2,sK0(sK3,X0)),sK2) = iProver_top
% 2.49/1.01      | v2_tex_2(sK0(sK2,sK0(sK3,X0)),sK3) != iProver_top
% 2.49/1.01      | v2_tex_2(sK0(sK3,X0),sK2) = iProver_top
% 2.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.49/1.01      inference(superposition,[status(thm)],[c_1502,c_2841]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_15,negated_conjecture,
% 2.49/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.49/1.01      inference(cnf_transformation,[],[f39]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1504,plain,
% 2.49/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_560,plain,
% 2.49/1.01      ( ~ r1_tarski(X0,X1)
% 2.49/1.01      | ~ v2_tex_2(X1,X2)
% 2.49/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.49/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 2.49/1.01      | k9_subset_1(u1_struct_0(X2),X1,sK1(X2,X1,X0)) = X0
% 2.49/1.01      | sK2 != X2 ),
% 2.49/1.01      inference(resolution_lifted,[status(thm)],[c_8,c_18]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_561,plain,
% 2.49/1.01      ( ~ r1_tarski(X0,X1)
% 2.49/1.01      | ~ v2_tex_2(X1,sK2)
% 2.49/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.49/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.49/1.01      | k9_subset_1(u1_struct_0(sK2),X1,sK1(sK2,X1,X0)) = X0 ),
% 2.49/1.01      inference(unflattening,[status(thm)],[c_560]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_805,plain,
% 2.49/1.01      ( ~ v2_tex_2(X0,sK2)
% 2.49/1.01      | v2_tex_2(X1,sK3)
% 2.49/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.49/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.49/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.49/1.01      | X1 != X0
% 2.49/1.01      | k9_subset_1(u1_struct_0(sK2),X0,sK1(sK2,X0,X2)) = X2
% 2.49/1.01      | sK0(sK3,X1) != X2 ),
% 2.49/1.01      inference(resolution_lifted,[status(thm)],[c_561,c_412]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_806,plain,
% 2.49/1.01      ( ~ v2_tex_2(X0,sK2)
% 2.49/1.01      | v2_tex_2(X0,sK3)
% 2.49/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.49/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.49/1.01      | ~ m1_subset_1(sK0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.49/1.01      | k9_subset_1(u1_struct_0(sK2),X0,sK1(sK2,X0,sK0(sK3,X0))) = sK0(sK3,X0) ),
% 2.49/1.01      inference(unflattening,[status(thm)],[c_805]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1496,plain,
% 2.49/1.01      ( k9_subset_1(u1_struct_0(sK2),X0,sK1(sK2,X0,sK0(sK3,X0))) = sK0(sK3,X0)
% 2.49/1.01      | v2_tex_2(X0,sK2) != iProver_top
% 2.49/1.01      | v2_tex_2(X0,sK3) = iProver_top
% 2.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.49/1.01      | m1_subset_1(sK0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_806]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2901,plain,
% 2.49/1.01      ( k9_subset_1(u1_struct_0(sK3),X0,sK1(sK2,X0,sK0(sK3,X0))) = sK0(sK3,X0)
% 2.49/1.01      | v2_tex_2(X0,sK2) != iProver_top
% 2.49/1.01      | v2_tex_2(X0,sK3) = iProver_top
% 2.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.49/1.01      | m1_subset_1(sK0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.49/1.01      inference(light_normalisation,[status(thm)],[c_1496,c_2055]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2907,plain,
% 2.49/1.01      ( k9_subset_1(u1_struct_0(sK3),X0,sK1(sK2,X0,sK0(sK3,X0))) = sK0(sK3,X0)
% 2.49/1.01      | v2_tex_2(X0,sK2) != iProver_top
% 2.49/1.01      | v2_tex_2(X0,sK3) = iProver_top
% 2.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.49/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_2901,c_1502]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2911,plain,
% 2.49/1.01      ( k9_subset_1(u1_struct_0(sK3),sK5,sK1(sK2,sK5,sK0(sK3,sK5))) = sK0(sK3,sK5)
% 2.49/1.01      | v2_tex_2(sK5,sK2) != iProver_top
% 2.49/1.01      | v2_tex_2(sK5,sK3) = iProver_top ),
% 2.49/1.01      inference(superposition,[status(thm)],[c_1504,c_2907]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_11,negated_conjecture,
% 2.49/1.01      ( ~ v2_tex_2(sK5,sK3) ),
% 2.49/1.01      inference(cnf_transformation,[],[f43]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_24,plain,
% 2.49/1.01      ( v2_tex_2(sK5,sK3) != iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_12,negated_conjecture,
% 2.49/1.01      ( v2_tex_2(sK4,sK2) ),
% 2.49/1.01      inference(cnf_transformation,[],[f42]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1505,plain,
% 2.49/1.01      ( v2_tex_2(sK4,sK2) = iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_13,negated_conjecture,
% 2.49/1.01      ( sK4 = sK5 ),
% 2.49/1.01      inference(cnf_transformation,[],[f41]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1511,plain,
% 2.49/1.01      ( v2_tex_2(sK5,sK2) = iProver_top ),
% 2.49/1.01      inference(light_normalisation,[status(thm)],[c_1505,c_13]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_3017,plain,
% 2.49/1.01      ( k9_subset_1(u1_struct_0(sK3),sK5,sK1(sK2,sK5,sK0(sK3,sK5))) = sK0(sK3,sK5) ),
% 2.49/1.01      inference(global_propositional_subsumption,
% 2.49/1.01                [status(thm)],
% 2.49/1.01                [c_2911,c_24,c_1511]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_5,plain,
% 2.49/1.01      ( v2_tex_2(X0,X1)
% 2.49/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.49/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.49/1.01      | ~ v3_pre_topc(X2,X1)
% 2.49/1.01      | ~ l1_pre_topc(X1)
% 2.49/1.01      | k9_subset_1(u1_struct_0(X1),X0,X2) != sK0(X1,X0) ),
% 2.49/1.01      inference(cnf_transformation,[],[f35]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_354,plain,
% 2.49/1.01      ( v2_tex_2(X0,X1)
% 2.49/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.49/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.49/1.01      | ~ v3_pre_topc(X2,X1)
% 2.49/1.01      | k9_subset_1(u1_struct_0(X1),X0,X2) != sK0(X1,X0)
% 2.49/1.01      | sK3 != X1 ),
% 2.49/1.01      inference(resolution_lifted,[status(thm)],[c_5,c_17]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_355,plain,
% 2.49/1.01      ( v2_tex_2(X0,sK3)
% 2.49/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.49/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.49/1.01      | ~ v3_pre_topc(X1,sK3)
% 2.49/1.01      | k9_subset_1(u1_struct_0(sK3),X0,X1) != sK0(sK3,X0) ),
% 2.49/1.01      inference(unflattening,[status(thm)],[c_354]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1501,plain,
% 2.49/1.01      ( k9_subset_1(u1_struct_0(sK3),X0,X1) != sK0(sK3,X0)
% 2.49/1.01      | v2_tex_2(X0,sK3) = iProver_top
% 2.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.49/1.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.49/1.01      | v3_pre_topc(X1,sK3) != iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_355]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_3020,plain,
% 2.49/1.01      ( v2_tex_2(sK5,sK3) = iProver_top
% 2.49/1.01      | m1_subset_1(sK1(sK2,sK5,sK0(sK3,sK5)),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.49/1.01      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.49/1.01      | v3_pre_topc(sK1(sK2,sK5,sK0(sK3,sK5)),sK3) != iProver_top ),
% 2.49/1.01      inference(superposition,[status(thm)],[c_3017,c_1501]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_22,plain,
% 2.49/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_3032,plain,
% 2.49/1.01      ( m1_subset_1(sK1(sK2,sK5,sK0(sK3,sK5)),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.49/1.01      | v3_pre_topc(sK1(sK2,sK5,sK0(sK3,sK5)),sK3) != iProver_top ),
% 2.49/1.01      inference(global_propositional_subsumption,
% 2.49/1.01                [status(thm)],
% 2.49/1.01                [c_3020,c_22,c_24]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_3038,plain,
% 2.49/1.01      ( v2_tex_2(sK5,sK2) != iProver_top
% 2.49/1.01      | v2_tex_2(sK5,sK3) = iProver_top
% 2.49/1.01      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.49/1.01      | v3_pre_topc(sK1(sK2,sK5,sK0(sK3,sK5)),sK3) != iProver_top ),
% 2.49/1.01      inference(superposition,[status(thm)],[c_2705,c_3032]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_3327,plain,
% 2.49/1.01      ( v3_pre_topc(sK1(sK2,sK5,sK0(sK3,sK5)),sK3) != iProver_top ),
% 2.49/1.01      inference(global_propositional_subsumption,
% 2.49/1.01                [status(thm)],
% 2.49/1.01                [c_3038,c_22,c_24,c_1511]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2840,plain,
% 2.49/1.01      ( k9_subset_1(u1_struct_0(sK3),sK0(sK3,X0),sK1(sK3,sK0(sK3,X0),sK0(sK2,sK0(sK3,X0)))) = sK0(sK2,sK0(sK3,X0))
% 2.49/1.01      | v2_tex_2(X0,sK3) = iProver_top
% 2.49/1.01      | v2_tex_2(sK0(sK3,X0),sK2) = iProver_top
% 2.49/1.01      | v2_tex_2(sK0(sK3,X0),sK3) != iProver_top
% 2.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.49/1.01      inference(superposition,[status(thm)],[c_1502,c_2831]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_3094,plain,
% 2.49/1.01      ( k9_subset_1(u1_struct_0(sK3),sK0(sK3,sK5),sK1(sK3,sK0(sK3,sK5),sK0(sK2,sK0(sK3,sK5)))) = sK0(sK2,sK0(sK3,sK5))
% 2.49/1.01      | v2_tex_2(sK0(sK3,sK5),sK2) = iProver_top
% 2.49/1.01      | v2_tex_2(sK0(sK3,sK5),sK3) != iProver_top
% 2.49/1.01      | v2_tex_2(sK5,sK3) = iProver_top ),
% 2.49/1.01      inference(superposition,[status(thm)],[c_1504,c_2840]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_3173,plain,
% 2.49/1.01      ( v2_tex_2(sK0(sK3,sK5),sK3) != iProver_top
% 2.49/1.01      | v2_tex_2(sK0(sK3,sK5),sK2) = iProver_top
% 2.49/1.01      | k9_subset_1(u1_struct_0(sK3),sK0(sK3,sK5),sK1(sK3,sK0(sK3,sK5),sK0(sK2,sK0(sK3,sK5)))) = sK0(sK2,sK0(sK3,sK5)) ),
% 2.49/1.01      inference(global_propositional_subsumption,[status(thm)],[c_3094,c_24]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_3174,plain,
% 2.49/1.01      ( k9_subset_1(u1_struct_0(sK3),sK0(sK3,sK5),sK1(sK3,sK0(sK3,sK5),sK0(sK2,sK0(sK3,sK5)))) = sK0(sK2,sK0(sK3,sK5))
% 2.49/1.01      | v2_tex_2(sK0(sK3,sK5),sK2) = iProver_top
% 2.49/1.01      | v2_tex_2(sK0(sK3,sK5),sK3) != iProver_top ),
% 2.49/1.01      inference(renaming,[status(thm)],[c_3173]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_3098,plain,
% 2.49/1.01      ( k9_subset_1(u1_struct_0(sK3),sK0(sK3,sK1(sK2,X0,sK0(sK3,X0))),sK1(sK3,sK0(sK3,sK1(sK2,X0,sK0(sK3,X0))),sK0(sK2,sK0(sK3,sK1(sK2,X0,sK0(sK3,X0)))))) = sK0(sK2,sK0(sK3,sK1(sK2,X0,sK0(sK3,X0))))
% 2.49/1.01      | v2_tex_2(X0,sK2) != iProver_top
% 2.49/1.01      | v2_tex_2(X0,sK3) = iProver_top
% 2.49/1.01      | v2_tex_2(sK1(sK2,X0,sK0(sK3,X0)),sK3) = iProver_top
% 2.49/1.01      | v2_tex_2(sK0(sK3,sK1(sK2,X0,sK0(sK3,X0))),sK2) = iProver_top
% 2.49/1.01      | v2_tex_2(sK0(sK3,sK1(sK2,X0,sK0(sK3,X0))),sK3) != iProver_top
% 2.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.49/1.01      inference(superposition,[status(thm)],[c_2705,c_2840]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_3097,plain,
% 2.49/1.01      ( k9_subset_1(u1_struct_0(sK3),sK0(sK3,sK1(sK3,X0,sK0(sK2,X0))),sK1(sK3,sK0(sK3,sK1(sK3,X0,sK0(sK2,X0))),sK0(sK2,sK0(sK3,sK1(sK3,X0,sK0(sK2,X0)))))) = sK0(sK2,sK0(sK3,sK1(sK3,X0,sK0(sK2,X0))))
% 2.49/1.01      | v2_tex_2(X0,sK2) = iProver_top
% 2.49/1.01      | v2_tex_2(X0,sK3) != iProver_top
% 2.49/1.01      | v2_tex_2(sK1(sK3,X0,sK0(sK2,X0)),sK3) = iProver_top
% 2.49/1.01      | v2_tex_2(sK0(sK3,sK1(sK3,X0,sK0(sK2,X0))),sK2) = iProver_top
% 2.49/1.01      | v2_tex_2(sK0(sK3,sK1(sK3,X0,sK0(sK2,X0))),sK3) != iProver_top
% 2.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.49/1.01      inference(superposition,[status(thm)],[c_2603,c_2840]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_3096,plain,
% 2.49/1.01      ( k9_subset_1(u1_struct_0(sK3),sK0(sK3,sK0(sK2,X0)),sK1(sK3,sK0(sK3,sK0(sK2,X0)),sK0(sK2,sK0(sK3,sK0(sK2,X0))))) = sK0(sK2,sK0(sK3,sK0(sK2,X0)))
% 2.49/1.01      | v2_tex_2(X0,sK2) = iProver_top
% 2.49/1.01      | v2_tex_2(sK0(sK2,X0),sK3) = iProver_top
% 2.49/1.01      | v2_tex_2(sK0(sK3,sK0(sK2,X0)),sK2) = iProver_top
% 2.49/1.01      | v2_tex_2(sK0(sK3,sK0(sK2,X0)),sK3) != iProver_top
% 2.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.49/1.01      inference(superposition,[status(thm)],[c_2422,c_2840]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_3095,plain,
% 2.49/1.01      ( k9_subset_1(u1_struct_0(sK3),sK0(sK3,sK0(sK3,X0)),sK1(sK3,sK0(sK3,sK0(sK3,X0)),sK0(sK2,sK0(sK3,sK0(sK3,X0))))) = sK0(sK2,sK0(sK3,sK0(sK3,X0)))
% 2.49/1.01      | v2_tex_2(X0,sK3) = iProver_top
% 2.49/1.01      | v2_tex_2(sK0(sK3,X0),sK3) = iProver_top
% 2.49/1.01      | v2_tex_2(sK0(sK3,sK0(sK3,X0)),sK2) = iProver_top
% 2.49/1.01      | v2_tex_2(sK0(sK3,sK0(sK3,X0)),sK3) != iProver_top
% 2.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.49/1.01      inference(superposition,[status(thm)],[c_1502,c_2840]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2915,plain,
% 2.49/1.01      ( k9_subset_1(u1_struct_0(sK3),sK1(sK2,X0,sK0(sK3,X0)),sK1(sK2,sK1(sK2,X0,sK0(sK3,X0)),sK0(sK3,sK1(sK2,X0,sK0(sK3,X0))))) = sK0(sK3,sK1(sK2,X0,sK0(sK3,X0)))
% 2.49/1.01      | v2_tex_2(X0,sK2) != iProver_top
% 2.49/1.01      | v2_tex_2(X0,sK3) = iProver_top
% 2.49/1.01      | v2_tex_2(sK1(sK2,X0,sK0(sK3,X0)),sK2) != iProver_top
% 2.49/1.01      | v2_tex_2(sK1(sK2,X0,sK0(sK3,X0)),sK3) = iProver_top
% 2.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.49/1.01      inference(superposition,[status(thm)],[c_2705,c_2907]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2914,plain,
% 2.49/1.01      ( k9_subset_1(u1_struct_0(sK3),sK1(sK3,X0,sK0(sK2,X0)),sK1(sK2,sK1(sK3,X0,sK0(sK2,X0)),sK0(sK3,sK1(sK3,X0,sK0(sK2,X0))))) = sK0(sK3,sK1(sK3,X0,sK0(sK2,X0)))
% 2.49/1.01      | v2_tex_2(X0,sK2) = iProver_top
% 2.49/1.01      | v2_tex_2(X0,sK3) != iProver_top
% 2.49/1.01      | v2_tex_2(sK1(sK3,X0,sK0(sK2,X0)),sK2) != iProver_top
% 2.49/1.01      | v2_tex_2(sK1(sK3,X0,sK0(sK2,X0)),sK3) = iProver_top
% 2.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.49/1.01      inference(superposition,[status(thm)],[c_2603,c_2907]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2913,plain,
% 2.49/1.01      ( k9_subset_1(u1_struct_0(sK3),sK0(sK2,X0),sK1(sK2,sK0(sK2,X0),sK0(sK3,sK0(sK2,X0)))) = sK0(sK3,sK0(sK2,X0))
% 2.49/1.01      | v2_tex_2(X0,sK2) = iProver_top
% 2.49/1.01      | v2_tex_2(sK0(sK2,X0),sK2) != iProver_top
% 2.49/1.01      | v2_tex_2(sK0(sK2,X0),sK3) = iProver_top
% 2.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.49/1.01      inference(superposition,[status(thm)],[c_2422,c_2907]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2912,plain,
% 2.49/1.01      ( k9_subset_1(u1_struct_0(sK3),sK0(sK3,X0),sK1(sK2,sK0(sK3,X0),sK0(sK3,sK0(sK3,X0)))) = sK0(sK3,sK0(sK3,X0))
% 2.49/1.01      | v2_tex_2(X0,sK3) = iProver_top
% 2.49/1.01      | v2_tex_2(sK0(sK3,X0),sK2) != iProver_top
% 2.49/1.01      | v2_tex_2(sK0(sK3,X0),sK3) = iProver_top
% 2.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.49/1.01      inference(superposition,[status(thm)],[c_1502,c_2907]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2843,plain,
% 2.49/1.01      ( k9_subset_1(u1_struct_0(sK3),sK1(sK2,X0,sK0(sK3,X0)),sK1(sK3,sK1(sK2,X0,sK0(sK3,X0)),sK0(sK2,sK1(sK2,X0,sK0(sK3,X0))))) = sK0(sK2,sK1(sK2,X0,sK0(sK3,X0)))
% 2.49/1.01      | v2_tex_2(X0,sK2) != iProver_top
% 2.49/1.01      | v2_tex_2(X0,sK3) = iProver_top
% 2.49/1.01      | v2_tex_2(sK1(sK2,X0,sK0(sK3,X0)),sK2) = iProver_top
% 2.49/1.01      | v2_tex_2(sK1(sK2,X0,sK0(sK3,X0)),sK3) != iProver_top
% 2.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.49/1.01      inference(superposition,[status(thm)],[c_2705,c_2831]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2842,plain,
% 2.49/1.01      ( k9_subset_1(u1_struct_0(sK3),sK1(sK3,X0,sK0(sK2,X0)),sK1(sK3,sK1(sK3,X0,sK0(sK2,X0)),sK0(sK2,sK1(sK3,X0,sK0(sK2,X0))))) = sK0(sK2,sK1(sK3,X0,sK0(sK2,X0)))
% 2.49/1.01      | v2_tex_2(X0,sK2) = iProver_top
% 2.49/1.01      | v2_tex_2(X0,sK3) != iProver_top
% 2.49/1.01      | v2_tex_2(sK1(sK3,X0,sK0(sK2,X0)),sK2) = iProver_top
% 2.49/1.01      | v2_tex_2(sK1(sK3,X0,sK0(sK2,X0)),sK3) != iProver_top
% 2.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.49/1.01      inference(superposition,[status(thm)],[c_2603,c_2831]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_9,plain,
% 2.49/1.01      ( ~ r1_tarski(X0,X1)
% 2.49/1.01      | ~ v2_tex_2(X1,X2)
% 2.49/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.49/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 2.49/1.01      | v3_pre_topc(sK1(X2,X1,X0),X2)
% 2.49/1.01      | ~ l1_pre_topc(X2) ),
% 2.49/1.01      inference(cnf_transformation,[],[f31]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_539,plain,
% 2.49/1.01      ( ~ r1_tarski(X0,X1)
% 2.49/1.01      | ~ v2_tex_2(X1,X2)
% 2.49/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.49/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 2.49/1.01      | v3_pre_topc(sK1(X2,X1,X0),X2)
% 2.49/1.01      | sK2 != X2 ),
% 2.49/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_18]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_540,plain,
% 2.49/1.01      ( ~ r1_tarski(X0,X1)
% 2.49/1.01      | ~ v2_tex_2(X1,sK2)
% 2.49/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.49/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.49/1.01      | v3_pre_topc(sK1(sK2,X1,X0),sK2) ),
% 2.49/1.01      inference(unflattening,[status(thm)],[c_539]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_829,plain,
% 2.49/1.01      ( ~ v2_tex_2(X0,sK2)
% 2.49/1.01      | v2_tex_2(X1,sK3)
% 2.49/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.49/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.49/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.49/1.01      | v3_pre_topc(sK1(sK2,X0,X2),sK2)
% 2.49/1.01      | X1 != X0
% 2.49/1.01      | sK0(sK3,X1) != X2 ),
% 2.49/1.01      inference(resolution_lifted,[status(thm)],[c_540,c_412]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_830,plain,
% 2.49/1.01      ( ~ v2_tex_2(X0,sK2)
% 2.49/1.01      | v2_tex_2(X0,sK3)
% 2.49/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.49/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.49/1.01      | ~ m1_subset_1(sK0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.49/1.01      | v3_pre_topc(sK1(sK2,X0,sK0(sK3,X0)),sK2) ),
% 2.49/1.01      inference(unflattening,[status(thm)],[c_829]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1495,plain,
% 2.49/1.01      ( v2_tex_2(X0,sK2) != iProver_top
% 2.49/1.01      | v2_tex_2(X0,sK3) = iProver_top
% 2.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.49/1.01      | m1_subset_1(sK0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.49/1.01      | v3_pre_topc(sK1(sK2,X0,sK0(sK3,X0)),sK2) = iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_830]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2688,plain,
% 2.49/1.01      ( v2_tex_2(X0,sK2) != iProver_top
% 2.49/1.01      | v2_tex_2(X0,sK3) = iProver_top
% 2.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.49/1.01      | m1_subset_1(sK0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.49/1.01      | v3_pre_topc(sK1(sK2,X0,sK0(sK3,X0)),sK2) = iProver_top ),
% 2.49/1.01      inference(light_normalisation,[status(thm)],[c_1495,c_2055]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2694,plain,
% 2.49/1.01      ( v2_tex_2(X0,sK2) != iProver_top
% 2.49/1.01      | v2_tex_2(X0,sK3) = iProver_top
% 2.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.49/1.01      | v3_pre_topc(sK1(sK2,X0,sK0(sK3,X0)),sK2) = iProver_top ),
% 2.49/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_2688,c_1502]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_390,plain,
% 2.49/1.01      ( v2_tex_2(X0,X1)
% 2.49/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.49/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.49/1.01      | ~ v3_pre_topc(X2,X1)
% 2.49/1.01      | k9_subset_1(u1_struct_0(X1),X0,X2) != sK0(X1,X0)
% 2.49/1.01      | sK2 != X1 ),
% 2.49/1.01      inference(resolution_lifted,[status(thm)],[c_5,c_18]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_391,plain,
% 2.49/1.01      ( v2_tex_2(X0,sK2)
% 2.49/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.49/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.49/1.01      | ~ v3_pre_topc(X1,sK2)
% 2.49/1.01      | k9_subset_1(u1_struct_0(sK2),X0,X1) != sK0(sK2,X0) ),
% 2.49/1.01      inference(unflattening,[status(thm)],[c_390]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1499,plain,
% 2.49/1.01      ( k9_subset_1(u1_struct_0(sK2),X0,X1) != sK0(sK2,X0)
% 2.49/1.01      | v2_tex_2(X0,sK2) = iProver_top
% 2.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.49/1.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.49/1.01      | v3_pre_topc(X1,sK2) != iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_391]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2542,plain,
% 2.49/1.01      ( k9_subset_1(u1_struct_0(sK3),X0,X1) != sK0(sK2,X0)
% 2.49/1.01      | v2_tex_2(X0,sK2) = iProver_top
% 2.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.49/1.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.49/1.01      | v3_pre_topc(X1,sK2) != iProver_top ),
% 2.49/1.01      inference(light_normalisation,[status(thm)],[c_1499,c_2055]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_476,plain,
% 2.49/1.01      ( ~ r1_tarski(X0,X1)
% 2.49/1.01      | ~ v2_tex_2(X1,X2)
% 2.49/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.49/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 2.49/1.01      | v3_pre_topc(sK1(X2,X1,X0),X2)
% 2.49/1.01      | sK3 != X2 ),
% 2.49/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_17]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_477,plain,
% 2.49/1.01      ( ~ r1_tarski(X0,X1)
% 2.49/1.01      | ~ v2_tex_2(X1,sK3)
% 2.49/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.49/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.49/1.01      | v3_pre_topc(sK1(sK3,X1,X0),sK3) ),
% 2.49/1.01      inference(unflattening,[status(thm)],[c_476]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_913,plain,
% 2.49/1.01      ( v2_tex_2(X0,sK2)
% 2.49/1.01      | ~ v2_tex_2(X1,sK3)
% 2.49/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.49/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.49/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.49/1.01      | v3_pre_topc(sK1(sK3,X1,X2),sK3)
% 2.49/1.01      | X0 != X1
% 2.49/1.01      | sK0(sK2,X0) != X2 ),
% 2.49/1.01      inference(resolution_lifted,[status(thm)],[c_477,c_434]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_914,plain,
% 2.49/1.01      ( v2_tex_2(X0,sK2)
% 2.49/1.01      | ~ v2_tex_2(X0,sK3)
% 2.49/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.49/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.49/1.01      | ~ m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.49/1.01      | v3_pre_topc(sK1(sK3,X0,sK0(sK2,X0)),sK3) ),
% 2.49/1.01      inference(unflattening,[status(thm)],[c_913]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1492,plain,
% 2.49/1.01      ( v2_tex_2(X0,sK2) = iProver_top
% 2.49/1.01      | v2_tex_2(X0,sK3) != iProver_top
% 2.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.49/1.01      | m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.49/1.01      | v3_pre_topc(sK1(sK3,X0,sK0(sK2,X0)),sK3) = iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_914]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2409,plain,
% 2.49/1.01      ( v2_tex_2(X0,sK2) = iProver_top
% 2.49/1.01      | v2_tex_2(X0,sK3) != iProver_top
% 2.49/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.49/1.01      | m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.49/1.01      | v3_pre_topc(sK1(sK3,X0,sK0(sK2,X0)),sK3) = iProver_top ),
% 2.49/1.01      inference(light_normalisation,[status(thm)],[c_1492,c_2055]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_3,plain,
% 2.49/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.49/1.01      | X2 = X0
% 2.49/1.01      | g1_pre_topc(X3,X2) != g1_pre_topc(X1,X0) ),
% 2.49/1.01      inference(cnf_transformation,[],[f29]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1508,plain,
% 2.49/1.01      ( X0 = X1
% 2.49/1.01      | g1_pre_topc(X2,X0) != g1_pre_topc(X3,X1)
% 2.49/1.01      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) != iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2027,plain,
% 2.49/1.01      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(X0,X1)
% 2.49/1.01      | u1_pre_topc(sK2) = X1
% 2.49/1.01      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.49/1.01      inference(superposition,[status(thm)],[c_14,c_1508]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_19,plain,
% 2.49/1.01      ( l1_pre_topc(sK2) = iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_47,plain,
% 2.49/1.01      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 2.49/1.01      | l1_pre_topc(X0) != iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_49,plain,
% 2.49/1.01      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
% 2.49/1.01      | l1_pre_topc(sK2) != iProver_top ),
% 2.49/1.01      inference(instantiation,[status(thm)],[c_47]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2028,plain,
% 2.49/1.01      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(X0,X1)
% 2.49/1.01      | u1_pre_topc(sK2) = X1
% 2.49/1.01      | m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
% 2.49/1.01      inference(superposition,[status(thm)],[c_14,c_1508]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2176,plain,
% 2.49/1.01      ( u1_pre_topc(sK2) = X1
% 2.49/1.01      | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(X0,X1) ),
% 2.49/1.01      inference(global_propositional_subsumption,
% 2.49/1.01                [status(thm)],
% 2.49/1.01                [c_2027,c_19,c_49,c_2028]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2177,plain,
% 2.49/1.01      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(X0,X1)
% 2.49/1.01      | u1_pre_topc(sK2) = X1 ),
% 2.49/1.01      inference(renaming,[status(thm)],[c_2176]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2182,plain,
% 2.49/1.01      ( u1_pre_topc(sK3) = u1_pre_topc(sK2) ),
% 2.49/1.01      inference(equality_resolution,[status(thm)],[c_2177]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2184,plain,
% 2.49/1.01      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(X0,X1)
% 2.49/1.01      | u1_pre_topc(sK3) = X1 ),
% 2.49/1.01      inference(demodulation,[status(thm)],[c_2182,c_2177]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2057,plain,
% 2.49/1.01      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(X0,X1)
% 2.49/1.01      | u1_struct_0(sK3) = X0 ),
% 2.49/1.01      inference(demodulation,[status(thm)],[c_2055,c_2050]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_426,plain,
% 2.49/1.01      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.49/1.01      | sK3 != X0 ),
% 2.49/1.01      inference(resolution_lifted,[status(thm)],[c_2,c_17]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_427,plain,
% 2.49/1.01      ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
% 2.49/1.01      inference(unflattening,[status(thm)],[c_426]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1498,plain,
% 2.49/1.01      ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_427]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1506,plain,
% 2.49/1.01      ( v2_tex_2(sK5,sK3) != iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.49/1.01  
% 2.49/1.01  
% 2.49/1.01  % SZS output end Saturation for theBenchmark.p
% 2.49/1.01  
% 2.49/1.01  ------                               Statistics
% 2.49/1.01  
% 2.49/1.01  ------ General
% 2.49/1.01  
% 2.49/1.01  abstr_ref_over_cycles:                  0
% 2.49/1.01  abstr_ref_under_cycles:                 0
% 2.49/1.01  gc_basic_clause_elim:                   0
% 2.49/1.01  forced_gc_time:                         0
% 2.49/1.01  parsing_time:                           0.01
% 2.49/1.01  unif_index_cands_time:                  0.
% 2.49/1.01  unif_index_add_time:                    0.
% 2.49/1.01  orderings_time:                         0.
% 2.49/1.01  out_proof_time:                         0.
% 2.49/1.01  total_time:                             0.161
% 2.49/1.01  num_of_symbols:                         48
% 2.49/1.01  num_of_terms:                           3775
% 2.49/1.01  
% 2.49/1.01  ------ Preprocessing
% 2.49/1.01  
% 2.49/1.01  num_of_splits:                          0
% 2.49/1.01  num_of_split_atoms:                     0
% 2.49/1.01  num_of_reused_defs:                     0
% 2.49/1.01  num_eq_ax_congr_red:                    12
% 2.49/1.01  num_of_sem_filtered_clauses:            1
% 2.49/1.01  num_of_subtypes:                        0
% 2.49/1.01  monotx_restored_types:                  0
% 2.49/1.01  sat_num_of_epr_types:                   0
% 2.49/1.01  sat_num_of_non_cyclic_types:            0
% 2.49/1.01  sat_guarded_non_collapsed_types:        0
% 2.49/1.01  num_pure_diseq_elim:                    0
% 2.49/1.01  simp_replaced_by:                       0
% 2.49/1.01  res_preprocessed:                       84
% 2.49/1.01  prep_upred:                             0
% 2.49/1.01  prep_unflattend:                        54
% 2.49/1.01  smt_new_axioms:                         0
% 2.49/1.01  pred_elim_cands:                        6
% 2.49/1.01  pred_elim:                              3
% 2.49/1.01  pred_elim_cl:                           -1
% 2.49/1.01  pred_elim_cycles:                       7
% 2.49/1.01  merged_defs:                            0
% 2.49/1.01  merged_defs_ncl:                        0
% 2.49/1.01  bin_hyper_res:                          0
% 2.49/1.01  prep_cycles:                            3
% 2.49/1.01  pred_elim_time:                         0.022
% 2.49/1.01  splitting_time:                         0.
% 2.49/1.01  sem_filter_time:                        0.
% 2.49/1.01  monotx_time:                            0.001
% 2.49/1.01  subtype_inf_time:                       0.
% 2.49/1.01  
% 2.49/1.01  ------ Problem properties
% 2.49/1.01  
% 2.49/1.01  clauses:                                20
% 2.49/1.01  conjectures:                            6
% 2.49/1.01  epr:                                    3
% 2.49/1.01  horn:                                   12
% 2.49/1.01  ground:                                 8
% 2.49/1.01  unary:                                  8
% 2.49/1.01  binary:                                 0
% 2.49/1.01  lits:                                   66
% 2.49/1.01  lits_eq:                                10
% 2.49/1.01  fd_pure:                                0
% 2.49/1.01  fd_pseudo:                              0
% 2.49/1.01  fd_cond:                                0
% 2.49/1.01  fd_pseudo_cond:                         2
% 2.49/1.01  ac_symbols:                             0
% 2.49/1.01  
% 2.49/1.01  ------ Propositional Solver
% 2.49/1.01  
% 2.49/1.01  prop_solver_calls:                      24
% 2.49/1.01  prop_fast_solver_calls:                 993
% 2.49/1.01  smt_solver_calls:                       0
% 2.49/1.01  smt_fast_solver_calls:                  0
% 2.49/1.01  prop_num_of_clauses:                    1214
% 2.49/1.01  prop_preprocess_simplified:             3660
% 2.49/1.01  prop_fo_subsumed:                       18
% 2.49/1.01  prop_solver_time:                       0.
% 2.49/1.01  smt_solver_time:                        0.
% 2.49/1.01  smt_fast_solver_time:                   0.
% 2.49/1.01  prop_fast_solver_time:                  0.
% 2.49/1.01  prop_unsat_core_time:                   0.
% 2.49/1.01  
% 2.49/1.01  ------ QBF
% 2.49/1.01  
% 2.49/1.01  qbf_q_res:                              0
% 2.49/1.01  qbf_num_tautologies:                    0
% 2.49/1.01  qbf_prep_cycles:                        0
% 2.49/1.01  
% 2.49/1.01  ------ BMC1
% 2.49/1.01  
% 2.49/1.01  bmc1_current_bound:                     -1
% 2.49/1.01  bmc1_last_solved_bound:                 -1
% 2.49/1.01  bmc1_unsat_core_size:                   -1
% 2.49/1.01  bmc1_unsat_core_parents_size:           -1
% 2.49/1.01  bmc1_merge_next_fun:                    0
% 2.49/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.49/1.01  
% 2.49/1.01  ------ Instantiation
% 2.49/1.01  
% 2.49/1.01  inst_num_of_clauses:                    370
% 2.49/1.01  inst_num_in_passive:                    50
% 2.49/1.01  inst_num_in_active:                     235
% 2.49/1.01  inst_num_in_unprocessed:                85
% 2.49/1.01  inst_num_of_loops:                      250
% 2.49/1.01  inst_num_of_learning_restarts:          0
% 2.49/1.01  inst_num_moves_active_passive:          10
% 2.49/1.01  inst_lit_activity:                      0
% 2.49/1.01  inst_lit_activity_moves:                0
% 2.49/1.01  inst_num_tautologies:                   0
% 2.49/1.01  inst_num_prop_implied:                  0
% 2.49/1.01  inst_num_existing_simplified:           0
% 2.49/1.01  inst_num_eq_res_simplified:             0
% 2.49/1.01  inst_num_child_elim:                    0
% 2.49/1.01  inst_num_of_dismatching_blockings:      140
% 2.49/1.01  inst_num_of_non_proper_insts:           559
% 2.49/1.01  inst_num_of_duplicates:                 0
% 2.49/1.01  inst_inst_num_from_inst_to_res:         0
% 2.49/1.01  inst_dismatching_checking_time:         0.
% 2.49/1.01  
% 2.49/1.01  ------ Resolution
% 2.49/1.01  
% 2.49/1.01  res_num_of_clauses:                     0
% 2.49/1.01  res_num_in_passive:                     0
% 2.49/1.01  res_num_in_active:                      0
% 2.49/1.01  res_num_of_loops:                       87
% 2.49/1.01  res_forward_subset_subsumed:            115
% 2.49/1.01  res_backward_subset_subsumed:           6
% 2.49/1.01  res_forward_subsumed:                   0
% 2.49/1.01  res_backward_subsumed:                  0
% 2.49/1.01  res_forward_subsumption_resolution:     0
% 2.49/1.01  res_backward_subsumption_resolution:    0
% 2.49/1.01  res_clause_to_clause_subsumption:       268
% 2.49/1.01  res_orphan_elimination:                 0
% 2.49/1.01  res_tautology_del:                      66
% 2.49/1.01  res_num_eq_res_simplified:              0
% 2.49/1.01  res_num_sel_changes:                    0
% 2.49/1.01  res_moves_from_active_to_pass:          0
% 2.49/1.01  
% 2.49/1.01  ------ Superposition
% 2.49/1.01  
% 2.49/1.01  sup_time_total:                         0.
% 2.49/1.01  sup_time_generating:                    0.
% 2.49/1.01  sup_time_sim_full:                      0.
% 2.49/1.01  sup_time_sim_immed:                     0.
% 2.49/1.01  
% 2.49/1.01  sup_num_of_clauses:                     45
% 2.49/1.01  sup_num_in_active:                      41
% 2.49/1.01  sup_num_in_passive:                     4
% 2.49/1.01  sup_num_of_loops:                       48
% 2.49/1.01  sup_fw_superposition:                   27
% 2.49/1.01  sup_bw_superposition:                   6
% 2.49/1.01  sup_immediate_simplified:               5
% 2.49/1.01  sup_given_eliminated:                   2
% 2.49/1.01  comparisons_done:                       0
% 2.49/1.01  comparisons_avoided:                    0
% 2.49/1.01  
% 2.49/1.01  ------ Simplifications
% 2.49/1.01  
% 2.49/1.01  
% 2.49/1.01  sim_fw_subset_subsumed:                 5
% 2.49/1.01  sim_bw_subset_subsumed:                 2
% 2.49/1.01  sim_fw_subsumed:                        0
% 2.49/1.01  sim_bw_subsumed:                        0
% 2.49/1.01  sim_fw_subsumption_res:                 3
% 2.49/1.01  sim_bw_subsumption_res:                 0
% 2.49/1.01  sim_tautology_del:                      0
% 2.49/1.01  sim_eq_tautology_del:                   7
% 2.49/1.01  sim_eq_res_simp:                        0
% 2.49/1.01  sim_fw_demodulated:                     0
% 2.49/1.01  sim_bw_demodulated:                     7
% 2.49/1.01  sim_light_normalised:                   10
% 2.49/1.01  sim_joinable_taut:                      0
% 2.49/1.01  sim_joinable_simp:                      0
% 2.49/1.01  sim_ac_normalised:                      0
% 2.49/1.01  sim_smt_subsumption:                    0
% 2.49/1.01  
%------------------------------------------------------------------------------
