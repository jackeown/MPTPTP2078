%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:43 EST 2020

% Result     : CounterSatisfiable 2.47s
% Output     : Saturation 2.47s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_5456)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> ( m1_pre_topc(X2,X0)
                    & v1_tsep_1(X2,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( l1_pre_topc(X2)
                  & v2_pre_topc(X2) )
               => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
                 => ( ( m1_pre_topc(X1,X0)
                      & v1_tsep_1(X1,X0) )
                  <=> ( m1_pre_topc(X2,X0)
                      & v1_tsep_1(X2,X0) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <~> ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <~> ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,X0)
                | ~ v1_tsep_1(X2,X0)
                | ~ m1_pre_topc(X1,X0)
                | ~ v1_tsep_1(X1,X0) )
              & ( ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0) )
                | ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,X0)
                | ~ v1_tsep_1(X2,X0)
                | ~ m1_pre_topc(X1,X0)
                | ~ v1_tsep_1(X1,X0) )
              & ( ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0) )
                | ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ m1_pre_topc(X2,X0)
            | ~ v1_tsep_1(X2,X0)
            | ~ m1_pre_topc(X1,X0)
            | ~ v1_tsep_1(X1,X0) )
          & ( ( m1_pre_topc(X2,X0)
              & v1_tsep_1(X2,X0) )
            | ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) ) )
          & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
          & l1_pre_topc(X2)
          & v2_pre_topc(X2) )
     => ( ( ~ m1_pre_topc(sK2,X0)
          | ~ v1_tsep_1(sK2,X0)
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
        & ( ( m1_pre_topc(sK2,X0)
            & v1_tsep_1(sK2,X0) )
          | ( m1_pre_topc(X1,X0)
            & v1_tsep_1(X1,X0) ) )
        & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = sK2
        & l1_pre_topc(sK2)
        & v2_pre_topc(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,X0)
                | ~ v1_tsep_1(X2,X0)
                | ~ m1_pre_topc(X1,X0)
                | ~ v1_tsep_1(X1,X0) )
              & ( ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0) )
                | ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
     => ( ? [X2] :
            ( ( ~ m1_pre_topc(X2,X0)
              | ~ v1_tsep_1(X2,X0)
              | ~ m1_pre_topc(sK1,X0)
              | ~ v1_tsep_1(sK1,X0) )
            & ( ( m1_pre_topc(X2,X0)
                & v1_tsep_1(X2,X0) )
              | ( m1_pre_topc(sK1,X0)
                & v1_tsep_1(sK1,X0) ) )
            & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = X2
            & l1_pre_topc(X2)
            & v2_pre_topc(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_pre_topc(X2,X0)
                  | ~ v1_tsep_1(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) )
                & ( ( m1_pre_topc(X2,X0)
                    & v1_tsep_1(X2,X0) )
                  | ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) ) )
                & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
                & l1_pre_topc(X2)
                & v2_pre_topc(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,sK0)
                | ~ v1_tsep_1(X2,sK0)
                | ~ m1_pre_topc(X1,sK0)
                | ~ v1_tsep_1(X1,sK0) )
              & ( ( m1_pre_topc(X2,sK0)
                  & v1_tsep_1(X2,sK0) )
                | ( m1_pre_topc(X1,sK0)
                  & v1_tsep_1(X1,sK0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ( ~ m1_pre_topc(sK2,sK0)
      | ~ v1_tsep_1(sK2,sK0)
      | ~ m1_pre_topc(sK1,sK0)
      | ~ v1_tsep_1(sK1,sK0) )
    & ( ( m1_pre_topc(sK2,sK0)
        & v1_tsep_1(sK2,sK0) )
      | ( m1_pre_topc(sK1,sK0)
        & v1_tsep_1(sK1,sK0) ) )
    & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f29,f28,f27])).

fof(f48,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2 ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f33,plain,(
    ! [X0] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f44,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f45,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f47,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f31,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( l1_pre_topc(X2)
             => ! [X3] :
                  ( l1_pre_topc(X3)
                 => ( ( m1_pre_topc(X2,X0)
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                      & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                   => m1_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( m1_pre_topc(X3,X1)
                  | ~ m1_pre_topc(X2,X0)
                  | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ l1_pre_topc(X3) )
              | ~ l1_pre_topc(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( m1_pre_topc(X3,X1)
                  | ~ m1_pre_topc(X2,X0)
                  | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ l1_pre_topc(X3) )
              | ~ l1_pre_topc(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_pre_topc(X3,X1)
      | ~ m1_pre_topc(X2,X0)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | ~ l1_pre_topc(X3)
      | ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f52,plain,
    ( m1_pre_topc(sK2,sK0)
    | m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f43,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f34,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f53,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ v1_tsep_1(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v1_tsep_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f51,plain,
    ( m1_pre_topc(sK2,sK0)
    | v1_tsep_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f50,plain,
    ( v1_tsep_1(sK2,sK0)
    | m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f49,plain,
    ( v1_tsep_1(sK2,sK0)
    | v1_tsep_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f46,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f42,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_218,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_600,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_16,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_3,plain,
    ( ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_994,plain,
    ( v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1641,plain,
    ( v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_994])).

cnf(c_20,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_25,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_26,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1714,plain,
    ( v1_pre_topc(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1641,c_25,c_26])).

cnf(c_17,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_984,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_997,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1452,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK2
    | v1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_984,c_997])).

cnf(c_1719,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_1714,c_1452])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_992,plain,
    ( X0 = X1
    | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1778,plain,
    ( g1_pre_topc(X0,X1) != sK2
    | u1_struct_0(sK1) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_992])).

cnf(c_1,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1669,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1674,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1669])).

cnf(c_1779,plain,
    ( g1_pre_topc(X0,X1) != sK2
    | u1_struct_0(sK1) = X0
    | m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_992])).

cnf(c_1867,plain,
    ( u1_struct_0(sK1) = X0
    | g1_pre_topc(X0,X1) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1778,c_26,c_1674,c_1779])).

cnf(c_1868,plain,
    ( g1_pre_topc(X0,X1) != sK2
    | u1_struct_0(sK1) = X0 ),
    inference(renaming,[status(thm)],[c_1867])).

cnf(c_1876,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_1719,c_1868])).

cnf(c_1981,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK1)) = sK2 ),
    inference(demodulation,[status(thm)],[c_1876,c_16])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X0
    | g1_pre_topc(X3,X2) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_993,plain,
    ( X0 = X1
    | g1_pre_topc(X2,X0) != g1_pre_topc(X3,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2319,plain,
    ( g1_pre_topc(X0,X1) != sK2
    | u1_pre_topc(sK2) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1719,c_993])).

cnf(c_2526,plain,
    ( u1_pre_topc(sK2) = u1_pre_topc(sK1)
    | m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1981,c_2319])).

cnf(c_996,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1992,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1876,c_996])).

cnf(c_2533,plain,
    ( u1_pre_topc(sK2) = u1_pre_topc(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2526,c_26,c_1992])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X3)
    | g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_991,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
    | m1_pre_topc(X3,X1) != iProver_top
    | m1_pre_topc(X2,X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(X3) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2221,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != sK2
    | m1_pre_topc(X0,X2) = iProver_top
    | m1_pre_topc(X1,sK2) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1719,c_991])).

cnf(c_28,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3710,plain,
    ( l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | m1_pre_topc(X1,sK2) != iProver_top
    | m1_pre_topc(X0,X2) = iProver_top
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != sK2
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2221,c_28])).

cnf(c_3711,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != sK2
    | m1_pre_topc(X0,X2) = iProver_top
    | m1_pre_topc(X1,sK2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3710])).

cnf(c_3728,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(sK1,sK2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2533,c_3711])).

cnf(c_3747,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(sK1,sK2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3728,c_1719,c_1876])).

cnf(c_2222,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK1))
    | m1_pre_topc(X0,X2) = iProver_top
    | m1_pre_topc(X1,sK1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1876,c_991])).

cnf(c_2244,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != sK2
    | m1_pre_topc(X1,X2) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2222,c_1981])).

cnf(c_2616,plain,
    ( l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(X1,X2) = iProver_top
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != sK2
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2244,c_26])).

cnf(c_2617,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != sK2
    | m1_pre_topc(X1,X2) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2616])).

cnf(c_2629,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1719,c_2617])).

cnf(c_2220,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK1))
    | m1_pre_topc(X1,X2) != iProver_top
    | m1_pre_topc(X0,sK1) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1876,c_991])).

cnf(c_2277,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != sK2
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_pre_topc(X1,sK1) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2220,c_1981])).

cnf(c_2790,plain,
    ( l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | m1_pre_topc(X1,sK1) = iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != sK2
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2277,c_26])).

cnf(c_2791,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != sK2
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_pre_topc(X1,sK1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2790])).

cnf(c_2805,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | m1_pre_topc(X0,sK1) = iProver_top
    | m1_pre_topc(sK1,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2533,c_2791])).

cnf(c_2864,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | m1_pre_topc(X0,sK1) = iProver_top
    | m1_pre_topc(sK1,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2805,c_1719,c_1876])).

cnf(c_5133,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | m1_pre_topc(sK1,X1) != iProver_top
    | m1_pre_topc(X0,sK1) = iProver_top
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2864,c_26])).

cnf(c_5134,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | m1_pre_topc(X0,sK1) = iProver_top
    | m1_pre_topc(sK1,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5133])).

cnf(c_5145,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | m1_pre_topc(sK1,X0) != iProver_top
    | m1_pre_topc(sK2,sK1) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1719,c_5134])).

cnf(c_2806,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(sK2,sK1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1719,c_2791])).

cnf(c_4815,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | m1_pre_topc(sK2,sK1) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2806,c_28])).

cnf(c_4816,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(sK2,sK1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4815])).

cnf(c_4829,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) != sK2
    | m1_pre_topc(sK1,X0) != iProver_top
    | m1_pre_topc(sK2,sK1) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2533,c_4816])).

cnf(c_4836,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | sK2 != sK2
    | m1_pre_topc(sK1,X0) != iProver_top
    | m1_pre_topc(sK2,sK1) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4829,c_1719,c_1876])).

cnf(c_4837,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | m1_pre_topc(sK1,X0) != iProver_top
    | m1_pre_topc(sK2,sK1) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4836])).

cnf(c_5288,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_pre_topc(sK2,sK1) = iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5145,c_26,c_4837])).

cnf(c_5289,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | m1_pre_topc(sK1,X0) != iProver_top
    | m1_pre_topc(sK2,sK1) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5288])).

cnf(c_5298,plain,
    ( m1_pre_topc(sK1,sK2) != iProver_top
    | m1_pre_topc(sK2,sK1) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1719,c_5289])).

cnf(c_5309,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top
    | m1_pre_topc(sK1,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5298,c_28])).

cnf(c_5310,plain,
    ( m1_pre_topc(sK1,sK2) != iProver_top
    | m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(renaming,[status(thm)],[c_5309])).

cnf(c_6273,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | m1_pre_topc(sK1,sK2) != iProver_top
    | m1_pre_topc(X0,X1) = iProver_top
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3747,c_28,c_2629,c_5310])).

cnf(c_6274,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(sK1,sK2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6273])).

cnf(c_6287,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) != sK2
    | m1_pre_topc(sK1,X0) = iProver_top
    | m1_pre_topc(sK1,sK2) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2533,c_6274])).

cnf(c_6294,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | sK2 != sK2
    | m1_pre_topc(sK1,X0) = iProver_top
    | m1_pre_topc(sK1,sK2) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6287,c_1719,c_1876])).

cnf(c_6295,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | m1_pre_topc(sK1,X0) = iProver_top
    | m1_pre_topc(sK1,sK2) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_6294])).

cnf(c_2634,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(sK1,X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2533,c_2617])).

cnf(c_2653,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(sK1,X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2634,c_1719,c_1876])).

cnf(c_4316,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | m1_pre_topc(sK1,X1) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2653,c_26])).

cnf(c_4317,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(sK1,X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4316])).

cnf(c_4326,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | m1_pre_topc(sK1,X0) = iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1719,c_4317])).

cnf(c_4170,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_pre_topc(X0,X1) = iProver_top
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2629,c_28])).

cnf(c_4171,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4170])).

cnf(c_4184,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) != sK2
    | m1_pre_topc(sK1,X0) = iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2533,c_4171])).

cnf(c_4191,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | sK2 != sK2
    | m1_pre_topc(sK1,X0) = iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4184,c_1719,c_1876])).

cnf(c_4192,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | m1_pre_topc(sK1,X0) = iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4191])).

cnf(c_4357,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_pre_topc(sK1,X0) = iProver_top
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4326,c_26,c_4192])).

cnf(c_4358,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | m1_pre_topc(sK1,X0) = iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4357])).

cnf(c_6883,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_pre_topc(sK1,sK2) != iProver_top
    | m1_pre_topc(sK1,X0) = iProver_top
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6295,c_26,c_4192,c_5310])).

cnf(c_6884,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | m1_pre_topc(sK1,X0) = iProver_top
    | m1_pre_topc(sK1,sK2) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6883])).

cnf(c_3723,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(sK2,X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1719,c_3711])).

cnf(c_6071,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | m1_pre_topc(sK2,X1) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3723,c_28,c_2632,c_3492])).

cnf(c_6072,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(sK2,X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6071])).

cnf(c_6081,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | m1_pre_topc(sK2,X0) = iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1719,c_6072])).

cnf(c_6110,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_pre_topc(sK2,X0) = iProver_top
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6081,c_28])).

cnf(c_6111,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | m1_pre_topc(sK2,X0) = iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6110])).

cnf(c_6120,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) != sK2
    | m1_pre_topc(sK2,sK1) = iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2533,c_6111])).

cnf(c_6125,plain,
    ( sK2 != sK2
    | m1_pre_topc(sK2,sK1) = iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6120,c_1719,c_1876])).

cnf(c_6126,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_6125])).

cnf(c_6736,plain,
    ( m1_pre_topc(sK2,sK2) != iProver_top
    | m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6126,c_26])).

cnf(c_6737,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_6736])).

cnf(c_2219,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != sK2
    | m1_pre_topc(X1,X2) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1719,c_991])).

cnf(c_3242,plain,
    ( l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X1,X2) != iProver_top
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != sK2
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2219,c_28])).

cnf(c_3243,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != sK2
    | m1_pre_topc(X1,X2) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3242])).

cnf(c_3255,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(sK2,sK2) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1719,c_3243])).

cnf(c_2808,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(sK1,sK1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2533,c_2791])).

cnf(c_2827,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(sK1,sK1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2808,c_1719,c_1876])).

cnf(c_2631,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(sK1,sK1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2533,c_2617])).

cnf(c_2690,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(sK1,sK1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2631,c_1719,c_1876])).

cnf(c_4550,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | m1_pre_topc(sK1,sK1) != iProver_top
    | m1_pre_topc(X0,X1) = iProver_top
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2690,c_26])).

cnf(c_4551,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(sK1,sK1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4550])).

cnf(c_4562,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | m1_pre_topc(sK1,sK1) != iProver_top
    | m1_pre_topc(sK2,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1719,c_4551])).

cnf(c_2632,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(sK2,X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1719,c_2617])).

cnf(c_4205,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | m1_pre_topc(sK2,X1) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2632,c_28])).

cnf(c_4206,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(sK2,X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4205])).

cnf(c_4217,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) != sK2
    | m1_pre_topc(sK1,sK1) != iProver_top
    | m1_pre_topc(sK2,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2533,c_4206])).

cnf(c_4224,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | sK2 != sK2
    | m1_pre_topc(sK1,sK1) != iProver_top
    | m1_pre_topc(sK2,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4217,c_1719,c_1876])).

cnf(c_4225,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | m1_pre_topc(sK1,sK1) != iProver_top
    | m1_pre_topc(sK2,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4224])).

cnf(c_4678,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_pre_topc(sK2,X0) = iProver_top
    | m1_pre_topc(sK1,sK1) != iProver_top
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4562,c_26,c_4225])).

cnf(c_4679,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | m1_pre_topc(sK1,sK1) != iProver_top
    | m1_pre_topc(sK2,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4678])).

cnf(c_4686,plain,
    ( m1_pre_topc(sK1,sK1) != iProver_top
    | m1_pre_topc(sK2,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1719,c_4679])).

cnf(c_4808,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top
    | m1_pre_topc(sK1,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4686,c_28])).

cnf(c_4809,plain,
    ( m1_pre_topc(sK1,sK1) != iProver_top
    | m1_pre_topc(sK2,sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_4808])).

cnf(c_5434,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | m1_pre_topc(sK2,sK2) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3255,c_28])).

cnf(c_5435,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(sK2,sK2) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5434])).

cnf(c_5446,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | m1_pre_topc(sK2,X0) != iProver_top
    | m1_pre_topc(sK2,sK2) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1719,c_5435])).

cnf(c_5479,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_pre_topc(sK2,sK2) = iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5446,c_28])).

cnf(c_5480,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | m1_pre_topc(sK2,X0) != iProver_top
    | m1_pre_topc(sK2,sK2) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5479])).

cnf(c_5491,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) != sK2
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_pre_topc(sK2,sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2533,c_5480])).

cnf(c_5496,plain,
    ( sK2 != sK2
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_pre_topc(sK2,sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5491,c_1719,c_1876])).

cnf(c_5497,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | m1_pre_topc(sK2,sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5496])).

cnf(c_6668,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5497,c_26])).

cnf(c_6669,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | m1_pre_topc(sK2,sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_6668])).

cnf(c_3725,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(sK1,X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2533,c_3711])).

cnf(c_3784,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(sK1,X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3725,c_1719,c_1876])).

cnf(c_2809,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(X1,sK1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2791])).

cnf(c_3492,plain,
    ( m1_pre_topc(X0,sK1) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1719,c_2809])).

cnf(c_6486,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | m1_pre_topc(sK1,X1) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3784,c_26,c_28,c_2653,c_3492])).

cnf(c_6487,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(sK1,X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6486])).

cnf(c_6496,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | m1_pre_topc(sK1,X0) = iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1719,c_6487])).

cnf(c_3726,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1719,c_3711])).

cnf(c_4962,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | m1_pre_topc(sK1,sK1) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2827,c_26])).

cnf(c_4963,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(sK1,sK1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4962])).

cnf(c_4974,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | m1_pre_topc(sK1,sK1) = iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1719,c_4963])).

cnf(c_2803,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | m1_pre_topc(X0,sK1) = iProver_top
    | m1_pre_topc(sK2,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1719,c_2791])).

cnf(c_4641,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | m1_pre_topc(sK2,X1) != iProver_top
    | m1_pre_topc(X0,sK1) = iProver_top
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2803,c_28])).

cnf(c_4642,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | m1_pre_topc(X0,sK1) = iProver_top
    | m1_pre_topc(sK2,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4641])).

cnf(c_4655,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) != sK2
    | m1_pre_topc(sK1,sK1) = iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2533,c_4642])).

cnf(c_4662,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | sK2 != sK2
    | m1_pre_topc(sK1,sK1) = iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4655,c_1719,c_1876])).

cnf(c_4663,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | m1_pre_topc(sK1,sK1) = iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4662])).

cnf(c_5007,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | m1_pre_topc(sK1,sK1) = iProver_top
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4974,c_26,c_4663])).

cnf(c_5008,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | m1_pre_topc(sK1,sK1) = iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5007])).

cnf(c_5017,plain,
    ( m1_pre_topc(sK1,sK1) = iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1719,c_5008])).

cnf(c_5126,plain,
    ( m1_pre_topc(sK2,sK2) != iProver_top
    | m1_pre_topc(sK1,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5017,c_28])).

cnf(c_5127,plain,
    ( m1_pre_topc(sK1,sK1) = iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5126])).

cnf(c_6243,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_pre_topc(X0,X1) = iProver_top
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3726,c_26,c_28,c_2629,c_6126])).

cnf(c_6244,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6243])).

cnf(c_6257,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) != sK2
    | m1_pre_topc(sK1,X0) = iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2533,c_6244])).

cnf(c_6264,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | sK2 != sK2
    | m1_pre_topc(sK1,X0) = iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6257,c_1719,c_1876])).

cnf(c_6265,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | m1_pre_topc(sK1,X0) = iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_6264])).

cnf(c_6656,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_pre_topc(sK1,X0) = iProver_top
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6496,c_26,c_6265])).

cnf(c_6657,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | m1_pre_topc(sK1,X0) = iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6656])).

cnf(c_6285,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | m1_pre_topc(sK1,sK2) != iProver_top
    | m1_pre_topc(sK2,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1719,c_6274])).

cnf(c_6083,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) != sK2
    | m1_pre_topc(sK1,sK2) != iProver_top
    | m1_pre_topc(sK2,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2533,c_6072])).

cnf(c_6090,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | sK2 != sK2
    | m1_pre_topc(sK1,sK2) != iProver_top
    | m1_pre_topc(sK2,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6083,c_1719,c_1876])).

cnf(c_6091,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | m1_pre_topc(sK1,sK2) != iProver_top
    | m1_pre_topc(sK2,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_6090])).

cnf(c_6474,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_pre_topc(sK2,X0) = iProver_top
    | m1_pre_topc(sK1,sK2) != iProver_top
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6285,c_26,c_6091])).

cnf(c_6475,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | m1_pre_topc(sK1,sK2) != iProver_top
    | m1_pre_topc(sK2,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6474])).

cnf(c_3257,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(sK1,sK2) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2533,c_3243])).

cnf(c_3316,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(sK1,sK2) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3257,c_1719,c_1876])).

cnf(c_5950,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | m1_pre_topc(sK1,sK2) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3316,c_28,c_2806,c_4544])).

cnf(c_5951,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(sK1,sK2) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5950])).

cnf(c_5962,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | m1_pre_topc(sK1,sK2) = iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1719,c_5951])).

cnf(c_3258,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(sK2,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1719,c_3243])).

cnf(c_2635,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | m1_pre_topc(X1,X0) = iProver_top
    | m1_pre_topc(X1,sK1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2617])).

cnf(c_3403,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1719,c_2635])).

cnf(c_5620,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | m1_pre_topc(sK2,X1) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3258,c_28,c_2803,c_3403])).

cnf(c_5621,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(sK2,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5620])).

cnf(c_5634,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) != sK2
    | m1_pre_topc(sK1,sK2) = iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2533,c_5621])).

cnf(c_5641,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | sK2 != sK2
    | m1_pre_topc(sK1,sK2) = iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5634,c_1719,c_1876])).

cnf(c_5642,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | m1_pre_topc(sK1,sK2) = iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5641])).

cnf(c_5979,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | m1_pre_topc(sK1,sK2) = iProver_top
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5962,c_26,c_5642])).

cnf(c_5980,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | m1_pre_topc(sK1,sK2) = iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5979])).

cnf(c_3260,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(sK1,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2533,c_3243])).

cnf(c_3279,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(sK1,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3260,c_1719,c_1876])).

cnf(c_5765,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | m1_pre_topc(sK1,X1) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3279,c_26,c_28,c_2864,c_3403])).

cnf(c_5766,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
    | m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(sK1,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5765])).

cnf(c_5777,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | m1_pre_topc(sK1,X0) != iProver_top
    | m1_pre_topc(sK2,sK2) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1719,c_5766])).

cnf(c_5810,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_pre_topc(sK2,sK2) = iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5777,c_26,c_5456])).

cnf(c_5811,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | m1_pre_topc(sK1,X0) != iProver_top
    | m1_pre_topc(sK2,sK2) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5810])).

cnf(c_4365,plain,
    ( m1_pre_topc(sK1,sK2) = iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1719,c_4358])).

cnf(c_4543,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | m1_pre_topc(sK1,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4365,c_28])).

cnf(c_4544,plain,
    ( m1_pre_topc(sK1,sK2) = iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_4543])).

cnf(c_12,negated_conjecture,
    ( m1_pre_topc(sK1,sK0)
    | m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_988,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top
    | m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2223,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_pre_topc(X1,X2) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_991])).

cnf(c_3160,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))
    | m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(sK1,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2533,c_2223])).

cnf(c_3203,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(sK1,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3160,c_1719,c_1876])).

cnf(c_4001,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | m1_pre_topc(sK1,X1) != iProver_top
    | m1_pre_topc(X0,X1) = iProver_top
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3203,c_26])).

cnf(c_4002,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(sK1,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4001])).

cnf(c_4012,plain,
    ( m1_pre_topc(sK1,X0) != iProver_top
    | m1_pre_topc(sK2,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1719,c_4002])).

cnf(c_3161,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(sK2,X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1719,c_2223])).

cnf(c_3681,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | m1_pre_topc(sK2,X1) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3161,c_28])).

cnf(c_3682,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(sK2,X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3681])).

cnf(c_3694,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) != sK2
    | m1_pre_topc(sK1,X0) != iProver_top
    | m1_pre_topc(sK2,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2533,c_3682])).

cnf(c_3700,plain,
    ( sK2 != sK2
    | m1_pre_topc(sK1,X0) != iProver_top
    | m1_pre_topc(sK2,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3694,c_1719,c_1876])).

cnf(c_3701,plain,
    ( m1_pre_topc(sK1,X0) != iProver_top
    | m1_pre_topc(sK2,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3700])).

cnf(c_4027,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_pre_topc(sK2,X0) = iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4012,c_26,c_3701])).

cnf(c_4028,plain,
    ( m1_pre_topc(sK1,X0) != iProver_top
    | m1_pre_topc(sK2,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4027])).

cnf(c_4036,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_988,c_4028])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_24,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4071,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4036,c_24])).

cnf(c_3163,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(sK1,X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2533,c_2223])).

cnf(c_3171,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(sK1,X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3163,c_1719,c_1876])).

cnf(c_3911,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | m1_pre_topc(sK1,X1) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3171,c_26])).

cnf(c_3912,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(sK1,X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3911])).

cnf(c_3922,plain,
    ( m1_pre_topc(sK1,X0) = iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1719,c_3912])).

cnf(c_3158,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(sK2,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1719,c_2223])).

cnf(c_3587,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | m1_pre_topc(sK2,X1) != iProver_top
    | m1_pre_topc(X0,X1) = iProver_top
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3158,c_28])).

cnf(c_3588,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(sK2,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3587])).

cnf(c_3600,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) != sK2
    | m1_pre_topc(sK1,X0) = iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2533,c_3588])).

cnf(c_3606,plain,
    ( sK2 != sK2
    | m1_pre_topc(sK1,X0) = iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3600,c_1719,c_1876])).

cnf(c_3607,plain,
    ( m1_pre_topc(sK1,X0) = iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3606])).

cnf(c_3937,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | m1_pre_topc(sK1,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3922,c_26,c_3607])).

cnf(c_3938,plain,
    ( m1_pre_topc(sK1,X0) = iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3937])).

cnf(c_4076,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4071,c_3938])).

cnf(c_3940,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3938])).

cnf(c_4079,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4076,c_24,c_3940,c_4036])).

cnf(c_3729,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | m1_pre_topc(X1,X0) = iProver_top
    | m1_pre_topc(X1,sK2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3711])).

cnf(c_3577,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3492,c_28])).

cnf(c_3578,plain,
    ( m1_pre_topc(X0,sK1) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3577])).

cnf(c_3477,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3403,c_28])).

cnf(c_3478,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3477])).

cnf(c_3261,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(X1,sK2) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3243])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_990,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1993,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1876,c_990])).

cnf(c_3010,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1993,c_26])).

cnf(c_3011,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(renaming,[status(thm)],[c_3010])).

cnf(c_3018,plain,
    ( m1_pre_topc(sK1,sK1) != iProver_top
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1876,c_3011])).

cnf(c_2320,plain,
    ( g1_pre_topc(X0,X1) != sK2
    | u1_pre_topc(sK1) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1981,c_993])).

cnf(c_2322,plain,
    ( g1_pre_topc(X0,X1) != sK2
    | u1_pre_topc(sK1) = X1
    | m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1981,c_993])).

cnf(c_2604,plain,
    ( u1_pre_topc(sK1) = X1
    | g1_pre_topc(X0,X1) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2320,c_26,c_1992,c_2322])).

cnf(c_2605,plain,
    ( g1_pre_topc(X0,X1) != sK2
    | u1_pre_topc(sK1) = X1 ),
    inference(renaming,[status(thm)],[c_2604])).

cnf(c_2607,plain,
    ( g1_pre_topc(X0,X1) != sK2
    | u1_pre_topc(sK2) = X1 ),
    inference(demodulation,[status(thm)],[c_2605,c_2533])).

cnf(c_2103,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1992,c_26])).

cnf(c_2536,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2533,c_2103])).

cnf(c_1990,plain,
    ( m1_pre_topc(sK1,X0) != iProver_top
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1876,c_990])).

cnf(c_1980,plain,
    ( g1_pre_topc(X0,X1) != sK2
    | u1_struct_0(sK2) = X0 ),
    inference(demodulation,[status(thm)],[c_1876,c_1868])).

cnf(c_982,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1453,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK1
    | v1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_982,c_997])).

cnf(c_1461,plain,
    ( sK1 = sK2
    | v1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1453,c_16])).

cnf(c_980,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1454,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = sK0
    | v1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_980,c_997])).

cnf(c_2,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_995,plain,
    ( v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_11,negated_conjecture,
    ( ~ v1_tsep_1(sK1,sK0)
    | ~ v1_tsep_1(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_989,plain,
    ( v1_tsep_1(sK1,sK0) != iProver_top
    | v1_tsep_1(sK2,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_13,negated_conjecture,
    ( v1_tsep_1(sK1,sK0)
    | m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_987,plain,
    ( v1_tsep_1(sK1,sK0) = iProver_top
    | m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_14,negated_conjecture,
    ( v1_tsep_1(sK2,sK0)
    | m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_986,plain,
    ( v1_tsep_1(sK2,sK0) = iProver_top
    | m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_15,negated_conjecture,
    ( v1_tsep_1(sK1,sK0)
    | v1_tsep_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_985,plain,
    ( v1_tsep_1(sK1,sK0) = iProver_top
    | v1_tsep_1(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_18,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_983,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_981,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_22,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_979,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:10:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.47/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.00  
% 2.47/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.47/1.00  
% 2.47/1.00  ------  iProver source info
% 2.47/1.00  
% 2.47/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.47/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.47/1.00  git: non_committed_changes: false
% 2.47/1.00  git: last_make_outside_of_git: false
% 2.47/1.00  
% 2.47/1.00  ------ 
% 2.47/1.00  
% 2.47/1.00  ------ Input Options
% 2.47/1.00  
% 2.47/1.00  --out_options                           all
% 2.47/1.00  --tptp_safe_out                         true
% 2.47/1.00  --problem_path                          ""
% 2.47/1.00  --include_path                          ""
% 2.47/1.00  --clausifier                            res/vclausify_rel
% 2.47/1.00  --clausifier_options                    --mode clausify
% 2.47/1.00  --stdin                                 false
% 2.47/1.00  --stats_out                             all
% 2.47/1.00  
% 2.47/1.00  ------ General Options
% 2.47/1.00  
% 2.47/1.00  --fof                                   false
% 2.47/1.00  --time_out_real                         305.
% 2.47/1.00  --time_out_virtual                      -1.
% 2.47/1.00  --symbol_type_check                     false
% 2.47/1.00  --clausify_out                          false
% 2.47/1.00  --sig_cnt_out                           false
% 2.47/1.00  --trig_cnt_out                          false
% 2.47/1.00  --trig_cnt_out_tolerance                1.
% 2.47/1.00  --trig_cnt_out_sk_spl                   false
% 2.47/1.00  --abstr_cl_out                          false
% 2.47/1.00  
% 2.47/1.00  ------ Global Options
% 2.47/1.00  
% 2.47/1.00  --schedule                              default
% 2.47/1.00  --add_important_lit                     false
% 2.47/1.00  --prop_solver_per_cl                    1000
% 2.47/1.00  --min_unsat_core                        false
% 2.47/1.00  --soft_assumptions                      false
% 2.47/1.00  --soft_lemma_size                       3
% 2.47/1.00  --prop_impl_unit_size                   0
% 2.47/1.00  --prop_impl_unit                        []
% 2.47/1.00  --share_sel_clauses                     true
% 2.47/1.00  --reset_solvers                         false
% 2.47/1.00  --bc_imp_inh                            [conj_cone]
% 2.47/1.00  --conj_cone_tolerance                   3.
% 2.47/1.00  --extra_neg_conj                        none
% 2.47/1.00  --large_theory_mode                     true
% 2.47/1.00  --prolific_symb_bound                   200
% 2.47/1.00  --lt_threshold                          2000
% 2.47/1.00  --clause_weak_htbl                      true
% 2.47/1.00  --gc_record_bc_elim                     false
% 2.47/1.00  
% 2.47/1.00  ------ Preprocessing Options
% 2.47/1.00  
% 2.47/1.00  --preprocessing_flag                    true
% 2.47/1.00  --time_out_prep_mult                    0.1
% 2.47/1.00  --splitting_mode                        input
% 2.47/1.00  --splitting_grd                         true
% 2.47/1.00  --splitting_cvd                         false
% 2.47/1.00  --splitting_cvd_svl                     false
% 2.47/1.00  --splitting_nvd                         32
% 2.47/1.00  --sub_typing                            true
% 2.47/1.00  --prep_gs_sim                           true
% 2.47/1.00  --prep_unflatten                        true
% 2.47/1.00  --prep_res_sim                          true
% 2.47/1.00  --prep_upred                            true
% 2.47/1.00  --prep_sem_filter                       exhaustive
% 2.47/1.00  --prep_sem_filter_out                   false
% 2.47/1.00  --pred_elim                             true
% 2.47/1.00  --res_sim_input                         true
% 2.47/1.00  --eq_ax_congr_red                       true
% 2.47/1.00  --pure_diseq_elim                       true
% 2.47/1.00  --brand_transform                       false
% 2.47/1.00  --non_eq_to_eq                          false
% 2.47/1.00  --prep_def_merge                        true
% 2.47/1.00  --prep_def_merge_prop_impl              false
% 2.47/1.00  --prep_def_merge_mbd                    true
% 2.47/1.00  --prep_def_merge_tr_red                 false
% 2.47/1.00  --prep_def_merge_tr_cl                  false
% 2.47/1.00  --smt_preprocessing                     true
% 2.47/1.00  --smt_ac_axioms                         fast
% 2.47/1.00  --preprocessed_out                      false
% 2.47/1.00  --preprocessed_stats                    false
% 2.47/1.00  
% 2.47/1.00  ------ Abstraction refinement Options
% 2.47/1.00  
% 2.47/1.00  --abstr_ref                             []
% 2.47/1.00  --abstr_ref_prep                        false
% 2.47/1.00  --abstr_ref_until_sat                   false
% 2.47/1.00  --abstr_ref_sig_restrict                funpre
% 2.47/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.47/1.00  --abstr_ref_under                       []
% 2.47/1.00  
% 2.47/1.00  ------ SAT Options
% 2.47/1.00  
% 2.47/1.00  --sat_mode                              false
% 2.47/1.00  --sat_fm_restart_options                ""
% 2.47/1.00  --sat_gr_def                            false
% 2.47/1.00  --sat_epr_types                         true
% 2.47/1.00  --sat_non_cyclic_types                  false
% 2.47/1.00  --sat_finite_models                     false
% 2.47/1.00  --sat_fm_lemmas                         false
% 2.47/1.00  --sat_fm_prep                           false
% 2.47/1.00  --sat_fm_uc_incr                        true
% 2.47/1.00  --sat_out_model                         small
% 2.47/1.00  --sat_out_clauses                       false
% 2.47/1.00  
% 2.47/1.00  ------ QBF Options
% 2.47/1.00  
% 2.47/1.00  --qbf_mode                              false
% 2.47/1.00  --qbf_elim_univ                         false
% 2.47/1.00  --qbf_dom_inst                          none
% 2.47/1.00  --qbf_dom_pre_inst                      false
% 2.47/1.00  --qbf_sk_in                             false
% 2.47/1.00  --qbf_pred_elim                         true
% 2.47/1.00  --qbf_split                             512
% 2.47/1.00  
% 2.47/1.00  ------ BMC1 Options
% 2.47/1.00  
% 2.47/1.00  --bmc1_incremental                      false
% 2.47/1.00  --bmc1_axioms                           reachable_all
% 2.47/1.00  --bmc1_min_bound                        0
% 2.47/1.00  --bmc1_max_bound                        -1
% 2.47/1.00  --bmc1_max_bound_default                -1
% 2.47/1.00  --bmc1_symbol_reachability              true
% 2.47/1.00  --bmc1_property_lemmas                  false
% 2.47/1.00  --bmc1_k_induction                      false
% 2.47/1.00  --bmc1_non_equiv_states                 false
% 2.47/1.00  --bmc1_deadlock                         false
% 2.47/1.00  --bmc1_ucm                              false
% 2.47/1.00  --bmc1_add_unsat_core                   none
% 2.47/1.00  --bmc1_unsat_core_children              false
% 2.47/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.47/1.00  --bmc1_out_stat                         full
% 2.47/1.00  --bmc1_ground_init                      false
% 2.47/1.00  --bmc1_pre_inst_next_state              false
% 2.47/1.00  --bmc1_pre_inst_state                   false
% 2.47/1.00  --bmc1_pre_inst_reach_state             false
% 2.47/1.00  --bmc1_out_unsat_core                   false
% 2.47/1.00  --bmc1_aig_witness_out                  false
% 2.47/1.00  --bmc1_verbose                          false
% 2.47/1.00  --bmc1_dump_clauses_tptp                false
% 2.47/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.47/1.00  --bmc1_dump_file                        -
% 2.47/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.47/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.47/1.00  --bmc1_ucm_extend_mode                  1
% 2.47/1.00  --bmc1_ucm_init_mode                    2
% 2.47/1.00  --bmc1_ucm_cone_mode                    none
% 2.47/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.47/1.00  --bmc1_ucm_relax_model                  4
% 2.47/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.47/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.47/1.00  --bmc1_ucm_layered_model                none
% 2.47/1.00  --bmc1_ucm_max_lemma_size               10
% 2.47/1.00  
% 2.47/1.00  ------ AIG Options
% 2.47/1.00  
% 2.47/1.00  --aig_mode                              false
% 2.47/1.00  
% 2.47/1.00  ------ Instantiation Options
% 2.47/1.00  
% 2.47/1.00  --instantiation_flag                    true
% 2.47/1.00  --inst_sos_flag                         false
% 2.47/1.00  --inst_sos_phase                        true
% 2.47/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.47/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.47/1.00  --inst_lit_sel_side                     num_symb
% 2.47/1.00  --inst_solver_per_active                1400
% 2.47/1.00  --inst_solver_calls_frac                1.
% 2.47/1.00  --inst_passive_queue_type               priority_queues
% 2.47/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.47/1.00  --inst_passive_queues_freq              [25;2]
% 2.47/1.00  --inst_dismatching                      true
% 2.47/1.00  --inst_eager_unprocessed_to_passive     true
% 2.47/1.00  --inst_prop_sim_given                   true
% 2.47/1.00  --inst_prop_sim_new                     false
% 2.47/1.00  --inst_subs_new                         false
% 2.47/1.00  --inst_eq_res_simp                      false
% 2.47/1.00  --inst_subs_given                       false
% 2.47/1.00  --inst_orphan_elimination               true
% 2.47/1.00  --inst_learning_loop_flag               true
% 2.47/1.00  --inst_learning_start                   3000
% 2.47/1.00  --inst_learning_factor                  2
% 2.47/1.00  --inst_start_prop_sim_after_learn       3
% 2.47/1.00  --inst_sel_renew                        solver
% 2.47/1.00  --inst_lit_activity_flag                true
% 2.47/1.00  --inst_restr_to_given                   false
% 2.47/1.00  --inst_activity_threshold               500
% 2.47/1.00  --inst_out_proof                        true
% 2.47/1.00  
% 2.47/1.00  ------ Resolution Options
% 2.47/1.00  
% 2.47/1.00  --resolution_flag                       true
% 2.47/1.00  --res_lit_sel                           adaptive
% 2.47/1.00  --res_lit_sel_side                      none
% 2.47/1.00  --res_ordering                          kbo
% 2.47/1.00  --res_to_prop_solver                    active
% 2.47/1.00  --res_prop_simpl_new                    false
% 2.47/1.00  --res_prop_simpl_given                  true
% 2.47/1.00  --res_passive_queue_type                priority_queues
% 2.47/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.47/1.00  --res_passive_queues_freq               [15;5]
% 2.47/1.00  --res_forward_subs                      full
% 2.47/1.00  --res_backward_subs                     full
% 2.47/1.00  --res_forward_subs_resolution           true
% 2.47/1.00  --res_backward_subs_resolution          true
% 2.47/1.00  --res_orphan_elimination                true
% 2.47/1.00  --res_time_limit                        2.
% 2.47/1.00  --res_out_proof                         true
% 2.47/1.00  
% 2.47/1.00  ------ Superposition Options
% 2.47/1.00  
% 2.47/1.00  --superposition_flag                    true
% 2.47/1.00  --sup_passive_queue_type                priority_queues
% 2.47/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.47/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.47/1.00  --demod_completeness_check              fast
% 2.47/1.00  --demod_use_ground                      true
% 2.47/1.00  --sup_to_prop_solver                    passive
% 2.47/1.00  --sup_prop_simpl_new                    true
% 2.47/1.00  --sup_prop_simpl_given                  true
% 2.47/1.00  --sup_fun_splitting                     false
% 2.47/1.00  --sup_smt_interval                      50000
% 2.47/1.00  
% 2.47/1.00  ------ Superposition Simplification Setup
% 2.47/1.00  
% 2.47/1.00  --sup_indices_passive                   []
% 2.47/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.47/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/1.00  --sup_full_bw                           [BwDemod]
% 2.47/1.00  --sup_immed_triv                        [TrivRules]
% 2.47/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.47/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/1.00  --sup_immed_bw_main                     []
% 2.47/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.47/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.47/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.47/1.00  
% 2.47/1.00  ------ Combination Options
% 2.47/1.00  
% 2.47/1.00  --comb_res_mult                         3
% 2.47/1.00  --comb_sup_mult                         2
% 2.47/1.00  --comb_inst_mult                        10
% 2.47/1.00  
% 2.47/1.00  ------ Debug Options
% 2.47/1.00  
% 2.47/1.00  --dbg_backtrace                         false
% 2.47/1.00  --dbg_dump_prop_clauses                 false
% 2.47/1.00  --dbg_dump_prop_clauses_file            -
% 2.47/1.00  --dbg_out_stat                          false
% 2.47/1.00  ------ Parsing...
% 2.47/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.47/1.00  
% 2.47/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.47/1.00  
% 2.47/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.47/1.00  
% 2.47/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.47/1.00  ------ Proving...
% 2.47/1.00  ------ Problem Properties 
% 2.47/1.00  
% 2.47/1.00  
% 2.47/1.00  clauses                                 20
% 2.47/1.00  conjectures                             12
% 2.47/1.00  EPR                                     11
% 2.47/1.00  Horn                                    16
% 2.47/1.00  unary                                   7
% 2.47/1.00  binary                                  5
% 2.47/1.00  lits                                    47
% 2.47/1.00  lits eq                                 8
% 2.47/1.00  fd_pure                                 0
% 2.47/1.00  fd_pseudo                               0
% 2.47/1.00  fd_cond                                 0
% 2.47/1.00  fd_pseudo_cond                          2
% 2.47/1.00  AC symbols                              0
% 2.47/1.00  
% 2.47/1.00  ------ Schedule dynamic 5 is on 
% 2.47/1.00  
% 2.47/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.47/1.00  
% 2.47/1.00  
% 2.47/1.00  ------ 
% 2.47/1.00  Current options:
% 2.47/1.00  ------ 
% 2.47/1.00  
% 2.47/1.00  ------ Input Options
% 2.47/1.00  
% 2.47/1.00  --out_options                           all
% 2.47/1.00  --tptp_safe_out                         true
% 2.47/1.00  --problem_path                          ""
% 2.47/1.00  --include_path                          ""
% 2.47/1.00  --clausifier                            res/vclausify_rel
% 2.47/1.00  --clausifier_options                    --mode clausify
% 2.47/1.00  --stdin                                 false
% 2.47/1.00  --stats_out                             all
% 2.47/1.00  
% 2.47/1.00  ------ General Options
% 2.47/1.00  
% 2.47/1.00  --fof                                   false
% 2.47/1.00  --time_out_real                         305.
% 2.47/1.00  --time_out_virtual                      -1.
% 2.47/1.00  --symbol_type_check                     false
% 2.47/1.00  --clausify_out                          false
% 2.47/1.00  --sig_cnt_out                           false
% 2.47/1.00  --trig_cnt_out                          false
% 2.47/1.00  --trig_cnt_out_tolerance                1.
% 2.47/1.00  --trig_cnt_out_sk_spl                   false
% 2.47/1.00  --abstr_cl_out                          false
% 2.47/1.00  
% 2.47/1.00  ------ Global Options
% 2.47/1.00  
% 2.47/1.00  --schedule                              default
% 2.47/1.00  --add_important_lit                     false
% 2.47/1.00  --prop_solver_per_cl                    1000
% 2.47/1.00  --min_unsat_core                        false
% 2.47/1.00  --soft_assumptions                      false
% 2.47/1.00  --soft_lemma_size                       3
% 2.47/1.00  --prop_impl_unit_size                   0
% 2.47/1.00  --prop_impl_unit                        []
% 2.47/1.00  --share_sel_clauses                     true
% 2.47/1.00  --reset_solvers                         false
% 2.47/1.00  --bc_imp_inh                            [conj_cone]
% 2.47/1.00  --conj_cone_tolerance                   3.
% 2.47/1.00  --extra_neg_conj                        none
% 2.47/1.00  --large_theory_mode                     true
% 2.47/1.00  --prolific_symb_bound                   200
% 2.47/1.00  --lt_threshold                          2000
% 2.47/1.00  --clause_weak_htbl                      true
% 2.47/1.00  --gc_record_bc_elim                     false
% 2.47/1.00  
% 2.47/1.00  ------ Preprocessing Options
% 2.47/1.00  
% 2.47/1.00  --preprocessing_flag                    true
% 2.47/1.00  --time_out_prep_mult                    0.1
% 2.47/1.00  --splitting_mode                        input
% 2.47/1.00  --splitting_grd                         true
% 2.47/1.00  --splitting_cvd                         false
% 2.47/1.00  --splitting_cvd_svl                     false
% 2.47/1.00  --splitting_nvd                         32
% 2.47/1.00  --sub_typing                            true
% 2.47/1.00  --prep_gs_sim                           true
% 2.47/1.00  --prep_unflatten                        true
% 2.47/1.00  --prep_res_sim                          true
% 2.47/1.00  --prep_upred                            true
% 2.47/1.00  --prep_sem_filter                       exhaustive
% 2.47/1.00  --prep_sem_filter_out                   false
% 2.47/1.00  --pred_elim                             true
% 2.47/1.00  --res_sim_input                         true
% 2.47/1.00  --eq_ax_congr_red                       true
% 2.47/1.00  --pure_diseq_elim                       true
% 2.47/1.00  --brand_transform                       false
% 2.47/1.00  --non_eq_to_eq                          false
% 2.47/1.00  --prep_def_merge                        true
% 2.47/1.00  --prep_def_merge_prop_impl              false
% 2.47/1.00  --prep_def_merge_mbd                    true
% 2.47/1.00  --prep_def_merge_tr_red                 false
% 2.47/1.00  --prep_def_merge_tr_cl                  false
% 2.47/1.00  --smt_preprocessing                     true
% 2.47/1.00  --smt_ac_axioms                         fast
% 2.47/1.00  --preprocessed_out                      false
% 2.47/1.00  --preprocessed_stats                    false
% 2.47/1.00  
% 2.47/1.00  ------ Abstraction refinement Options
% 2.47/1.00  
% 2.47/1.00  --abstr_ref                             []
% 2.47/1.00  --abstr_ref_prep                        false
% 2.47/1.00  --abstr_ref_until_sat                   false
% 2.47/1.00  --abstr_ref_sig_restrict                funpre
% 2.47/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.47/1.00  --abstr_ref_under                       []
% 2.47/1.00  
% 2.47/1.00  ------ SAT Options
% 2.47/1.00  
% 2.47/1.00  --sat_mode                              false
% 2.47/1.00  --sat_fm_restart_options                ""
% 2.47/1.00  --sat_gr_def                            false
% 2.47/1.00  --sat_epr_types                         true
% 2.47/1.00  --sat_non_cyclic_types                  false
% 2.47/1.00  --sat_finite_models                     false
% 2.47/1.00  --sat_fm_lemmas                         false
% 2.47/1.00  --sat_fm_prep                           false
% 2.47/1.00  --sat_fm_uc_incr                        true
% 2.47/1.00  --sat_out_model                         small
% 2.47/1.00  --sat_out_clauses                       false
% 2.47/1.00  
% 2.47/1.00  ------ QBF Options
% 2.47/1.00  
% 2.47/1.00  --qbf_mode                              false
% 2.47/1.00  --qbf_elim_univ                         false
% 2.47/1.00  --qbf_dom_inst                          none
% 2.47/1.00  --qbf_dom_pre_inst                      false
% 2.47/1.00  --qbf_sk_in                             false
% 2.47/1.00  --qbf_pred_elim                         true
% 2.47/1.00  --qbf_split                             512
% 2.47/1.00  
% 2.47/1.00  ------ BMC1 Options
% 2.47/1.00  
% 2.47/1.00  --bmc1_incremental                      false
% 2.47/1.00  --bmc1_axioms                           reachable_all
% 2.47/1.00  --bmc1_min_bound                        0
% 2.47/1.00  --bmc1_max_bound                        -1
% 2.47/1.00  --bmc1_max_bound_default                -1
% 2.47/1.00  --bmc1_symbol_reachability              true
% 2.47/1.00  --bmc1_property_lemmas                  false
% 2.47/1.00  --bmc1_k_induction                      false
% 2.47/1.00  --bmc1_non_equiv_states                 false
% 2.47/1.00  --bmc1_deadlock                         false
% 2.47/1.00  --bmc1_ucm                              false
% 2.47/1.00  --bmc1_add_unsat_core                   none
% 2.47/1.00  --bmc1_unsat_core_children              false
% 2.47/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.47/1.00  --bmc1_out_stat                         full
% 2.47/1.00  --bmc1_ground_init                      false
% 2.47/1.00  --bmc1_pre_inst_next_state              false
% 2.47/1.00  --bmc1_pre_inst_state                   false
% 2.47/1.00  --bmc1_pre_inst_reach_state             false
% 2.47/1.00  --bmc1_out_unsat_core                   false
% 2.47/1.00  --bmc1_aig_witness_out                  false
% 2.47/1.00  --bmc1_verbose                          false
% 2.47/1.00  --bmc1_dump_clauses_tptp                false
% 2.47/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.47/1.00  --bmc1_dump_file                        -
% 2.47/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.47/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.47/1.00  --bmc1_ucm_extend_mode                  1
% 2.47/1.00  --bmc1_ucm_init_mode                    2
% 2.47/1.00  --bmc1_ucm_cone_mode                    none
% 2.47/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.47/1.00  --bmc1_ucm_relax_model                  4
% 2.47/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.47/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.47/1.00  --bmc1_ucm_layered_model                none
% 2.47/1.00  --bmc1_ucm_max_lemma_size               10
% 2.47/1.00  
% 2.47/1.00  ------ AIG Options
% 2.47/1.00  
% 2.47/1.00  --aig_mode                              false
% 2.47/1.00  
% 2.47/1.00  ------ Instantiation Options
% 2.47/1.00  
% 2.47/1.00  --instantiation_flag                    true
% 2.47/1.00  --inst_sos_flag                         false
% 2.47/1.00  --inst_sos_phase                        true
% 2.47/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.47/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.47/1.00  --inst_lit_sel_side                     none
% 2.47/1.00  --inst_solver_per_active                1400
% 2.47/1.00  --inst_solver_calls_frac                1.
% 2.47/1.00  --inst_passive_queue_type               priority_queues
% 2.47/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.47/1.00  --inst_passive_queues_freq              [25;2]
% 2.47/1.00  --inst_dismatching                      true
% 2.47/1.00  --inst_eager_unprocessed_to_passive     true
% 2.47/1.00  --inst_prop_sim_given                   true
% 2.47/1.00  --inst_prop_sim_new                     false
% 2.47/1.00  --inst_subs_new                         false
% 2.47/1.00  --inst_eq_res_simp                      false
% 2.47/1.00  --inst_subs_given                       false
% 2.47/1.00  --inst_orphan_elimination               true
% 2.47/1.00  --inst_learning_loop_flag               true
% 2.47/1.00  --inst_learning_start                   3000
% 2.47/1.00  --inst_learning_factor                  2
% 2.47/1.00  --inst_start_prop_sim_after_learn       3
% 2.47/1.00  --inst_sel_renew                        solver
% 2.47/1.00  --inst_lit_activity_flag                true
% 2.47/1.00  --inst_restr_to_given                   false
% 2.47/1.00  --inst_activity_threshold               500
% 2.47/1.00  --inst_out_proof                        true
% 2.47/1.00  
% 2.47/1.00  ------ Resolution Options
% 2.47/1.00  
% 2.47/1.00  --resolution_flag                       false
% 2.47/1.00  --res_lit_sel                           adaptive
% 2.47/1.00  --res_lit_sel_side                      none
% 2.47/1.00  --res_ordering                          kbo
% 2.47/1.00  --res_to_prop_solver                    active
% 2.47/1.00  --res_prop_simpl_new                    false
% 2.47/1.00  --res_prop_simpl_given                  true
% 2.47/1.00  --res_passive_queue_type                priority_queues
% 2.47/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.47/1.00  --res_passive_queues_freq               [15;5]
% 2.47/1.00  --res_forward_subs                      full
% 2.47/1.00  --res_backward_subs                     full
% 2.47/1.00  --res_forward_subs_resolution           true
% 2.47/1.00  --res_backward_subs_resolution          true
% 2.47/1.00  --res_orphan_elimination                true
% 2.47/1.00  --res_time_limit                        2.
% 2.47/1.00  --res_out_proof                         true
% 2.47/1.00  
% 2.47/1.00  ------ Superposition Options
% 2.47/1.00  
% 2.47/1.00  --superposition_flag                    true
% 2.47/1.00  --sup_passive_queue_type                priority_queues
% 2.47/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.47/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.47/1.00  --demod_completeness_check              fast
% 2.47/1.00  --demod_use_ground                      true
% 2.47/1.00  --sup_to_prop_solver                    passive
% 2.47/1.00  --sup_prop_simpl_new                    true
% 2.47/1.00  --sup_prop_simpl_given                  true
% 2.47/1.00  --sup_fun_splitting                     false
% 2.47/1.00  --sup_smt_interval                      50000
% 2.47/1.00  
% 2.47/1.00  ------ Superposition Simplification Setup
% 2.47/1.00  
% 2.47/1.00  --sup_indices_passive                   []
% 2.47/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.47/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/1.00  --sup_full_bw                           [BwDemod]
% 2.47/1.00  --sup_immed_triv                        [TrivRules]
% 2.47/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.47/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/1.00  --sup_immed_bw_main                     []
% 2.47/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.47/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.47/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.47/1.00  
% 2.47/1.00  ------ Combination Options
% 2.47/1.00  
% 2.47/1.00  --comb_res_mult                         3
% 2.47/1.00  --comb_sup_mult                         2
% 2.47/1.00  --comb_inst_mult                        10
% 2.47/1.00  
% 2.47/1.00  ------ Debug Options
% 2.47/1.00  
% 2.47/1.00  --dbg_backtrace                         false
% 2.47/1.00  --dbg_dump_prop_clauses                 false
% 2.47/1.00  --dbg_dump_prop_clauses_file            -
% 2.47/1.00  --dbg_out_stat                          false
% 2.47/1.00  
% 2.47/1.00  
% 2.47/1.00  
% 2.47/1.00  
% 2.47/1.00  ------ Proving...
% 2.47/1.00  
% 2.47/1.00  
% 2.47/1.00  % SZS status CounterSatisfiable for theBenchmark.p
% 2.47/1.00  
% 2.47/1.00  % SZS output start Saturation for theBenchmark.p
% 2.47/1.00  
% 2.47/1.00  fof(f8,conjecture,(
% 2.47/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)))))))),
% 2.47/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.47/1.00  
% 2.47/1.00  fof(f9,negated_conjecture,(
% 2.47/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)))))))),
% 2.47/1.00    inference(negated_conjecture,[],[f8])).
% 2.47/1.00  
% 2.47/1.00  fof(f21,plain,(
% 2.47/1.00    ? [X0] : (? [X1] : (? [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2) & (l1_pre_topc(X2) & v2_pre_topc(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.47/1.00    inference(ennf_transformation,[],[f9])).
% 2.47/1.00  
% 2.47/1.00  fof(f22,plain,(
% 2.47/1.00    ? [X0] : (? [X1] : (? [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.47/1.00    inference(flattening,[],[f21])).
% 2.47/1.00  
% 2.47/1.00  fof(f25,plain,(
% 2.47/1.00    ? [X0] : (? [X1] : (? [X2] : ((((~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0)) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) & ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.47/1.00    inference(nnf_transformation,[],[f22])).
% 2.47/1.00  
% 2.47/1.00  fof(f26,plain,(
% 2.47/1.00    ? [X0] : (? [X1] : (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.47/1.00    inference(flattening,[],[f25])).
% 2.47/1.00  
% 2.47/1.00  fof(f29,plain,(
% 2.47/1.00    ( ! [X0,X1] : (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) => ((~m1_pre_topc(sK2,X0) | ~v1_tsep_1(sK2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_pre_topc(sK2,X0) & v1_tsep_1(sK2,X0)) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = sK2 & l1_pre_topc(sK2) & v2_pre_topc(sK2))) )),
% 2.47/1.00    introduced(choice_axiom,[])).
% 2.47/1.00  
% 2.47/1.00  fof(f28,plain,(
% 2.47/1.00    ( ! [X0] : (? [X1] : (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0) | ~m1_pre_topc(sK1,X0) | ~v1_tsep_1(sK1,X0)) & ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)) | (m1_pre_topc(sK1,X0) & v1_tsep_1(sK1,X0))) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))) )),
% 2.47/1.00    introduced(choice_axiom,[])).
% 2.47/1.00  
% 2.47/1.00  fof(f27,plain,(
% 2.47/1.00    ? [X0] : (? [X1] : (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : ((~m1_pre_topc(X2,sK0) | ~v1_tsep_1(X2,sK0) | ~m1_pre_topc(X1,sK0) | ~v1_tsep_1(X1,sK0)) & ((m1_pre_topc(X2,sK0) & v1_tsep_1(X2,sK0)) | (m1_pre_topc(X1,sK0) & v1_tsep_1(X1,sK0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.47/1.00    introduced(choice_axiom,[])).
% 2.47/1.00  
% 2.47/1.00  fof(f30,plain,(
% 2.47/1.00    (((~m1_pre_topc(sK2,sK0) | ~v1_tsep_1(sK2,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_tsep_1(sK1,sK0)) & ((m1_pre_topc(sK2,sK0) & v1_tsep_1(sK2,sK0)) | (m1_pre_topc(sK1,sK0) & v1_tsep_1(sK1,sK0))) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2 & l1_pre_topc(sK2) & v2_pre_topc(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.47/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f29,f28,f27])).
% 2.47/1.00  
% 2.47/1.00  fof(f48,plain,(
% 2.47/1.00    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2),
% 2.47/1.00    inference(cnf_transformation,[],[f30])).
% 2.47/1.00  
% 2.47/1.00  fof(f3,axiom,(
% 2.47/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 2.47/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.47/1.00  
% 2.47/1.00  fof(f13,plain,(
% 2.47/1.00    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.47/1.00    inference(ennf_transformation,[],[f3])).
% 2.47/1.00  
% 2.47/1.00  fof(f14,plain,(
% 2.47/1.00    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.47/1.00    inference(flattening,[],[f13])).
% 2.47/1.00  
% 2.47/1.00  fof(f33,plain,(
% 2.47/1.00    ( ! [X0] : (v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.47/1.00    inference(cnf_transformation,[],[f14])).
% 2.47/1.00  
% 2.47/1.00  fof(f44,plain,(
% 2.47/1.00    v2_pre_topc(sK1)),
% 2.47/1.00    inference(cnf_transformation,[],[f30])).
% 2.47/1.00  
% 2.47/1.00  fof(f45,plain,(
% 2.47/1.00    l1_pre_topc(sK1)),
% 2.47/1.00    inference(cnf_transformation,[],[f30])).
% 2.47/1.00  
% 2.47/1.00  fof(f47,plain,(
% 2.47/1.00    l1_pre_topc(sK2)),
% 2.47/1.00    inference(cnf_transformation,[],[f30])).
% 2.47/1.00  
% 2.47/1.00  fof(f1,axiom,(
% 2.47/1.00    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 2.47/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.47/1.00  
% 2.47/1.00  fof(f10,plain,(
% 2.47/1.00    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 2.47/1.00    inference(ennf_transformation,[],[f1])).
% 2.47/1.00  
% 2.47/1.00  fof(f11,plain,(
% 2.47/1.00    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 2.47/1.00    inference(flattening,[],[f10])).
% 2.47/1.00  
% 2.47/1.00  fof(f31,plain,(
% 2.47/1.00    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 2.47/1.00    inference(cnf_transformation,[],[f11])).
% 2.47/1.00  
% 2.47/1.00  fof(f4,axiom,(
% 2.47/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 2.47/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.47/1.00  
% 2.47/1.00  fof(f15,plain,(
% 2.47/1.00    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.47/1.00    inference(ennf_transformation,[],[f4])).
% 2.47/1.00  
% 2.47/1.00  fof(f35,plain,(
% 2.47/1.00    ( ! [X2,X0,X3,X1] : (X0 = X2 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.47/1.00    inference(cnf_transformation,[],[f15])).
% 2.47/1.00  
% 2.47/1.00  fof(f2,axiom,(
% 2.47/1.00    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.47/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.47/1.00  
% 2.47/1.00  fof(f12,plain,(
% 2.47/1.00    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.47/1.00    inference(ennf_transformation,[],[f2])).
% 2.47/1.00  
% 2.47/1.00  fof(f32,plain,(
% 2.47/1.00    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.47/1.00    inference(cnf_transformation,[],[f12])).
% 2.47/1.00  
% 2.47/1.00  fof(f36,plain,(
% 2.47/1.00    ( ! [X2,X0,X3,X1] : (X1 = X3 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.47/1.00    inference(cnf_transformation,[],[f15])).
% 2.47/1.00  
% 2.47/1.00  fof(f5,axiom,(
% 2.47/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (l1_pre_topc(X2) => ! [X3] : (l1_pre_topc(X3) => ((m1_pre_topc(X2,X0) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => m1_pre_topc(X3,X1))))))),
% 2.47/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.47/1.00  
% 2.47/1.00  fof(f16,plain,(
% 2.47/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_pre_topc(X3,X1) | (~m1_pre_topc(X2,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X3)) | ~l1_pre_topc(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.47/1.00    inference(ennf_transformation,[],[f5])).
% 2.47/1.00  
% 2.47/1.00  fof(f17,plain,(
% 2.47/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (m1_pre_topc(X3,X1) | ~m1_pre_topc(X2,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~l1_pre_topc(X3)) | ~l1_pre_topc(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.47/1.00    inference(flattening,[],[f16])).
% 2.47/1.00  
% 2.47/1.00  fof(f37,plain,(
% 2.47/1.00    ( ! [X2,X0,X3,X1] : (m1_pre_topc(X3,X1) | ~m1_pre_topc(X2,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~l1_pre_topc(X3) | ~l1_pre_topc(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.47/1.00    inference(cnf_transformation,[],[f17])).
% 2.47/1.00  
% 2.47/1.00  fof(f52,plain,(
% 2.47/1.00    m1_pre_topc(sK2,sK0) | m1_pre_topc(sK1,sK0)),
% 2.47/1.00    inference(cnf_transformation,[],[f30])).
% 2.47/1.00  
% 2.47/1.00  fof(f43,plain,(
% 2.47/1.00    l1_pre_topc(sK0)),
% 2.47/1.00    inference(cnf_transformation,[],[f30])).
% 2.47/1.00  
% 2.47/1.00  fof(f7,axiom,(
% 2.47/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.47/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.47/1.00  
% 2.47/1.00  fof(f20,plain,(
% 2.47/1.00    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.47/1.00    inference(ennf_transformation,[],[f7])).
% 2.47/1.00  
% 2.47/1.00  fof(f41,plain,(
% 2.47/1.00    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.47/1.00    inference(cnf_transformation,[],[f20])).
% 2.47/1.00  
% 2.47/1.00  fof(f34,plain,(
% 2.47/1.00    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.47/1.00    inference(cnf_transformation,[],[f14])).
% 2.47/1.00  
% 2.47/1.00  fof(f53,plain,(
% 2.47/1.00    ~m1_pre_topc(sK2,sK0) | ~v1_tsep_1(sK2,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_tsep_1(sK1,sK0)),
% 2.47/1.00    inference(cnf_transformation,[],[f30])).
% 2.47/1.00  
% 2.47/1.00  fof(f51,plain,(
% 2.47/1.00    m1_pre_topc(sK2,sK0) | v1_tsep_1(sK1,sK0)),
% 2.47/1.00    inference(cnf_transformation,[],[f30])).
% 2.47/1.00  
% 2.47/1.00  fof(f50,plain,(
% 2.47/1.00    v1_tsep_1(sK2,sK0) | m1_pre_topc(sK1,sK0)),
% 2.47/1.00    inference(cnf_transformation,[],[f30])).
% 2.47/1.00  
% 2.47/1.00  fof(f49,plain,(
% 2.47/1.00    v1_tsep_1(sK2,sK0) | v1_tsep_1(sK1,sK0)),
% 2.47/1.00    inference(cnf_transformation,[],[f30])).
% 2.47/1.00  
% 2.47/1.00  fof(f46,plain,(
% 2.47/1.00    v2_pre_topc(sK2)),
% 2.47/1.00    inference(cnf_transformation,[],[f30])).
% 2.47/1.00  
% 2.47/1.00  fof(f42,plain,(
% 2.47/1.00    v2_pre_topc(sK0)),
% 2.47/1.00    inference(cnf_transformation,[],[f30])).
% 2.47/1.00  
% 2.47/1.00  cnf(c_218,plain,
% 2.47/1.00      ( ~ v3_pre_topc(X0,X1) | v3_pre_topc(X2,X1) | X2 != X0 ),
% 2.47/1.00      theory(equality) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_600,plain,( X0_2 = X0_2 ),theory(equality) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_16,negated_conjecture,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2 ),
% 2.47/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_3,plain,
% 2.47/1.00      ( ~ v2_pre_topc(X0)
% 2.47/1.00      | ~ l1_pre_topc(X0)
% 2.47/1.00      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 2.47/1.00      inference(cnf_transformation,[],[f33]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_994,plain,
% 2.47/1.00      ( v2_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 2.47/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1641,plain,
% 2.47/1.00      ( v2_pre_topc(sK1) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.47/1.00      | v1_pre_topc(sK2) = iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_16,c_994]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_20,negated_conjecture,
% 2.47/1.00      ( v2_pre_topc(sK1) ),
% 2.47/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_25,plain,
% 2.47/1.00      ( v2_pre_topc(sK1) = iProver_top ),
% 2.47/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_19,negated_conjecture,
% 2.47/1.00      ( l1_pre_topc(sK1) ),
% 2.47/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_26,plain,
% 2.47/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 2.47/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1714,plain,
% 2.47/1.00      ( v1_pre_topc(sK2) = iProver_top ),
% 2.47/1.00      inference(global_propositional_subsumption,
% 2.47/1.00                [status(thm)],
% 2.47/1.00                [c_1641,c_25,c_26]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_17,negated_conjecture,
% 2.47/1.00      ( l1_pre_topc(sK2) ),
% 2.47/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_984,plain,
% 2.47/1.00      ( l1_pre_topc(sK2) = iProver_top ),
% 2.47/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_0,plain,
% 2.47/1.00      ( ~ l1_pre_topc(X0)
% 2.47/1.00      | ~ v1_pre_topc(X0)
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 2.47/1.00      inference(cnf_transformation,[],[f31]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_997,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | v1_pre_topc(X0) != iProver_top ),
% 2.47/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1452,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK2
% 2.47/1.00      | v1_pre_topc(sK2) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_984,c_997]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1719,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK2 ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_1714,c_1452]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_5,plain,
% 2.47/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.47/1.00      | X2 = X1
% 2.47/1.00      | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
% 2.47/1.00      inference(cnf_transformation,[],[f35]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_992,plain,
% 2.47/1.00      ( X0 = X1
% 2.47/1.00      | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
% 2.47/1.00      | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
% 2.47/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1778,plain,
% 2.47/1.00      ( g1_pre_topc(X0,X1) != sK2
% 2.47/1.00      | u1_struct_0(sK1) = X0
% 2.47/1.00      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_16,c_992]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1,plain,
% 2.47/1.00      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.47/1.00      | ~ l1_pre_topc(X0) ),
% 2.47/1.00      inference(cnf_transformation,[],[f32]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1669,plain,
% 2.47/1.00      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 2.47/1.00      | ~ l1_pre_topc(sK1) ),
% 2.47/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1674,plain,
% 2.47/1.00      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(predicate_to_equality,[status(thm)],[c_1669]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1779,plain,
% 2.47/1.00      ( g1_pre_topc(X0,X1) != sK2
% 2.47/1.00      | u1_struct_0(sK1) = X0
% 2.47/1.00      | m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_16,c_992]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1867,plain,
% 2.47/1.00      ( u1_struct_0(sK1) = X0 | g1_pre_topc(X0,X1) != sK2 ),
% 2.47/1.00      inference(global_propositional_subsumption,
% 2.47/1.00                [status(thm)],
% 2.47/1.00                [c_1778,c_26,c_1674,c_1779]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1868,plain,
% 2.47/1.00      ( g1_pre_topc(X0,X1) != sK2 | u1_struct_0(sK1) = X0 ),
% 2.47/1.00      inference(renaming,[status(thm)],[c_1867]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1876,plain,
% 2.47/1.00      ( u1_struct_0(sK2) = u1_struct_0(sK1) ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_1719,c_1868]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1981,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK1)) = sK2 ),
% 2.47/1.00      inference(demodulation,[status(thm)],[c_1876,c_16]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_4,plain,
% 2.47/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.47/1.00      | X2 = X0
% 2.47/1.00      | g1_pre_topc(X3,X2) != g1_pre_topc(X1,X0) ),
% 2.47/1.00      inference(cnf_transformation,[],[f36]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_993,plain,
% 2.47/1.00      ( X0 = X1
% 2.47/1.00      | g1_pre_topc(X2,X0) != g1_pre_topc(X3,X1)
% 2.47/1.00      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) != iProver_top ),
% 2.47/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_2319,plain,
% 2.47/1.00      ( g1_pre_topc(X0,X1) != sK2
% 2.47/1.00      | u1_pre_topc(sK2) = X1
% 2.47/1.00      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_1719,c_993]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_2526,plain,
% 2.47/1.00      ( u1_pre_topc(sK2) = u1_pre_topc(sK1)
% 2.47/1.00      | m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_1981,c_2319]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_996,plain,
% 2.47/1.00      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.47/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1992,plain,
% 2.47/1.00      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_1876,c_996]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_2533,plain,
% 2.47/1.00      ( u1_pre_topc(sK2) = u1_pre_topc(sK1) ),
% 2.47/1.00      inference(global_propositional_subsumption,
% 2.47/1.00                [status(thm)],
% 2.47/1.00                [c_2526,c_26,c_1992]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_6,plain,
% 2.47/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.47/1.00      | m1_pre_topc(X2,X3)
% 2.47/1.00      | ~ l1_pre_topc(X1)
% 2.47/1.00      | ~ l1_pre_topc(X2)
% 2.47/1.00      | ~ l1_pre_topc(X0)
% 2.47/1.00      | ~ l1_pre_topc(X3)
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
% 2.47/1.00      inference(cnf_transformation,[],[f37]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_991,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
% 2.47/1.00      | m1_pre_topc(X3,X1) != iProver_top
% 2.47/1.00      | m1_pre_topc(X2,X0) = iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X2) != iProver_top
% 2.47/1.00      | l1_pre_topc(X3) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.47/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_2221,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != sK2
% 2.47/1.00      | m1_pre_topc(X0,X2) = iProver_top
% 2.47/1.00      | m1_pre_topc(X1,sK2) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X2) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_1719,c_991]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_28,plain,
% 2.47/1.00      ( l1_pre_topc(sK2) = iProver_top ),
% 2.47/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_3710,plain,
% 2.47/1.00      ( l1_pre_topc(X2) != iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | m1_pre_topc(X1,sK2) != iProver_top
% 2.47/1.00      | m1_pre_topc(X0,X2) = iProver_top
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ),
% 2.47/1.00      inference(global_propositional_subsumption,[status(thm)],[c_2221,c_28]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_3711,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != sK2
% 2.47/1.00      | m1_pre_topc(X0,X2) = iProver_top
% 2.47/1.00      | m1_pre_topc(X1,sK2) != iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X2) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.47/1.00      inference(renaming,[status(thm)],[c_3710]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_3728,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | m1_pre_topc(X0,X1) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,sK2) != iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_2533,c_3711]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_3747,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | m1_pre_topc(X0,X1) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,sK2) != iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(light_normalisation,[status(thm)],[c_3728,c_1719,c_1876]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_2222,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK1))
% 2.47/1.00      | m1_pre_topc(X0,X2) = iProver_top
% 2.47/1.00      | m1_pre_topc(X1,sK1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X2) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_1876,c_991]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_2244,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != sK2
% 2.47/1.00      | m1_pre_topc(X1,X2) = iProver_top
% 2.47/1.00      | m1_pre_topc(X0,sK1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(X2) != iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(light_normalisation,[status(thm)],[c_2222,c_1981]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_2616,plain,
% 2.47/1.00      ( l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X2) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | m1_pre_topc(X0,sK1) != iProver_top
% 2.47/1.00      | m1_pre_topc(X1,X2) = iProver_top
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ),
% 2.47/1.00      inference(global_propositional_subsumption,[status(thm)],[c_2244,c_26]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_2617,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != sK2
% 2.47/1.00      | m1_pre_topc(X1,X2) = iProver_top
% 2.47/1.00      | m1_pre_topc(X0,sK1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X2) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.47/1.00      inference(renaming,[status(thm)],[c_2616]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_2629,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | m1_pre_topc(X0,X1) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_1719,c_2617]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_2220,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK1))
% 2.47/1.00      | m1_pre_topc(X1,X2) != iProver_top
% 2.47/1.00      | m1_pre_topc(X0,sK1) = iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X2) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_1876,c_991]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_2277,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != sK2
% 2.47/1.00      | m1_pre_topc(X0,X2) != iProver_top
% 2.47/1.00      | m1_pre_topc(X1,sK1) = iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(X2) != iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(light_normalisation,[status(thm)],[c_2220,c_1981]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_2790,plain,
% 2.47/1.00      ( l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X2) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | m1_pre_topc(X1,sK1) = iProver_top
% 2.47/1.00      | m1_pre_topc(X0,X2) != iProver_top
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ),
% 2.47/1.00      inference(global_propositional_subsumption,[status(thm)],[c_2277,c_26]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_2791,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != sK2
% 2.47/1.00      | m1_pre_topc(X0,X2) != iProver_top
% 2.47/1.00      | m1_pre_topc(X1,sK1) = iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X2) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.47/1.00      inference(renaming,[status(thm)],[c_2790]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_2805,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | m1_pre_topc(X0,sK1) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_2533,c_2791]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_2864,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | m1_pre_topc(X0,sK1) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(light_normalisation,[status(thm)],[c_2805,c_1719,c_1876]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_5133,plain,
% 2.47/1.00      ( l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,X1) != iProver_top
% 2.47/1.00      | m1_pre_topc(X0,sK1) = iProver_top
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
% 2.47/1.00      inference(global_propositional_subsumption,[status(thm)],[c_2864,c_26]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_5134,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | m1_pre_topc(X0,sK1) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.47/1.00      inference(renaming,[status(thm)],[c_5133]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_5145,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | m1_pre_topc(sK1,X0) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK1) = iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_1719,c_5134]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_2806,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | m1_pre_topc(X0,X1) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK1) = iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_1719,c_2791]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_4815,plain,
% 2.47/1.00      ( l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK1) = iProver_top
% 2.47/1.00      | m1_pre_topc(X0,X1) != iProver_top
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
% 2.47/1.00      inference(global_propositional_subsumption,[status(thm)],[c_2806,c_28]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_4816,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | m1_pre_topc(X0,X1) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK1) = iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.47/1.00      inference(renaming,[status(thm)],[c_4815]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_4829,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) != sK2
% 2.47/1.00      | m1_pre_topc(sK1,X0) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK1) = iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_2533,c_4816]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_4836,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | sK2 != sK2
% 2.47/1.00      | m1_pre_topc(sK1,X0) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK1) = iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(light_normalisation,[status(thm)],[c_4829,c_1719,c_1876]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_4837,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | m1_pre_topc(sK1,X0) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK1) = iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(equality_resolution_simp,[status(thm)],[c_4836]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_5288,plain,
% 2.47/1.00      ( l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK1) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,X0) != iProver_top
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
% 2.47/1.00      inference(global_propositional_subsumption,
% 2.47/1.00                [status(thm)],
% 2.47/1.00                [c_5145,c_26,c_4837]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_5289,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | m1_pre_topc(sK1,X0) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK1) = iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.47/1.00      inference(renaming,[status(thm)],[c_5288]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_5298,plain,
% 2.47/1.00      ( m1_pre_topc(sK1,sK2) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK1) = iProver_top
% 2.47/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_1719,c_5289]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_5309,plain,
% 2.47/1.00      ( m1_pre_topc(sK2,sK1) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,sK2) != iProver_top ),
% 2.47/1.00      inference(global_propositional_subsumption,[status(thm)],[c_5298,c_28]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_5310,plain,
% 2.47/1.00      ( m1_pre_topc(sK1,sK2) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK1) = iProver_top ),
% 2.47/1.00      inference(renaming,[status(thm)],[c_5309]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_6273,plain,
% 2.47/1.00      ( l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,sK2) != iProver_top
% 2.47/1.00      | m1_pre_topc(X0,X1) = iProver_top
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
% 2.47/1.00      inference(global_propositional_subsumption,
% 2.47/1.00                [status(thm)],
% 2.47/1.00                [c_3747,c_28,c_2629,c_5310]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_6274,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | m1_pre_topc(X0,X1) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,sK2) != iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.47/1.00      inference(renaming,[status(thm)],[c_6273]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_6287,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) != sK2
% 2.47/1.00      | m1_pre_topc(sK1,X0) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,sK2) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_2533,c_6274]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_6294,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | sK2 != sK2
% 2.47/1.00      | m1_pre_topc(sK1,X0) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,sK2) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(light_normalisation,[status(thm)],[c_6287,c_1719,c_1876]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_6295,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | m1_pre_topc(sK1,X0) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,sK2) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(equality_resolution_simp,[status(thm)],[c_6294]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_2634,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | m1_pre_topc(X0,sK1) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,X1) = iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_2533,c_2617]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_2653,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | m1_pre_topc(X0,sK1) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,X1) = iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(light_normalisation,[status(thm)],[c_2634,c_1719,c_1876]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_4316,plain,
% 2.47/1.00      ( l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,X1) = iProver_top
% 2.47/1.00      | m1_pre_topc(X0,sK1) != iProver_top
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
% 2.47/1.00      inference(global_propositional_subsumption,[status(thm)],[c_2653,c_26]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_4317,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | m1_pre_topc(X0,sK1) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,X1) = iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.47/1.00      inference(renaming,[status(thm)],[c_4316]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_4326,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | m1_pre_topc(sK1,X0) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_1719,c_4317]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_4170,plain,
% 2.47/1.00      ( l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK1) != iProver_top
% 2.47/1.00      | m1_pre_topc(X0,X1) = iProver_top
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
% 2.47/1.00      inference(global_propositional_subsumption,[status(thm)],[c_2629,c_28]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_4171,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | m1_pre_topc(X0,X1) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.47/1.00      inference(renaming,[status(thm)],[c_4170]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_4184,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) != sK2
% 2.47/1.00      | m1_pre_topc(sK1,X0) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_2533,c_4171]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_4191,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | sK2 != sK2
% 2.47/1.00      | m1_pre_topc(sK1,X0) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(light_normalisation,[status(thm)],[c_4184,c_1719,c_1876]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_4192,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | m1_pre_topc(sK1,X0) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(equality_resolution_simp,[status(thm)],[c_4191]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_4357,plain,
% 2.47/1.00      ( l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK1) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,X0) = iProver_top
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
% 2.47/1.00      inference(global_propositional_subsumption,
% 2.47/1.00                [status(thm)],
% 2.47/1.00                [c_4326,c_26,c_4192]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_4358,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | m1_pre_topc(sK1,X0) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.47/1.00      inference(renaming,[status(thm)],[c_4357]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_6883,plain,
% 2.47/1.00      ( l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,sK2) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,X0) = iProver_top
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
% 2.47/1.00      inference(global_propositional_subsumption,
% 2.47/1.00                [status(thm)],
% 2.47/1.00                [c_6295,c_26,c_4192,c_5310]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_6884,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | m1_pre_topc(sK1,X0) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,sK2) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.47/1.00      inference(renaming,[status(thm)],[c_6883]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_3723,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | m1_pre_topc(X0,sK2) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,X1) = iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_1719,c_3711]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_6071,plain,
% 2.47/1.00      ( l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,X1) = iProver_top
% 2.47/1.00      | m1_pre_topc(X0,sK2) != iProver_top
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
% 2.47/1.00      inference(global_propositional_subsumption,
% 2.47/1.00                [status(thm)],
% 2.47/1.00                [c_3723,c_28,c_2632,c_3492]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_6072,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | m1_pre_topc(X0,sK2) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,X1) = iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.47/1.00      inference(renaming,[status(thm)],[c_6071]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_6081,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | m1_pre_topc(sK2,X0) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK2) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_1719,c_6072]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_6110,plain,
% 2.47/1.00      ( l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK2) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,X0) = iProver_top
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
% 2.47/1.00      inference(global_propositional_subsumption,[status(thm)],[c_6081,c_28]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_6111,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | m1_pre_topc(sK2,X0) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK2) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.47/1.00      inference(renaming,[status(thm)],[c_6110]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_6120,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) != sK2
% 2.47/1.00      | m1_pre_topc(sK2,sK1) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK2) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_2533,c_6111]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_6125,plain,
% 2.47/1.00      ( sK2 != sK2
% 2.47/1.00      | m1_pre_topc(sK2,sK1) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK2) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(light_normalisation,[status(thm)],[c_6120,c_1719,c_1876]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_6126,plain,
% 2.47/1.00      ( m1_pre_topc(sK2,sK1) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK2) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(equality_resolution_simp,[status(thm)],[c_6125]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_6736,plain,
% 2.47/1.00      ( m1_pre_topc(sK2,sK2) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK1) = iProver_top ),
% 2.47/1.00      inference(global_propositional_subsumption,[status(thm)],[c_6126,c_26]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_6737,plain,
% 2.47/1.00      ( m1_pre_topc(sK2,sK1) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK2) != iProver_top ),
% 2.47/1.00      inference(renaming,[status(thm)],[c_6736]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_2219,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != sK2
% 2.47/1.00      | m1_pre_topc(X1,X2) != iProver_top
% 2.47/1.00      | m1_pre_topc(X0,sK2) = iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X2) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_1719,c_991]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_3242,plain,
% 2.47/1.00      ( l1_pre_topc(X2) != iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | m1_pre_topc(X0,sK2) = iProver_top
% 2.47/1.00      | m1_pre_topc(X1,X2) != iProver_top
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ),
% 2.47/1.00      inference(global_propositional_subsumption,[status(thm)],[c_2219,c_28]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_3243,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != sK2
% 2.47/1.00      | m1_pre_topc(X1,X2) != iProver_top
% 2.47/1.00      | m1_pre_topc(X0,sK2) = iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X2) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.47/1.00      inference(renaming,[status(thm)],[c_3242]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_3255,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | m1_pre_topc(X0,X1) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK2) = iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_1719,c_3243]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_2808,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | m1_pre_topc(X0,X1) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,sK1) = iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_2533,c_2791]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_2827,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | m1_pre_topc(X0,X1) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,sK1) = iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(light_normalisation,[status(thm)],[c_2808,c_1719,c_1876]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_2631,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | m1_pre_topc(X0,X1) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,sK1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_2533,c_2617]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_2690,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | m1_pre_topc(X0,X1) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,sK1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(light_normalisation,[status(thm)],[c_2631,c_1719,c_1876]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_4550,plain,
% 2.47/1.00      ( l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,sK1) != iProver_top
% 2.47/1.00      | m1_pre_topc(X0,X1) = iProver_top
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
% 2.47/1.00      inference(global_propositional_subsumption,[status(thm)],[c_2690,c_26]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_4551,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | m1_pre_topc(X0,X1) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,sK1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.47/1.00      inference(renaming,[status(thm)],[c_4550]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_4562,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | m1_pre_topc(sK1,sK1) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,X0) = iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_1719,c_4551]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_2632,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | m1_pre_topc(X0,sK1) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,X1) = iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_1719,c_2617]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_4205,plain,
% 2.47/1.00      ( l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,X1) = iProver_top
% 2.47/1.00      | m1_pre_topc(X0,sK1) != iProver_top
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
% 2.47/1.00      inference(global_propositional_subsumption,[status(thm)],[c_2632,c_28]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_4206,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | m1_pre_topc(X0,sK1) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,X1) = iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.47/1.00      inference(renaming,[status(thm)],[c_4205]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_4217,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) != sK2
% 2.47/1.00      | m1_pre_topc(sK1,sK1) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,X0) = iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_2533,c_4206]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_4224,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | sK2 != sK2
% 2.47/1.00      | m1_pre_topc(sK1,sK1) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,X0) = iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(light_normalisation,[status(thm)],[c_4217,c_1719,c_1876]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_4225,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | m1_pre_topc(sK1,sK1) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,X0) = iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(equality_resolution_simp,[status(thm)],[c_4224]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_4678,plain,
% 2.47/1.00      ( l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,X0) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,sK1) != iProver_top
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
% 2.47/1.00      inference(global_propositional_subsumption,
% 2.47/1.00                [status(thm)],
% 2.47/1.00                [c_4562,c_26,c_4225]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_4679,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | m1_pre_topc(sK1,sK1) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,X0) = iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.47/1.00      inference(renaming,[status(thm)],[c_4678]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_4686,plain,
% 2.47/1.00      ( m1_pre_topc(sK1,sK1) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK2) = iProver_top
% 2.47/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_1719,c_4679]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_4808,plain,
% 2.47/1.00      ( m1_pre_topc(sK2,sK2) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,sK1) != iProver_top ),
% 2.47/1.00      inference(global_propositional_subsumption,[status(thm)],[c_4686,c_28]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_4809,plain,
% 2.47/1.00      ( m1_pre_topc(sK1,sK1) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK2) = iProver_top ),
% 2.47/1.00      inference(renaming,[status(thm)],[c_4808]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_5434,plain,
% 2.47/1.00      ( l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK2) = iProver_top
% 2.47/1.00      | m1_pre_topc(X0,X1) != iProver_top
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
% 2.47/1.00      inference(global_propositional_subsumption,[status(thm)],[c_3255,c_28]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_5435,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | m1_pre_topc(X0,X1) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK2) = iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.47/1.00      inference(renaming,[status(thm)],[c_5434]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_5446,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | m1_pre_topc(sK2,X0) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK2) = iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_1719,c_5435]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_5479,plain,
% 2.47/1.00      ( l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK2) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,X0) != iProver_top
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
% 2.47/1.00      inference(global_propositional_subsumption,[status(thm)],[c_5446,c_28]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_5480,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | m1_pre_topc(sK2,X0) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK2) = iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.47/1.00      inference(renaming,[status(thm)],[c_5479]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_5491,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) != sK2
% 2.47/1.00      | m1_pre_topc(sK2,sK1) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK2) = iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_2533,c_5480]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_5496,plain,
% 2.47/1.00      ( sK2 != sK2
% 2.47/1.00      | m1_pre_topc(sK2,sK1) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK2) = iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(light_normalisation,[status(thm)],[c_5491,c_1719,c_1876]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_5497,plain,
% 2.47/1.00      ( m1_pre_topc(sK2,sK1) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK2) = iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(equality_resolution_simp,[status(thm)],[c_5496]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_6668,plain,
% 2.47/1.00      ( m1_pre_topc(sK2,sK2) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK1) != iProver_top ),
% 2.47/1.00      inference(global_propositional_subsumption,[status(thm)],[c_5497,c_26]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_6669,plain,
% 2.47/1.00      ( m1_pre_topc(sK2,sK1) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK2) = iProver_top ),
% 2.47/1.00      inference(renaming,[status(thm)],[c_6668]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_3725,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | m1_pre_topc(X0,sK2) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,X1) = iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_2533,c_3711]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_3784,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | m1_pre_topc(X0,sK2) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,X1) = iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(light_normalisation,[status(thm)],[c_3725,c_1719,c_1876]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_2809,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | m1_pre_topc(X1,X0) != iProver_top
% 2.47/1.00      | m1_pre_topc(X1,sK1) = iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.47/1.00      inference(equality_resolution,[status(thm)],[c_2791]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_3492,plain,
% 2.47/1.00      ( m1_pre_topc(X0,sK1) = iProver_top
% 2.47/1.00      | m1_pre_topc(X0,sK2) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_1719,c_2809]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_6486,plain,
% 2.47/1.00      ( l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,X1) = iProver_top
% 2.47/1.00      | m1_pre_topc(X0,sK2) != iProver_top
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
% 2.47/1.00      inference(global_propositional_subsumption,
% 2.47/1.00                [status(thm)],
% 2.47/1.00                [c_3784,c_26,c_28,c_2653,c_3492]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_6487,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | m1_pre_topc(X0,sK2) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,X1) = iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.47/1.00      inference(renaming,[status(thm)],[c_6486]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_6496,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | m1_pre_topc(sK1,X0) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK2) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_1719,c_6487]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_3726,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | m1_pre_topc(X0,X1) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK2) != iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_1719,c_3711]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_4962,plain,
% 2.47/1.00      ( l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,sK1) = iProver_top
% 2.47/1.00      | m1_pre_topc(X0,X1) != iProver_top
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
% 2.47/1.00      inference(global_propositional_subsumption,[status(thm)],[c_2827,c_26]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_4963,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | m1_pre_topc(X0,X1) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,sK1) = iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.47/1.00      inference(renaming,[status(thm)],[c_4962]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_4974,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | m1_pre_topc(sK1,sK1) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_1719,c_4963]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_2803,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | m1_pre_topc(X0,sK1) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_1719,c_2791]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_4641,plain,
% 2.47/1.00      ( l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,X1) != iProver_top
% 2.47/1.00      | m1_pre_topc(X0,sK1) = iProver_top
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
% 2.47/1.00      inference(global_propositional_subsumption,[status(thm)],[c_2803,c_28]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_4642,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | m1_pre_topc(X0,sK1) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.47/1.00      inference(renaming,[status(thm)],[c_4641]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_4655,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) != sK2
% 2.47/1.00      | m1_pre_topc(sK1,sK1) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_2533,c_4642]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_4662,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | sK2 != sK2
% 2.47/1.00      | m1_pre_topc(sK1,sK1) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(light_normalisation,[status(thm)],[c_4655,c_1719,c_1876]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_4663,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | m1_pre_topc(sK1,sK1) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(equality_resolution_simp,[status(thm)],[c_4662]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_5007,plain,
% 2.47/1.00      ( l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,X0) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,sK1) = iProver_top
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
% 2.47/1.00      inference(global_propositional_subsumption,
% 2.47/1.00                [status(thm)],
% 2.47/1.00                [c_4974,c_26,c_4663]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_5008,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | m1_pre_topc(sK1,sK1) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.47/1.00      inference(renaming,[status(thm)],[c_5007]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_5017,plain,
% 2.47/1.00      ( m1_pre_topc(sK1,sK1) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK2) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_1719,c_5008]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_5126,plain,
% 2.47/1.00      ( m1_pre_topc(sK2,sK2) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,sK1) = iProver_top ),
% 2.47/1.00      inference(global_propositional_subsumption,[status(thm)],[c_5017,c_28]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_5127,plain,
% 2.47/1.00      ( m1_pre_topc(sK1,sK1) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK2) != iProver_top ),
% 2.47/1.00      inference(renaming,[status(thm)],[c_5126]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_6243,plain,
% 2.47/1.00      ( l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK2) != iProver_top
% 2.47/1.00      | m1_pre_topc(X0,X1) = iProver_top
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
% 2.47/1.00      inference(global_propositional_subsumption,
% 2.47/1.00                [status(thm)],
% 2.47/1.00                [c_3726,c_26,c_28,c_2629,c_6126]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_6244,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | m1_pre_topc(X0,X1) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK2) != iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.47/1.00      inference(renaming,[status(thm)],[c_6243]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_6257,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) != sK2
% 2.47/1.00      | m1_pre_topc(sK1,X0) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK2) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_2533,c_6244]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_6264,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | sK2 != sK2
% 2.47/1.00      | m1_pre_topc(sK1,X0) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK2) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(light_normalisation,[status(thm)],[c_6257,c_1719,c_1876]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_6265,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | m1_pre_topc(sK1,X0) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK2) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(equality_resolution_simp,[status(thm)],[c_6264]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_6656,plain,
% 2.47/1.00      ( l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK2) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,X0) = iProver_top
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
% 2.47/1.00      inference(global_propositional_subsumption,
% 2.47/1.00                [status(thm)],
% 2.47/1.00                [c_6496,c_26,c_6265]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_6657,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | m1_pre_topc(sK1,X0) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK2) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.47/1.00      inference(renaming,[status(thm)],[c_6656]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_6285,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | m1_pre_topc(sK1,sK2) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,X0) = iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_1719,c_6274]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_6083,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) != sK2
% 2.47/1.00      | m1_pre_topc(sK1,sK2) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,X0) = iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_2533,c_6072]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_6090,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | sK2 != sK2
% 2.47/1.00      | m1_pre_topc(sK1,sK2) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,X0) = iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(light_normalisation,[status(thm)],[c_6083,c_1719,c_1876]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_6091,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | m1_pre_topc(sK1,sK2) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,X0) = iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(equality_resolution_simp,[status(thm)],[c_6090]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_6474,plain,
% 2.47/1.00      ( l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,X0) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,sK2) != iProver_top
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
% 2.47/1.00      inference(global_propositional_subsumption,
% 2.47/1.00                [status(thm)],
% 2.47/1.00                [c_6285,c_26,c_6091]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_6475,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | m1_pre_topc(sK1,sK2) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,X0) = iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.47/1.00      inference(renaming,[status(thm)],[c_6474]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_3257,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | m1_pre_topc(X0,X1) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,sK2) = iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_2533,c_3243]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_3316,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | m1_pre_topc(X0,X1) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,sK2) = iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(light_normalisation,[status(thm)],[c_3257,c_1719,c_1876]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_5950,plain,
% 2.47/1.00      ( l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,sK2) = iProver_top
% 2.47/1.00      | m1_pre_topc(X0,X1) != iProver_top
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
% 2.47/1.00      inference(global_propositional_subsumption,
% 2.47/1.00                [status(thm)],
% 2.47/1.00                [c_3316,c_28,c_2806,c_4544]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_5951,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | m1_pre_topc(X0,X1) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,sK2) = iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.47/1.00      inference(renaming,[status(thm)],[c_5950]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_5962,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | m1_pre_topc(sK1,sK2) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_1719,c_5951]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_3258,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | m1_pre_topc(X0,sK2) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_1719,c_3243]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_2635,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | m1_pre_topc(X1,X0) = iProver_top
% 2.47/1.00      | m1_pre_topc(X1,sK1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.47/1.00      inference(equality_resolution,[status(thm)],[c_2617]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_3403,plain,
% 2.47/1.00      ( m1_pre_topc(X0,sK1) != iProver_top
% 2.47/1.00      | m1_pre_topc(X0,sK2) = iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_1719,c_2635]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_5620,plain,
% 2.47/1.00      ( l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,X1) != iProver_top
% 2.47/1.00      | m1_pre_topc(X0,sK2) = iProver_top
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
% 2.47/1.00      inference(global_propositional_subsumption,
% 2.47/1.00                [status(thm)],
% 2.47/1.00                [c_3258,c_28,c_2803,c_3403]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_5621,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | m1_pre_topc(X0,sK2) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.47/1.00      inference(renaming,[status(thm)],[c_5620]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_5634,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) != sK2
% 2.47/1.00      | m1_pre_topc(sK1,sK2) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_2533,c_5621]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_5641,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | sK2 != sK2
% 2.47/1.00      | m1_pre_topc(sK1,sK2) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(light_normalisation,[status(thm)],[c_5634,c_1719,c_1876]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_5642,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | m1_pre_topc(sK1,sK2) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(equality_resolution_simp,[status(thm)],[c_5641]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_5979,plain,
% 2.47/1.00      ( l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,X0) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,sK2) = iProver_top
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
% 2.47/1.00      inference(global_propositional_subsumption,
% 2.47/1.00                [status(thm)],
% 2.47/1.00                [c_5962,c_26,c_5642]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_5980,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | m1_pre_topc(sK1,sK2) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.47/1.00      inference(renaming,[status(thm)],[c_5979]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_3260,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | m1_pre_topc(X0,sK2) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_2533,c_3243]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_3279,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | m1_pre_topc(X0,sK2) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(light_normalisation,[status(thm)],[c_3260,c_1719,c_1876]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_5765,plain,
% 2.47/1.00      ( l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,X1) != iProver_top
% 2.47/1.00      | m1_pre_topc(X0,sK2) = iProver_top
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
% 2.47/1.00      inference(global_propositional_subsumption,
% 2.47/1.00                [status(thm)],
% 2.47/1.00                [c_3279,c_26,c_28,c_2864,c_3403]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_5766,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK2
% 2.47/1.00      | m1_pre_topc(X0,sK2) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.47/1.00      inference(renaming,[status(thm)],[c_5765]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_5777,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | m1_pre_topc(sK1,X0) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK2) = iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_1719,c_5766]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_5810,plain,
% 2.47/1.00      ( l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK2) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,X0) != iProver_top
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
% 2.47/1.00      inference(global_propositional_subsumption,
% 2.47/1.00                [status(thm)],
% 2.47/1.00                [c_5777,c_26,c_5456]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_5811,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | m1_pre_topc(sK1,X0) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK2) = iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.47/1.00      inference(renaming,[status(thm)],[c_5810]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_4365,plain,
% 2.47/1.00      ( m1_pre_topc(sK1,sK2) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK1) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_1719,c_4358]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_4543,plain,
% 2.47/1.00      ( m1_pre_topc(sK2,sK1) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,sK2) = iProver_top ),
% 2.47/1.00      inference(global_propositional_subsumption,[status(thm)],[c_4365,c_28]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_4544,plain,
% 2.47/1.00      ( m1_pre_topc(sK1,sK2) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK1) != iProver_top ),
% 2.47/1.00      inference(renaming,[status(thm)],[c_4543]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_12,negated_conjecture,
% 2.47/1.00      ( m1_pre_topc(sK1,sK0) | m1_pre_topc(sK2,sK0) ),
% 2.47/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_988,plain,
% 2.47/1.00      ( m1_pre_topc(sK1,sK0) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK2,sK0) = iProver_top ),
% 2.47/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_2223,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
% 2.47/1.00      | m1_pre_topc(X0,X2) != iProver_top
% 2.47/1.00      | m1_pre_topc(X1,X2) = iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(X2) != iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top ),
% 2.47/1.00      inference(equality_resolution,[status(thm)],[c_991]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_3160,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))
% 2.47/1.00      | m1_pre_topc(X0,X1) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_2533,c_2223]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_3203,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | m1_pre_topc(X0,X1) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.00      inference(light_normalisation,[status(thm)],[c_3160,c_1719,c_1876]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_4001,plain,
% 2.47/1.00      ( l1_pre_topc(X0) != iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,X1) != iProver_top
% 2.47/1.00      | m1_pre_topc(X0,X1) = iProver_top
% 2.47/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
% 2.47/1.00      inference(global_propositional_subsumption,[status(thm)],[c_3203,c_26]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_4002,plain,
% 2.47/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.00      | m1_pre_topc(X0,X1) = iProver_top
% 2.47/1.00      | m1_pre_topc(sK1,X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X1) != iProver_top
% 2.47/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.47/1.00      inference(renaming,[status(thm)],[c_4001]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_4012,plain,
% 2.47/1.00      ( m1_pre_topc(sK1,X0) != iProver_top
% 2.47/1.01      | m1_pre_topc(sK2,X0) = iProver_top
% 2.47/1.01      | l1_pre_topc(X0) != iProver_top
% 2.47/1.01      | l1_pre_topc(sK2) != iProver_top ),
% 2.47/1.01      inference(superposition,[status(thm)],[c_1719,c_4002]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_3161,plain,
% 2.47/1.01      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.01      | m1_pre_topc(X0,X1) != iProver_top
% 2.47/1.01      | m1_pre_topc(sK2,X1) = iProver_top
% 2.47/1.01      | l1_pre_topc(X1) != iProver_top
% 2.47/1.01      | l1_pre_topc(X0) != iProver_top
% 2.47/1.01      | l1_pre_topc(sK2) != iProver_top ),
% 2.47/1.01      inference(superposition,[status(thm)],[c_1719,c_2223]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_3681,plain,
% 2.47/1.01      ( l1_pre_topc(X0) != iProver_top
% 2.47/1.01      | l1_pre_topc(X1) != iProver_top
% 2.47/1.01      | m1_pre_topc(sK2,X1) = iProver_top
% 2.47/1.01      | m1_pre_topc(X0,X1) != iProver_top
% 2.47/1.01      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
% 2.47/1.01      inference(global_propositional_subsumption,[status(thm)],[c_3161,c_28]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_3682,plain,
% 2.47/1.01      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.01      | m1_pre_topc(X0,X1) != iProver_top
% 2.47/1.01      | m1_pre_topc(sK2,X1) = iProver_top
% 2.47/1.01      | l1_pre_topc(X1) != iProver_top
% 2.47/1.01      | l1_pre_topc(X0) != iProver_top ),
% 2.47/1.01      inference(renaming,[status(thm)],[c_3681]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_3694,plain,
% 2.47/1.01      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) != sK2
% 2.47/1.01      | m1_pre_topc(sK1,X0) != iProver_top
% 2.47/1.01      | m1_pre_topc(sK2,X0) = iProver_top
% 2.47/1.01      | l1_pre_topc(X0) != iProver_top
% 2.47/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.01      inference(superposition,[status(thm)],[c_2533,c_3682]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_3700,plain,
% 2.47/1.01      ( sK2 != sK2
% 2.47/1.01      | m1_pre_topc(sK1,X0) != iProver_top
% 2.47/1.01      | m1_pre_topc(sK2,X0) = iProver_top
% 2.47/1.01      | l1_pre_topc(X0) != iProver_top
% 2.47/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.01      inference(light_normalisation,[status(thm)],[c_3694,c_1719,c_1876]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_3701,plain,
% 2.47/1.01      ( m1_pre_topc(sK1,X0) != iProver_top
% 2.47/1.01      | m1_pre_topc(sK2,X0) = iProver_top
% 2.47/1.01      | l1_pre_topc(X0) != iProver_top
% 2.47/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.01      inference(equality_resolution_simp,[status(thm)],[c_3700]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_4027,plain,
% 2.47/1.01      ( l1_pre_topc(X0) != iProver_top
% 2.47/1.01      | m1_pre_topc(sK2,X0) = iProver_top
% 2.47/1.01      | m1_pre_topc(sK1,X0) != iProver_top ),
% 2.47/1.01      inference(global_propositional_subsumption,
% 2.47/1.01                [status(thm)],
% 2.47/1.01                [c_4012,c_26,c_3701]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_4028,plain,
% 2.47/1.01      ( m1_pre_topc(sK1,X0) != iProver_top
% 2.47/1.01      | m1_pre_topc(sK2,X0) = iProver_top
% 2.47/1.01      | l1_pre_topc(X0) != iProver_top ),
% 2.47/1.01      inference(renaming,[status(thm)],[c_4027]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_4036,plain,
% 2.47/1.01      ( m1_pre_topc(sK2,sK0) = iProver_top | l1_pre_topc(sK0) != iProver_top ),
% 2.47/1.01      inference(superposition,[status(thm)],[c_988,c_4028]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_21,negated_conjecture,
% 2.47/1.01      ( l1_pre_topc(sK0) ),
% 2.47/1.01      inference(cnf_transformation,[],[f43]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_24,plain,
% 2.47/1.01      ( l1_pre_topc(sK0) = iProver_top ),
% 2.47/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_4071,plain,
% 2.47/1.01      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 2.47/1.01      inference(global_propositional_subsumption,[status(thm)],[c_4036,c_24]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_3163,plain,
% 2.47/1.01      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))
% 2.47/1.01      | m1_pre_topc(X0,X1) != iProver_top
% 2.47/1.01      | m1_pre_topc(sK1,X1) = iProver_top
% 2.47/1.01      | l1_pre_topc(X1) != iProver_top
% 2.47/1.01      | l1_pre_topc(X0) != iProver_top
% 2.47/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.01      inference(superposition,[status(thm)],[c_2533,c_2223]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_3171,plain,
% 2.47/1.01      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.01      | m1_pre_topc(X0,X1) != iProver_top
% 2.47/1.01      | m1_pre_topc(sK1,X1) = iProver_top
% 2.47/1.01      | l1_pre_topc(X1) != iProver_top
% 2.47/1.01      | l1_pre_topc(X0) != iProver_top
% 2.47/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.01      inference(light_normalisation,[status(thm)],[c_3163,c_1719,c_1876]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_3911,plain,
% 2.47/1.01      ( l1_pre_topc(X0) != iProver_top
% 2.47/1.01      | l1_pre_topc(X1) != iProver_top
% 2.47/1.01      | m1_pre_topc(sK1,X1) = iProver_top
% 2.47/1.01      | m1_pre_topc(X0,X1) != iProver_top
% 2.47/1.01      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
% 2.47/1.01      inference(global_propositional_subsumption,[status(thm)],[c_3171,c_26]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_3912,plain,
% 2.47/1.01      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.01      | m1_pre_topc(X0,X1) != iProver_top
% 2.47/1.01      | m1_pre_topc(sK1,X1) = iProver_top
% 2.47/1.01      | l1_pre_topc(X1) != iProver_top
% 2.47/1.01      | l1_pre_topc(X0) != iProver_top ),
% 2.47/1.01      inference(renaming,[status(thm)],[c_3911]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_3922,plain,
% 2.47/1.01      ( m1_pre_topc(sK1,X0) = iProver_top
% 2.47/1.01      | m1_pre_topc(sK2,X0) != iProver_top
% 2.47/1.01      | l1_pre_topc(X0) != iProver_top
% 2.47/1.01      | l1_pre_topc(sK2) != iProver_top ),
% 2.47/1.01      inference(superposition,[status(thm)],[c_1719,c_3912]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_3158,plain,
% 2.47/1.01      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.01      | m1_pre_topc(X0,X1) = iProver_top
% 2.47/1.01      | m1_pre_topc(sK2,X1) != iProver_top
% 2.47/1.01      | l1_pre_topc(X1) != iProver_top
% 2.47/1.01      | l1_pre_topc(X0) != iProver_top
% 2.47/1.01      | l1_pre_topc(sK2) != iProver_top ),
% 2.47/1.01      inference(superposition,[status(thm)],[c_1719,c_2223]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_3587,plain,
% 2.47/1.01      ( l1_pre_topc(X0) != iProver_top
% 2.47/1.01      | l1_pre_topc(X1) != iProver_top
% 2.47/1.01      | m1_pre_topc(sK2,X1) != iProver_top
% 2.47/1.01      | m1_pre_topc(X0,X1) = iProver_top
% 2.47/1.01      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2 ),
% 2.47/1.01      inference(global_propositional_subsumption,[status(thm)],[c_3158,c_28]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_3588,plain,
% 2.47/1.01      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.01      | m1_pre_topc(X0,X1) = iProver_top
% 2.47/1.01      | m1_pre_topc(sK2,X1) != iProver_top
% 2.47/1.01      | l1_pre_topc(X1) != iProver_top
% 2.47/1.01      | l1_pre_topc(X0) != iProver_top ),
% 2.47/1.01      inference(renaming,[status(thm)],[c_3587]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_3600,plain,
% 2.47/1.01      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) != sK2
% 2.47/1.01      | m1_pre_topc(sK1,X0) = iProver_top
% 2.47/1.01      | m1_pre_topc(sK2,X0) != iProver_top
% 2.47/1.01      | l1_pre_topc(X0) != iProver_top
% 2.47/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.01      inference(superposition,[status(thm)],[c_2533,c_3588]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_3606,plain,
% 2.47/1.01      ( sK2 != sK2
% 2.47/1.01      | m1_pre_topc(sK1,X0) = iProver_top
% 2.47/1.01      | m1_pre_topc(sK2,X0) != iProver_top
% 2.47/1.01      | l1_pre_topc(X0) != iProver_top
% 2.47/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.01      inference(light_normalisation,[status(thm)],[c_3600,c_1719,c_1876]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_3607,plain,
% 2.47/1.01      ( m1_pre_topc(sK1,X0) = iProver_top
% 2.47/1.01      | m1_pre_topc(sK2,X0) != iProver_top
% 2.47/1.01      | l1_pre_topc(X0) != iProver_top
% 2.47/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.01      inference(equality_resolution_simp,[status(thm)],[c_3606]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_3937,plain,
% 2.47/1.01      ( l1_pre_topc(X0) != iProver_top
% 2.47/1.01      | m1_pre_topc(sK2,X0) != iProver_top
% 2.47/1.01      | m1_pre_topc(sK1,X0) = iProver_top ),
% 2.47/1.01      inference(global_propositional_subsumption,
% 2.47/1.01                [status(thm)],
% 2.47/1.01                [c_3922,c_26,c_3607]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_3938,plain,
% 2.47/1.01      ( m1_pre_topc(sK1,X0) = iProver_top
% 2.47/1.01      | m1_pre_topc(sK2,X0) != iProver_top
% 2.47/1.01      | l1_pre_topc(X0) != iProver_top ),
% 2.47/1.01      inference(renaming,[status(thm)],[c_3937]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_4076,plain,
% 2.47/1.01      ( m1_pre_topc(sK1,sK0) = iProver_top | l1_pre_topc(sK0) != iProver_top ),
% 2.47/1.01      inference(superposition,[status(thm)],[c_4071,c_3938]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_3940,plain,
% 2.47/1.01      ( m1_pre_topc(sK1,sK0) = iProver_top
% 2.47/1.01      | m1_pre_topc(sK2,sK0) != iProver_top
% 2.47/1.01      | l1_pre_topc(sK0) != iProver_top ),
% 2.47/1.01      inference(instantiation,[status(thm)],[c_3938]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_4079,plain,
% 2.47/1.01      ( m1_pre_topc(sK1,sK0) = iProver_top ),
% 2.47/1.01      inference(global_propositional_subsumption,
% 2.47/1.01                [status(thm)],
% 2.47/1.01                [c_4076,c_24,c_3940,c_4036]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_3729,plain,
% 2.47/1.01      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.01      | m1_pre_topc(X1,X0) = iProver_top
% 2.47/1.01      | m1_pre_topc(X1,sK2) != iProver_top
% 2.47/1.01      | l1_pre_topc(X1) != iProver_top
% 2.47/1.01      | l1_pre_topc(X0) != iProver_top ),
% 2.47/1.01      inference(equality_resolution,[status(thm)],[c_3711]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_3577,plain,
% 2.47/1.01      ( l1_pre_topc(X0) != iProver_top
% 2.47/1.01      | m1_pre_topc(X0,sK2) != iProver_top
% 2.47/1.01      | m1_pre_topc(X0,sK1) = iProver_top ),
% 2.47/1.01      inference(global_propositional_subsumption,[status(thm)],[c_3492,c_28]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_3578,plain,
% 2.47/1.01      ( m1_pre_topc(X0,sK1) = iProver_top
% 2.47/1.01      | m1_pre_topc(X0,sK2) != iProver_top
% 2.47/1.01      | l1_pre_topc(X0) != iProver_top ),
% 2.47/1.01      inference(renaming,[status(thm)],[c_3577]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_3477,plain,
% 2.47/1.01      ( l1_pre_topc(X0) != iProver_top
% 2.47/1.01      | m1_pre_topc(X0,sK2) = iProver_top
% 2.47/1.01      | m1_pre_topc(X0,sK1) != iProver_top ),
% 2.47/1.01      inference(global_propositional_subsumption,[status(thm)],[c_3403,c_28]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_3478,plain,
% 2.47/1.01      ( m1_pre_topc(X0,sK1) != iProver_top
% 2.47/1.01      | m1_pre_topc(X0,sK2) = iProver_top
% 2.47/1.01      | l1_pre_topc(X0) != iProver_top ),
% 2.47/1.01      inference(renaming,[status(thm)],[c_3477]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_3261,plain,
% 2.47/1.01      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK2
% 2.47/1.01      | m1_pre_topc(X1,X0) != iProver_top
% 2.47/1.01      | m1_pre_topc(X1,sK2) = iProver_top
% 2.47/1.01      | l1_pre_topc(X1) != iProver_top
% 2.47/1.01      | l1_pre_topc(X0) != iProver_top ),
% 2.47/1.01      inference(equality_resolution,[status(thm)],[c_3243]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_10,plain,
% 2.47/1.01      ( ~ m1_pre_topc(X0,X1)
% 2.47/1.01      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.47/1.01      | ~ l1_pre_topc(X1) ),
% 2.47/1.01      inference(cnf_transformation,[],[f41]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_990,plain,
% 2.47/1.01      ( m1_pre_topc(X0,X1) != iProver_top
% 2.47/1.01      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 2.47/1.01      | l1_pre_topc(X1) != iProver_top ),
% 2.47/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1993,plain,
% 2.47/1.01      ( m1_pre_topc(X0,sK1) != iProver_top
% 2.47/1.01      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 2.47/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 2.47/1.01      inference(superposition,[status(thm)],[c_1876,c_990]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_3010,plain,
% 2.47/1.01      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 2.47/1.01      | m1_pre_topc(X0,sK1) != iProver_top ),
% 2.47/1.01      inference(global_propositional_subsumption,[status(thm)],[c_1993,c_26]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_3011,plain,
% 2.47/1.01      ( m1_pre_topc(X0,sK1) != iProver_top
% 2.47/1.01      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.47/1.01      inference(renaming,[status(thm)],[c_3010]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_3018,plain,
% 2.47/1.01      ( m1_pre_topc(sK1,sK1) != iProver_top
% 2.47/1.01      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.47/1.01      inference(superposition,[status(thm)],[c_1876,c_3011]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_2320,plain,
% 2.47/1.01      ( g1_pre_topc(X0,X1) != sK2
% 2.47/1.01      | u1_pre_topc(sK1) = X1
% 2.47/1.01      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.47/1.01      inference(superposition,[status(thm)],[c_1981,c_993]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_2322,plain,
% 2.47/1.01      ( g1_pre_topc(X0,X1) != sK2
% 2.47/1.01      | u1_pre_topc(sK1) = X1
% 2.47/1.01      | m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
% 2.47/1.01      inference(superposition,[status(thm)],[c_1981,c_993]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_2604,plain,
% 2.47/1.01      ( u1_pre_topc(sK1) = X1 | g1_pre_topc(X0,X1) != sK2 ),
% 2.47/1.01      inference(global_propositional_subsumption,
% 2.47/1.01                [status(thm)],
% 2.47/1.01                [c_2320,c_26,c_1992,c_2322]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_2605,plain,
% 2.47/1.01      ( g1_pre_topc(X0,X1) != sK2 | u1_pre_topc(sK1) = X1 ),
% 2.47/1.01      inference(renaming,[status(thm)],[c_2604]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_2607,plain,
% 2.47/1.01      ( g1_pre_topc(X0,X1) != sK2 | u1_pre_topc(sK2) = X1 ),
% 2.47/1.01      inference(demodulation,[status(thm)],[c_2605,c_2533]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_2103,plain,
% 2.47/1.01      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top ),
% 2.47/1.01      inference(global_propositional_subsumption,[status(thm)],[c_1992,c_26]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_2536,plain,
% 2.47/1.01      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top ),
% 2.47/1.01      inference(demodulation,[status(thm)],[c_2533,c_2103]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1990,plain,
% 2.47/1.01      ( m1_pre_topc(sK1,X0) != iProver_top
% 2.47/1.01      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 2.47/1.01      | l1_pre_topc(X0) != iProver_top ),
% 2.47/1.01      inference(superposition,[status(thm)],[c_1876,c_990]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1980,plain,
% 2.47/1.01      ( g1_pre_topc(X0,X1) != sK2 | u1_struct_0(sK2) = X0 ),
% 2.47/1.01      inference(demodulation,[status(thm)],[c_1876,c_1868]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_982,plain,
% 2.47/1.01      ( l1_pre_topc(sK1) = iProver_top ),
% 2.47/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1453,plain,
% 2.47/1.01      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK1
% 2.47/1.01      | v1_pre_topc(sK1) != iProver_top ),
% 2.47/1.01      inference(superposition,[status(thm)],[c_982,c_997]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1461,plain,
% 2.47/1.01      ( sK1 = sK2 | v1_pre_topc(sK1) != iProver_top ),
% 2.47/1.01      inference(light_normalisation,[status(thm)],[c_1453,c_16]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_980,plain,
% 2.47/1.01      ( l1_pre_topc(sK0) = iProver_top ),
% 2.47/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1454,plain,
% 2.47/1.01      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = sK0
% 2.47/1.01      | v1_pre_topc(sK0) != iProver_top ),
% 2.47/1.01      inference(superposition,[status(thm)],[c_980,c_997]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_2,plain,
% 2.47/1.01      ( ~ v2_pre_topc(X0)
% 2.47/1.01      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 2.47/1.01      | ~ l1_pre_topc(X0) ),
% 2.47/1.01      inference(cnf_transformation,[],[f34]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_995,plain,
% 2.47/1.01      ( v2_pre_topc(X0) != iProver_top
% 2.47/1.01      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
% 2.47/1.01      | l1_pre_topc(X0) != iProver_top ),
% 2.47/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_11,negated_conjecture,
% 2.47/1.01      ( ~ v1_tsep_1(sK1,sK0)
% 2.47/1.01      | ~ v1_tsep_1(sK2,sK0)
% 2.47/1.01      | ~ m1_pre_topc(sK1,sK0)
% 2.47/1.01      | ~ m1_pre_topc(sK2,sK0) ),
% 2.47/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_989,plain,
% 2.47/1.01      ( v1_tsep_1(sK1,sK0) != iProver_top
% 2.47/1.01      | v1_tsep_1(sK2,sK0) != iProver_top
% 2.47/1.01      | m1_pre_topc(sK1,sK0) != iProver_top
% 2.47/1.01      | m1_pre_topc(sK2,sK0) != iProver_top ),
% 2.47/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_13,negated_conjecture,
% 2.47/1.01      ( v1_tsep_1(sK1,sK0) | m1_pre_topc(sK2,sK0) ),
% 2.47/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_987,plain,
% 2.47/1.01      ( v1_tsep_1(sK1,sK0) = iProver_top | m1_pre_topc(sK2,sK0) = iProver_top ),
% 2.47/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_14,negated_conjecture,
% 2.47/1.01      ( v1_tsep_1(sK2,sK0) | m1_pre_topc(sK1,sK0) ),
% 2.47/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_986,plain,
% 2.47/1.01      ( v1_tsep_1(sK2,sK0) = iProver_top | m1_pre_topc(sK1,sK0) = iProver_top ),
% 2.47/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_15,negated_conjecture,
% 2.47/1.01      ( v1_tsep_1(sK1,sK0) | v1_tsep_1(sK2,sK0) ),
% 2.47/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_985,plain,
% 2.47/1.01      ( v1_tsep_1(sK1,sK0) = iProver_top | v1_tsep_1(sK2,sK0) = iProver_top ),
% 2.47/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_18,negated_conjecture,
% 2.47/1.01      ( v2_pre_topc(sK2) ),
% 2.47/1.01      inference(cnf_transformation,[],[f46]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_983,plain,
% 2.47/1.01      ( v2_pre_topc(sK2) = iProver_top ),
% 2.47/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_981,plain,
% 2.47/1.01      ( v2_pre_topc(sK1) = iProver_top ),
% 2.47/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_22,negated_conjecture,
% 2.47/1.01      ( v2_pre_topc(sK0) ),
% 2.47/1.01      inference(cnf_transformation,[],[f42]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_979,plain,
% 2.47/1.01      ( v2_pre_topc(sK0) = iProver_top ),
% 2.47/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.47/1.01  
% 2.47/1.01  
% 2.47/1.01  % SZS output end Saturation for theBenchmark.p
% 2.47/1.01  
% 2.47/1.01  ------                               Statistics
% 2.47/1.01  
% 2.47/1.01  ------ General
% 2.47/1.01  
% 2.47/1.01  abstr_ref_over_cycles:                  0
% 2.47/1.01  abstr_ref_under_cycles:                 0
% 2.47/1.01  gc_basic_clause_elim:                   0
% 2.47/1.01  forced_gc_time:                         0
% 2.47/1.01  parsing_time:                           0.007
% 2.47/1.01  unif_index_cands_time:                  0.
% 2.47/1.01  unif_index_add_time:                    0.
% 2.47/1.01  orderings_time:                         0.
% 2.47/1.01  out_proof_time:                         0.
% 2.47/1.01  total_time:                             0.213
% 2.47/1.01  num_of_symbols:                         45
% 2.47/1.01  num_of_terms:                           4721
% 2.47/1.01  
% 2.47/1.01  ------ Preprocessing
% 2.47/1.01  
% 2.47/1.01  num_of_splits:                          0
% 2.47/1.01  num_of_split_atoms:                     0
% 2.47/1.01  num_of_reused_defs:                     0
% 2.47/1.01  num_eq_ax_congr_red:                    1
% 2.47/1.01  num_of_sem_filtered_clauses:            1
% 2.47/1.01  num_of_subtypes:                        0
% 2.47/1.01  monotx_restored_types:                  0
% 2.47/1.01  sat_num_of_epr_types:                   0
% 2.47/1.01  sat_num_of_non_cyclic_types:            0
% 2.47/1.01  sat_guarded_non_collapsed_types:        0
% 2.47/1.01  num_pure_diseq_elim:                    0
% 2.47/1.01  simp_replaced_by:                       0
% 2.47/1.01  res_preprocessed:                       107
% 2.47/1.01  prep_upred:                             0
% 2.47/1.01  prep_unflattend:                        10
% 2.47/1.01  smt_new_axioms:                         0
% 2.47/1.01  pred_elim_cands:                        6
% 2.47/1.01  pred_elim:                              1
% 2.47/1.01  pred_elim_cl:                           2
% 2.47/1.01  pred_elim_cycles:                       5
% 2.47/1.01  merged_defs:                            0
% 2.47/1.01  merged_defs_ncl:                        0
% 2.47/1.01  bin_hyper_res:                          0
% 2.47/1.01  prep_cycles:                            4
% 2.47/1.01  pred_elim_time:                         0.004
% 2.47/1.01  splitting_time:                         0.
% 2.47/1.01  sem_filter_time:                        0.
% 2.47/1.01  monotx_time:                            0.
% 2.47/1.01  subtype_inf_time:                       0.
% 2.47/1.01  
% 2.47/1.01  ------ Problem properties
% 2.47/1.01  
% 2.47/1.01  clauses:                                20
% 2.47/1.01  conjectures:                            12
% 2.47/1.01  epr:                                    11
% 2.47/1.01  horn:                                   16
% 2.47/1.01  ground:                                 12
% 2.47/1.01  unary:                                  7
% 2.47/1.01  binary:                                 5
% 2.47/1.01  lits:                                   47
% 2.47/1.01  lits_eq:                                8
% 2.47/1.01  fd_pure:                                0
% 2.47/1.01  fd_pseudo:                              0
% 2.47/1.01  fd_cond:                                0
% 2.47/1.01  fd_pseudo_cond:                         2
% 2.47/1.01  ac_symbols:                             0
% 2.47/1.01  
% 2.47/1.01  ------ Propositional Solver
% 2.47/1.01  
% 2.47/1.01  prop_solver_calls:                      31
% 2.47/1.01  prop_fast_solver_calls:                 1198
% 2.47/1.01  smt_solver_calls:                       0
% 2.47/1.01  smt_fast_solver_calls:                  0
% 2.47/1.01  prop_num_of_clauses:                    1840
% 2.47/1.01  prop_preprocess_simplified:             5478
% 2.47/1.01  prop_fo_subsumed:                       61
% 2.47/1.01  prop_solver_time:                       0.
% 2.47/1.01  smt_solver_time:                        0.
% 2.47/1.01  smt_fast_solver_time:                   0.
% 2.47/1.01  prop_fast_solver_time:                  0.
% 2.47/1.01  prop_unsat_core_time:                   0.
% 2.47/1.01  
% 2.47/1.01  ------ QBF
% 2.47/1.01  
% 2.47/1.01  qbf_q_res:                              0
% 2.47/1.01  qbf_num_tautologies:                    0
% 2.47/1.01  qbf_prep_cycles:                        0
% 2.47/1.01  
% 2.47/1.01  ------ BMC1
% 2.47/1.01  
% 2.47/1.01  bmc1_current_bound:                     -1
% 2.47/1.01  bmc1_last_solved_bound:                 -1
% 2.47/1.01  bmc1_unsat_core_size:                   -1
% 2.47/1.01  bmc1_unsat_core_parents_size:           -1
% 2.47/1.01  bmc1_merge_next_fun:                    0
% 2.47/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.47/1.01  
% 2.47/1.01  ------ Instantiation
% 2.47/1.01  
% 2.47/1.01  inst_num_of_clauses:                    600
% 2.47/1.01  inst_num_in_passive:                    156
% 2.47/1.01  inst_num_in_active:                     409
% 2.47/1.01  inst_num_in_unprocessed:                35
% 2.47/1.01  inst_num_of_loops:                      450
% 2.47/1.01  inst_num_of_learning_restarts:          0
% 2.47/1.01  inst_num_moves_active_passive:          36
% 2.47/1.01  inst_lit_activity:                      0
% 2.47/1.01  inst_lit_activity_moves:                0
% 2.47/1.01  inst_num_tautologies:                   0
% 2.47/1.01  inst_num_prop_implied:                  0
% 2.47/1.01  inst_num_existing_simplified:           0
% 2.47/1.01  inst_num_eq_res_simplified:             0
% 2.47/1.01  inst_num_child_elim:                    0
% 2.47/1.01  inst_num_of_dismatching_blockings:      787
% 2.47/1.01  inst_num_of_non_proper_insts:           1340
% 2.47/1.01  inst_num_of_duplicates:                 0
% 2.47/1.01  inst_inst_num_from_inst_to_res:         0
% 2.47/1.01  inst_dismatching_checking_time:         0.
% 2.47/1.01  
% 2.47/1.01  ------ Resolution
% 2.47/1.01  
% 2.47/1.01  res_num_of_clauses:                     0
% 2.47/1.01  res_num_in_passive:                     0
% 2.47/1.01  res_num_in_active:                      0
% 2.47/1.01  res_num_of_loops:                       111
% 2.47/1.01  res_forward_subset_subsumed:            126
% 2.47/1.01  res_backward_subset_subsumed:           2
% 2.47/1.01  res_forward_subsumed:                   0
% 2.47/1.01  res_backward_subsumed:                  0
% 2.47/1.01  res_forward_subsumption_resolution:     0
% 2.47/1.01  res_backward_subsumption_resolution:    0
% 2.47/1.01  res_clause_to_clause_subsumption:       862
% 2.47/1.01  res_orphan_elimination:                 0
% 2.47/1.01  res_tautology_del:                      156
% 2.47/1.01  res_num_eq_res_simplified:              0
% 2.47/1.01  res_num_sel_changes:                    0
% 2.47/1.01  res_moves_from_active_to_pass:          0
% 2.47/1.01  
% 2.47/1.01  ------ Superposition
% 2.47/1.01  
% 2.47/1.01  sup_time_total:                         0.
% 2.47/1.01  sup_time_generating:                    0.
% 2.47/1.01  sup_time_sim_full:                      0.
% 2.47/1.01  sup_time_sim_immed:                     0.
% 2.47/1.01  
% 2.47/1.01  sup_num_of_clauses:                     87
% 2.47/1.01  sup_num_in_active:                      82
% 2.47/1.01  sup_num_in_passive:                     5
% 2.47/1.01  sup_num_of_loops:                       89
% 2.47/1.01  sup_fw_superposition:                   159
% 2.47/1.01  sup_bw_superposition:                   22
% 2.47/1.01  sup_immediate_simplified:               86
% 2.47/1.01  sup_given_eliminated:                   0
% 2.47/1.01  comparisons_done:                       0
% 2.47/1.01  comparisons_avoided:                    0
% 2.47/1.01  
% 2.47/1.01  ------ Simplifications
% 2.47/1.01  
% 2.47/1.01  
% 2.47/1.01  sim_fw_subset_subsumed:                 20
% 2.47/1.01  sim_bw_subset_subsumed:                 18
% 2.47/1.01  sim_fw_subsumed:                        25
% 2.47/1.01  sim_bw_subsumed:                        0
% 2.47/1.01  sim_fw_subsumption_res:                 0
% 2.47/1.01  sim_bw_subsumption_res:                 0
% 2.47/1.01  sim_tautology_del:                      19
% 2.47/1.01  sim_eq_tautology_del:                   6
% 2.47/1.01  sim_eq_res_simp:                        25
% 2.47/1.01  sim_fw_demodulated:                     1
% 2.47/1.01  sim_bw_demodulated:                     4
% 2.47/1.01  sim_light_normalised:                   55
% 2.47/1.01  sim_joinable_taut:                      0
% 2.47/1.01  sim_joinable_simp:                      0
% 2.47/1.01  sim_ac_normalised:                      0
% 2.47/1.01  sim_smt_subsumption:                    0
% 2.47/1.01  
%------------------------------------------------------------------------------
