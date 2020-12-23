%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1884+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:47 EST 2020

% Result     : Theorem 9.85s
% Output     : CNFRefutation 9.85s
% Verified   : 
% Statistics : Number of formulae       :  398 (53981 expanded)
%              Number of clauses        :  295 (14849 expanded)
%              Number of leaves         :   24 (12352 expanded)
%              Depth                    :   42
%              Number of atoms          : 1943 (579605 expanded)
%              Number of equality atoms :  732 (76469 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   38 (   4 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( v4_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_tdlat_3(X2)
                    & ~ v2_struct_0(X2) )
                 => ( m1_pre_topc(X1,X2)
                   => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ) )
              & v1_tdlat_3(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ( v4_tex_2(X1,X0)
            <=> ( ! [X2] :
                    ( ( m1_pre_topc(X2,X0)
                      & v1_tdlat_3(X2)
                      & ~ v2_struct_0(X2) )
                   => ( m1_pre_topc(X1,X2)
                     => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ) )
                & v1_tdlat_3(X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_tex_2(X1,X0)
          <~> ( ! [X2] :
                  ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X2,X0)
                  | ~ v1_tdlat_3(X2)
                  | v2_struct_0(X2) )
              & v1_tdlat_3(X1) ) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_tex_2(X1,X0)
          <~> ( ! [X2] :
                  ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X2,X0)
                  | ~ v1_tdlat_3(X2)
                  | v2_struct_0(X2) )
              & v1_tdlat_3(X1) ) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f62,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X2,X0)
                & v1_tdlat_3(X2)
                & ~ v2_struct_0(X2) )
            | ~ v1_tdlat_3(X1)
            | ~ v4_tex_2(X1,X0) )
          & ( ( ! [X2] :
                  ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X2,X0)
                  | ~ v1_tdlat_3(X2)
                  | v2_struct_0(X2) )
              & v1_tdlat_3(X1) )
            | v4_tex_2(X1,X0) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f63,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X2,X0)
                & v1_tdlat_3(X2)
                & ~ v2_struct_0(X2) )
            | ~ v1_tdlat_3(X1)
            | ~ v4_tex_2(X1,X0) )
          & ( ( ! [X2] :
                  ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X2,X0)
                  | ~ v1_tdlat_3(X2)
                  | v2_struct_0(X2) )
              & v1_tdlat_3(X1) )
            | v4_tex_2(X1,X0) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f62])).

fof(f64,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X2,X0)
                & v1_tdlat_3(X2)
                & ~ v2_struct_0(X2) )
            | ~ v1_tdlat_3(X1)
            | ~ v4_tex_2(X1,X0) )
          & ( ( ! [X3] :
                  ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  | ~ m1_pre_topc(X1,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_tdlat_3(X3)
                  | v2_struct_0(X3) )
              & v1_tdlat_3(X1) )
            | v4_tex_2(X1,X0) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f63])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
          & m1_pre_topc(X1,X2)
          & m1_pre_topc(X2,X0)
          & v1_tdlat_3(X2)
          & ~ v2_struct_0(X2) )
     => ( g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
        & m1_pre_topc(X1,sK7)
        & m1_pre_topc(sK7,X0)
        & v1_tdlat_3(sK7)
        & ~ v2_struct_0(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X2,X0)
                & v1_tdlat_3(X2)
                & ~ v2_struct_0(X2) )
            | ~ v1_tdlat_3(X1)
            | ~ v4_tex_2(X1,X0) )
          & ( ( ! [X3] :
                  ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  | ~ m1_pre_topc(X1,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_tdlat_3(X3)
                  | v2_struct_0(X3) )
              & v1_tdlat_3(X1) )
            | v4_tex_2(X1,X0) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ( ? [X2] :
              ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(sK6,X2)
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & ~ v2_struct_0(X2) )
          | ~ v1_tdlat_3(sK6)
          | ~ v4_tex_2(sK6,X0) )
        & ( ( ! [X3] :
                ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                | ~ m1_pre_topc(sK6,X3)
                | ~ m1_pre_topc(X3,X0)
                | ~ v1_tdlat_3(X3)
                | v2_struct_0(X3) )
            & v1_tdlat_3(sK6) )
          | v4_tex_2(sK6,X0) )
        & m1_pre_topc(sK6,X0)
        & ~ v2_struct_0(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X2,X0)
                  & v1_tdlat_3(X2)
                  & ~ v2_struct_0(X2) )
              | ~ v1_tdlat_3(X1)
              | ~ v4_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                    | ~ m1_pre_topc(X1,X3)
                    | ~ m1_pre_topc(X3,X0)
                    | ~ v1_tdlat_3(X3)
                    | v2_struct_0(X3) )
                & v1_tdlat_3(X1) )
              | v4_tex_2(X1,X0) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X2,sK5)
                & v1_tdlat_3(X2)
                & ~ v2_struct_0(X2) )
            | ~ v1_tdlat_3(X1)
            | ~ v4_tex_2(X1,sK5) )
          & ( ( ! [X3] :
                  ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  | ~ m1_pre_topc(X1,X3)
                  | ~ m1_pre_topc(X3,sK5)
                  | ~ v1_tdlat_3(X3)
                  | v2_struct_0(X3) )
              & v1_tdlat_3(X1) )
            | v4_tex_2(X1,sK5) )
          & m1_pre_topc(X1,sK5)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK5)
      & v2_pre_topc(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,
    ( ( ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) != g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))
        & m1_pre_topc(sK6,sK7)
        & m1_pre_topc(sK7,sK5)
        & v1_tdlat_3(sK7)
        & ~ v2_struct_0(sK7) )
      | ~ v1_tdlat_3(sK6)
      | ~ v4_tex_2(sK6,sK5) )
    & ( ( ! [X3] :
            ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
            | ~ m1_pre_topc(sK6,X3)
            | ~ m1_pre_topc(X3,sK5)
            | ~ v1_tdlat_3(X3)
            | v2_struct_0(X3) )
        & v1_tdlat_3(sK6) )
      | v4_tex_2(sK6,sK5) )
    & m1_pre_topc(sK6,sK5)
    & ~ v2_struct_0(sK6)
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f64,f67,f66,f65])).

fof(f106,plain,(
    m1_pre_topc(sK6,sK5) ),
    inference(cnf_transformation,[],[f68])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f79,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f104,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f68])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f80,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f78,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f69,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
                  | ~ m1_pre_topc(X1,X2) )
                & ( m1_pre_topc(X1,X2)
                  | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f103,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f68])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f95,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_tex_2(X2,X0) )
                   => X1 = X2 ) )
              & v2_tex_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f46])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r1_tarski(X1,X2)
          & v2_tex_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK0(X0,X1) != X1
        & r1_tarski(X1,sK0(X0,X1))
        & v2_tex_2(sK0(X0,X1),X0)
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ( sK0(X0,X1) != X1
                & r1_tarski(X1,sK0(X0,X1))
                & v2_tex_2(sK0(X0,X1),X0)
                & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f47,f48])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_tdlat_3(X2)
                    & v1_pre_topc(X2)
                    & ~ v2_struct_0(X2) )
                 => u1_struct_0(X2) != X1 )
              & v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f57,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & v1_tdlat_3(X2)
          & v1_pre_topc(X2)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK4(X0,X1)) = X1
        & m1_pre_topc(sK4(X0,X1),X0)
        & v1_tdlat_3(sK4(X0,X1))
        & v1_pre_topc(sK4(X0,X1))
        & ~ v2_struct_0(sK4(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK4(X0,X1)) = X1
            & m1_pre_topc(sK4(X0,X1),X0)
            & v1_tdlat_3(sK4(X0,X1))
            & v1_pre_topc(sK4(X0,X1))
            & ~ v2_struct_0(sK4(X0,X1)) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f57])).

fof(f92,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK4(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f102,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f68])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | v2_tex_2(sK0(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f90,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(sK4(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f18,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v2_tex_2(X2,X0)
                <=> v1_tdlat_3(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_tex_2(X2,X0)
                  | ~ v1_tdlat_3(X1) )
                & ( v1_tdlat_3(X1)
                  | ~ v2_tex_2(X2,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v1_tdlat_3(X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f114,plain,(
    ! [X0,X1] :
      ( v2_tex_2(u1_struct_0(X1),X0)
      | ~ v1_tdlat_3(X1)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f88])).

fof(f93,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK4(X0,X1)) = X1
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f105,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f68])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v3_tex_2(X2,X0)
                <=> v4_tex_2(X1,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tex_2(X2,X0)
              <=> v4_tex_2(X1,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tex_2(X2,X0)
              <=> v4_tex_2(X1,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_tex_2(X2,X0)
                  | ~ v4_tex_2(X1,X0) )
                & ( v4_tex_2(X1,X0)
                  | ~ v3_tex_2(X2,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( v3_tex_2(X2,X0)
      | ~ v4_tex_2(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f116,plain,(
    ! [X0,X1] :
      ( v3_tex_2(u1_struct_0(X1),X0)
      | ~ v4_tex_2(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f99])).

fof(f107,plain,
    ( v1_tdlat_3(sK6)
    | v4_tex_2(sK6,sK5) ),
    inference(cnf_transformation,[],[f68])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( v4_tex_2(X1,X0)
      | ~ v3_tex_2(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f117,plain,(
    ! [X0,X1] :
      ( v4_tex_2(X1,X0)
      | ~ v3_tex_2(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f98])).

fof(f109,plain,
    ( ~ v2_struct_0(sK7)
    | ~ v1_tdlat_3(sK6)
    | ~ v4_tex_2(sK6,sK5) ),
    inference(cnf_transformation,[],[f68])).

fof(f110,plain,
    ( v1_tdlat_3(sK7)
    | ~ v1_tdlat_3(sK6)
    | ~ v4_tex_2(sK6,sK5) ),
    inference(cnf_transformation,[],[f68])).

fof(f111,plain,
    ( m1_pre_topc(sK7,sK5)
    | ~ v1_tdlat_3(sK6)
    | ~ v4_tex_2(sK6,sK5) ),
    inference(cnf_transformation,[],[f68])).

fof(f112,plain,
    ( m1_pre_topc(sK6,sK7)
    | ~ v1_tdlat_3(sK6)
    | ~ v4_tex_2(sK6,sK5) ),
    inference(cnf_transformation,[],[f68])).

fof(f113,plain,
    ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) != g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))
    | ~ v1_tdlat_3(sK6)
    | ~ v4_tex_2(sK6,sK5) ),
    inference(cnf_transformation,[],[f68])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | r1_tarski(X1,sK0(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | sK0(X0,X1) != X1
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ v2_tex_2(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f115,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ v2_tex_2(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f87])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( X1 = X3
      | ~ r1_tarski(X1,X3)
      | ~ v2_tex_2(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( u1_struct_0(X1) = u1_struct_0(X2)
               => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              | u1_struct_0(X1) != u1_struct_0(X2)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              | u1_struct_0(X1) != u1_struct_0(X2)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
      | u1_struct_0(X1) != u1_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f108,plain,(
    ! [X3] :
      ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
      | ~ m1_pre_topc(sK6,X3)
      | ~ m1_pre_topc(X3,sK5)
      | ~ v1_tdlat_3(X3)
      | v2_struct_0(X3)
      | v4_tex_2(sK6,sK5) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f91,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(sK4(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK4(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_40,negated_conjecture,
    ( m1_pre_topc(sK6,sK5) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_4250,plain,
    ( m1_pre_topc(sK6,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_4269,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_6007,plain,
    ( l1_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_4250,c_4269])).

cnf(c_42,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_47,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_49,plain,
    ( m1_pre_topc(sK6,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_4813,plain,
    ( ~ m1_pre_topc(X0,sK5)
    | l1_pre_topc(X0)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_4814,plain,
    ( m1_pre_topc(X0,sK5) != iProver_top
    | l1_pre_topc(X0) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4813])).

cnf(c_4816,plain,
    ( m1_pre_topc(sK6,sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK6) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4814])).

cnf(c_6118,plain,
    ( l1_pre_topc(sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6007,c_47,c_49,c_4816])).

cnf(c_11,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_4268,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_4271,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | l1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5898,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4268,c_4271])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_4278,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_8950,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5898,c_4278])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | v1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_4270,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | v1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5885,plain,
    ( l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4268,c_4270])).

cnf(c_11224,plain,
    ( l1_pre_topc(X0) != iProver_top
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8950,c_5885])).

cnf(c_11225,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_11224])).

cnf(c_11232,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) ),
    inference(superposition,[status(thm)],[c_6118,c_11225])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_4263,plain,
    ( X0 = X1
    | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_11615,plain,
    ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) != g1_pre_topc(X0,X1)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_11232,c_4263])).

cnf(c_12135,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(sK6)
    | m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_11615])).

cnf(c_116,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_118,plain,
    ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) = iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_116])).

cnf(c_18793,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12135,c_47,c_49,c_118,c_4816])).

cnf(c_18805,plain,
    ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) ),
    inference(demodulation,[status(thm)],[c_18793,c_11232])).

cnf(c_4248,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_11231,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) ),
    inference(superposition,[status(thm)],[c_4248,c_11225])).

cnf(c_11366,plain,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != g1_pre_topc(X0,X1)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = X0
    | m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_11231,c_4263])).

cnf(c_11729,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = u1_struct_0(sK5)
    | m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_11366])).

cnf(c_11365,plain,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != g1_pre_topc(X0,X1)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_11231,c_4263])).

cnf(c_11646,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = u1_struct_0(sK5)
    | m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_11365])).

cnf(c_12482,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = u1_struct_0(sK5)
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4268,c_11646])).

cnf(c_12558,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = u1_struct_0(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11729,c_47,c_12482])).

cnf(c_27,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_43,negated_conjecture,
    ( v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_709,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ l1_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_43])).

cnf(c_710,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,sK5)
    | ~ m1_pre_topc(X0,sK5)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_709])).

cnf(c_714,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,sK5)
    | ~ m1_pre_topc(X1,sK5)
    | ~ m1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_710,c_42])).

cnf(c_715,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK5)
    | ~ m1_pre_topc(X1,sK5)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(renaming,[status(thm)],[c_714])).

cnf(c_4239,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,sK5) != iProver_top
    | m1_pre_topc(X1,sK5) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_715])).

cnf(c_12624,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | m1_pre_topc(X0,sK5) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK5) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_12558,c_4239])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_6429,plain,
    ( ~ m1_pre_topc(X0,sK5)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_6430,plain,
    ( m1_pre_topc(X0,sK5) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6429])).

cnf(c_26,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_4706,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_8594,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(sK5))
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_4706])).

cnf(c_8595,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(sK5)) = iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8594])).

cnf(c_13153,plain,
    ( m1_pre_topc(X0,sK5) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12624,c_47,c_6430,c_8595])).

cnf(c_25,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_4261,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_4274,plain,
    ( v2_tex_2(X0,X1) != iProver_top
    | v3_tex_2(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_21,plain,
    ( m1_pre_topc(sK4(X0,X1),X0)
    | ~ v2_tex_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v1_xboole_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_661,plain,
    ( m1_pre_topc(sK4(X0,X1),X0)
    | ~ v2_tex_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | v1_xboole_0(X1)
    | ~ l1_pre_topc(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_43])).

cnf(c_662,plain,
    ( m1_pre_topc(sK4(sK5,X0),sK5)
    | ~ v2_tex_2(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | v2_struct_0(sK5)
    | v1_xboole_0(X0)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_661])).

cnf(c_44,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_666,plain,
    ( v1_xboole_0(X0)
    | m1_pre_topc(sK4(sK5,X0),sK5)
    | ~ v2_tex_2(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_662,c_44,c_42])).

cnf(c_667,plain,
    ( m1_pre_topc(sK4(sK5,X0),sK5)
    | ~ v2_tex_2(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_666])).

cnf(c_4241,plain,
    ( m1_pre_topc(sK4(sK5,X0),sK5) = iProver_top
    | v2_tex_2(X0,sK5) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_667])).

cnf(c_7338,plain,
    ( m1_pre_topc(sK4(sK5,sK0(sK5,X0)),sK5) = iProver_top
    | v2_tex_2(X0,sK5) != iProver_top
    | v2_tex_2(sK0(sK5,X0),sK5) != iProver_top
    | v3_tex_2(X0,sK5) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v1_xboole_0(sK0(sK5,X0)) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4274,c_4241])).

cnf(c_4,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(sK0(X1,X0),X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_4937,plain,
    ( ~ v2_tex_2(X0,sK5)
    | v2_tex_2(sK0(sK5,X0),sK5)
    | v3_tex_2(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_4938,plain,
    ( v2_tex_2(X0,sK5) != iProver_top
    | v2_tex_2(sK0(sK5,X0),sK5) = iProver_top
    | v3_tex_2(X0,sK5) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4937])).

cnf(c_7666,plain,
    ( v1_xboole_0(sK0(sK5,X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v3_tex_2(X0,sK5) = iProver_top
    | m1_pre_topc(sK4(sK5,sK0(sK5,X0)),sK5) = iProver_top
    | v2_tex_2(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7338,c_47,c_4938])).

cnf(c_7667,plain,
    ( m1_pre_topc(sK4(sK5,sK0(sK5,X0)),sK5) = iProver_top
    | v2_tex_2(X0,sK5) != iProver_top
    | v3_tex_2(X0,sK5) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v1_xboole_0(sK0(sK5,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_7666])).

cnf(c_7672,plain,
    ( v2_tex_2(X0,sK5) != iProver_top
    | v3_tex_2(X0,sK5) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v1_xboole_0(sK0(sK5,X0)) = iProver_top
    | l1_pre_topc(sK4(sK5,sK0(sK5,X0))) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_7667,c_4269])).

cnf(c_8673,plain,
    ( l1_pre_topc(sK4(sK5,sK0(sK5,X0))) = iProver_top
    | v1_xboole_0(sK0(sK5,X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v3_tex_2(X0,sK5) = iProver_top
    | v2_tex_2(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7672,c_47])).

cnf(c_8674,plain,
    ( v2_tex_2(X0,sK5) != iProver_top
    | v3_tex_2(X0,sK5) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v1_xboole_0(sK0(sK5,X0)) = iProver_top
    | l1_pre_topc(sK4(sK5,sK0(sK5,X0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_8673])).

cnf(c_8679,plain,
    ( g1_pre_topc(u1_struct_0(sK4(sK5,sK0(sK5,X0))),u1_pre_topc(sK4(sK5,sK0(sK5,X0)))) = sK4(sK5,sK0(sK5,X0))
    | v2_tex_2(X0,sK5) != iProver_top
    | v3_tex_2(X0,sK5) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v1_xboole_0(sK0(sK5,X0)) = iProver_top
    | v1_pre_topc(sK4(sK5,sK0(sK5,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8674,c_4278])).

cnf(c_23,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(sK4(X1,X0)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_757,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(sK4(X1,X0))
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_43])).

cnf(c_758,plain,
    ( ~ v2_tex_2(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | v2_struct_0(sK5)
    | v1_xboole_0(X0)
    | ~ l1_pre_topc(sK5)
    | v1_pre_topc(sK4(sK5,X0)) ),
    inference(unflattening,[status(thm)],[c_757])).

cnf(c_762,plain,
    ( v1_xboole_0(X0)
    | ~ v2_tex_2(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | v1_pre_topc(sK4(sK5,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_758,c_44,c_42])).

cnf(c_763,plain,
    ( ~ v2_tex_2(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | v1_xboole_0(X0)
    | v1_pre_topc(sK4(sK5,X0)) ),
    inference(renaming,[status(thm)],[c_762])).

cnf(c_4237,plain,
    ( v2_tex_2(X0,sK5) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_pre_topc(sK4(sK5,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_763])).

cnf(c_7339,plain,
    ( v2_tex_2(X0,sK5) != iProver_top
    | v2_tex_2(sK0(sK5,X0),sK5) != iProver_top
    | v3_tex_2(X0,sK5) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v1_xboole_0(sK0(sK5,X0)) = iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v1_pre_topc(sK4(sK5,sK0(sK5,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4274,c_4237])).

cnf(c_7491,plain,
    ( v1_xboole_0(sK0(sK5,X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v3_tex_2(X0,sK5) = iProver_top
    | v2_tex_2(X0,sK5) != iProver_top
    | v1_pre_topc(sK4(sK5,sK0(sK5,X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7339,c_47,c_4938])).

cnf(c_7492,plain,
    ( v2_tex_2(X0,sK5) != iProver_top
    | v3_tex_2(X0,sK5) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v1_xboole_0(sK0(sK5,X0)) = iProver_top
    | v1_pre_topc(sK4(sK5,sK0(sK5,X0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_7491])).

cnf(c_17910,plain,
    ( v1_xboole_0(sK0(sK5,X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v3_tex_2(X0,sK5) = iProver_top
    | v2_tex_2(X0,sK5) != iProver_top
    | g1_pre_topc(u1_struct_0(sK4(sK5,sK0(sK5,X0))),u1_pre_topc(sK4(sK5,sK0(sK5,X0)))) = sK4(sK5,sK0(sK5,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8679,c_7492])).

cnf(c_17911,plain,
    ( g1_pre_topc(u1_struct_0(sK4(sK5,sK0(sK5,X0))),u1_pre_topc(sK4(sK5,sK0(sK5,X0)))) = sK4(sK5,sK0(sK5,X0))
    | v2_tex_2(X0,sK5) != iProver_top
    | v3_tex_2(X0,sK5) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v1_xboole_0(sK0(sK5,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_17910])).

cnf(c_17916,plain,
    ( g1_pre_topc(u1_struct_0(sK4(sK5,sK0(sK5,X0))),u1_pre_topc(sK4(sK5,sK0(sK5,X0)))) = sK4(sK5,sK0(sK5,X0))
    | r1_tarski(X0,u1_struct_0(sK5)) != iProver_top
    | v2_tex_2(X0,sK5) != iProver_top
    | v3_tex_2(X0,sK5) = iProver_top
    | v1_xboole_0(sK0(sK5,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4261,c_17911])).

cnf(c_18030,plain,
    ( g1_pre_topc(u1_struct_0(sK4(sK5,sK0(sK5,u1_struct_0(X0)))),u1_pre_topc(sK4(sK5,sK0(sK5,u1_struct_0(X0))))) = sK4(sK5,sK0(sK5,u1_struct_0(X0)))
    | m1_pre_topc(X0,sK5) != iProver_top
    | v2_tex_2(u1_struct_0(X0),sK5) != iProver_top
    | v3_tex_2(u1_struct_0(X0),sK5) = iProver_top
    | v1_xboole_0(sK0(sK5,u1_struct_0(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_13153,c_17916])).

cnf(c_32,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_4258,plain,
    ( X0 = X1
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_18407,plain,
    ( sK0(sK5,u1_struct_0(X0)) = X1
    | g1_pre_topc(u1_struct_0(sK4(sK5,sK0(sK5,u1_struct_0(X0)))),u1_pre_topc(sK4(sK5,sK0(sK5,u1_struct_0(X0))))) = sK4(sK5,sK0(sK5,u1_struct_0(X0)))
    | m1_pre_topc(X0,sK5) != iProver_top
    | v2_tex_2(u1_struct_0(X0),sK5) != iProver_top
    | v3_tex_2(u1_struct_0(X0),sK5) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_18030,c_4258])).

cnf(c_26650,plain,
    ( sK0(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = X0
    | g1_pre_topc(u1_struct_0(sK4(sK5,sK0(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))),u1_pre_topc(sK4(sK5,sK0(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))))) = sK4(sK5,sK0(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK5) != iProver_top
    | v2_tex_2(u1_struct_0(sK6),sK5) != iProver_top
    | v3_tex_2(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),sK5) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_18793,c_18407])).

cnf(c_18,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_tex_2(u1_struct_0(X0),X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v1_tdlat_3(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_283,plain,
    ( v2_tex_2(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v1_tdlat_3(X0)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_17])).

cnf(c_284,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_tex_2(u1_struct_0(X0),X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X0)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_283])).

cnf(c_4243,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | v2_tex_2(u1_struct_0(X0),X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v1_tdlat_3(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_284])).

cnf(c_4262,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_20,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(sK4(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_805,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(sK4(X1,X0)) = X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_43])).

cnf(c_806,plain,
    ( ~ v2_tex_2(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | v2_struct_0(sK5)
    | v1_xboole_0(X0)
    | ~ l1_pre_topc(sK5)
    | u1_struct_0(sK4(sK5,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_805])).

cnf(c_810,plain,
    ( v1_xboole_0(X0)
    | ~ v2_tex_2(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | u1_struct_0(sK4(sK5,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_806,c_44,c_42])).

cnf(c_811,plain,
    ( ~ v2_tex_2(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | v1_xboole_0(X0)
    | u1_struct_0(sK4(sK5,X0)) = X0 ),
    inference(renaming,[status(thm)],[c_810])).

cnf(c_4235,plain,
    ( u1_struct_0(sK4(sK5,X0)) = X0
    | v2_tex_2(X0,sK5) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_811])).

cnf(c_6391,plain,
    ( u1_struct_0(sK4(sK5,u1_struct_0(X0))) = u1_struct_0(X0)
    | m1_pre_topc(X0,sK5) != iProver_top
    | v2_tex_2(u1_struct_0(X0),sK5) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4262,c_4235])).

cnf(c_7475,plain,
    ( v1_xboole_0(u1_struct_0(X0)) = iProver_top
    | v2_tex_2(u1_struct_0(X0),sK5) != iProver_top
    | m1_pre_topc(X0,sK5) != iProver_top
    | u1_struct_0(sK4(sK5,u1_struct_0(X0))) = u1_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6391,c_47])).

cnf(c_7476,plain,
    ( u1_struct_0(sK4(sK5,u1_struct_0(X0))) = u1_struct_0(X0)
    | m1_pre_topc(X0,sK5) != iProver_top
    | v2_tex_2(u1_struct_0(X0),sK5) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_7475])).

cnf(c_7481,plain,
    ( u1_struct_0(sK4(sK5,u1_struct_0(X0))) = u1_struct_0(X0)
    | m1_pre_topc(X0,sK5) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v1_tdlat_3(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4243,c_7476])).

cnf(c_45,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_8424,plain,
    ( v1_xboole_0(u1_struct_0(X0)) = iProver_top
    | v1_tdlat_3(X0) != iProver_top
    | u1_struct_0(sK4(sK5,u1_struct_0(X0))) = u1_struct_0(X0)
    | m1_pre_topc(X0,sK5) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7481,c_45,c_47])).

cnf(c_8425,plain,
    ( u1_struct_0(sK4(sK5,u1_struct_0(X0))) = u1_struct_0(X0)
    | m1_pre_topc(X0,sK5) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v1_tdlat_3(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_8424])).

cnf(c_8431,plain,
    ( u1_struct_0(sK4(sK5,u1_struct_0(sK6))) = u1_struct_0(sK6)
    | v2_struct_0(sK6) = iProver_top
    | v1_tdlat_3(sK6) != iProver_top
    | v1_xboole_0(u1_struct_0(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4250,c_8425])).

cnf(c_41,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_48,plain,
    ( v2_struct_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_29,plain,
    ( ~ v4_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v3_tex_2(u1_struct_0(X0),X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_260,plain,
    ( v3_tex_2(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v4_tex_2(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_29,c_17])).

cnf(c_261,plain,
    ( ~ v4_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v3_tex_2(u1_struct_0(X0),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_260])).

cnf(c_39,negated_conjecture,
    ( v4_tex_2(sK6,sK5)
    | v1_tdlat_3(sK6) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1425,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v3_tex_2(u1_struct_0(X0),X1)
    | v2_struct_0(X1)
    | v1_tdlat_3(sK6)
    | ~ l1_pre_topc(X1)
    | sK5 != X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_261,c_39])).

cnf(c_1426,plain,
    ( ~ m1_pre_topc(sK6,sK5)
    | v3_tex_2(u1_struct_0(sK6),sK5)
    | v2_struct_0(sK5)
    | v1_tdlat_3(sK6)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_1425])).

cnf(c_1428,plain,
    ( v1_tdlat_3(sK6)
    | v3_tex_2(u1_struct_0(sK6),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1426,c_44,c_42,c_40])).

cnf(c_1429,plain,
    ( v3_tex_2(u1_struct_0(sK6),sK5)
    | v1_tdlat_3(sK6) ),
    inference(renaming,[status(thm)],[c_1428])).

cnf(c_1430,plain,
    ( v3_tex_2(u1_struct_0(sK6),sK5) = iProver_top
    | v1_tdlat_3(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1429])).

cnf(c_7,plain,
    ( v2_tex_2(X0,X1)
    | ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_4417,plain,
    ( v2_tex_2(X0,sK5)
    | ~ v3_tex_2(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_5138,plain,
    ( v2_tex_2(u1_struct_0(X0),sK5)
    | ~ v3_tex_2(u1_struct_0(X0),sK5)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_4417])).

cnf(c_5139,plain,
    ( v2_tex_2(u1_struct_0(X0),sK5) = iProver_top
    | v3_tex_2(u1_struct_0(X0),sK5) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5138])).

cnf(c_5141,plain,
    ( v2_tex_2(u1_struct_0(sK6),sK5) = iProver_top
    | v3_tex_2(u1_struct_0(sK6),sK5) != iProver_top
    | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5139])).

cnf(c_6432,plain,
    ( m1_pre_topc(sK6,sK5) != iProver_top
    | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6430])).

cnf(c_8384,plain,
    ( ~ v2_tex_2(u1_struct_0(sK6),sK5)
    | ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK5)))
    | v1_xboole_0(u1_struct_0(sK6))
    | u1_struct_0(sK4(sK5,u1_struct_0(sK6))) = u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_811])).

cnf(c_8397,plain,
    ( u1_struct_0(sK4(sK5,u1_struct_0(sK6))) = u1_struct_0(sK6)
    | v2_tex_2(u1_struct_0(sK6),sK5) != iProver_top
    | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8384])).

cnf(c_8449,plain,
    ( u1_struct_0(sK4(sK5,u1_struct_0(sK6))) = u1_struct_0(sK6)
    | v1_xboole_0(u1_struct_0(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8431,c_47,c_48,c_49,c_1430,c_5141,c_6432,c_8397])).

cnf(c_7342,plain,
    ( u1_struct_0(sK4(sK5,sK0(sK5,X0))) = sK0(sK5,X0)
    | v2_tex_2(X0,sK5) != iProver_top
    | v2_tex_2(sK0(sK5,X0),sK5) != iProver_top
    | v3_tex_2(X0,sK5) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v1_xboole_0(sK0(sK5,X0)) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4274,c_4235])).

cnf(c_8011,plain,
    ( v1_xboole_0(sK0(sK5,X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v3_tex_2(X0,sK5) = iProver_top
    | u1_struct_0(sK4(sK5,sK0(sK5,X0))) = sK0(sK5,X0)
    | v2_tex_2(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7342,c_47,c_4938])).

cnf(c_8012,plain,
    ( u1_struct_0(sK4(sK5,sK0(sK5,X0))) = sK0(sK5,X0)
    | v2_tex_2(X0,sK5) != iProver_top
    | v3_tex_2(X0,sK5) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v1_xboole_0(sK0(sK5,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_8011])).

cnf(c_8017,plain,
    ( u1_struct_0(sK4(sK5,sK0(sK5,X0))) = sK0(sK5,X0)
    | r1_tarski(X0,u1_struct_0(sK5)) != iProver_top
    | v2_tex_2(X0,sK5) != iProver_top
    | v3_tex_2(X0,sK5) = iProver_top
    | v1_xboole_0(sK0(sK5,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4261,c_8012])).

cnf(c_8361,plain,
    ( u1_struct_0(sK4(sK5,sK0(sK5,u1_struct_0(X0)))) = sK0(sK5,u1_struct_0(X0))
    | m1_pre_topc(X0,sK5) != iProver_top
    | m1_pre_topc(sK5,sK5) != iProver_top
    | v2_tex_2(u1_struct_0(X0),sK5) != iProver_top
    | v3_tex_2(u1_struct_0(X0),sK5) = iProver_top
    | v1_xboole_0(sK0(sK5,u1_struct_0(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4239,c_8017])).

cnf(c_8020,plain,
    ( u1_struct_0(sK4(sK5,sK0(sK5,u1_struct_0(X0)))) = sK0(sK5,u1_struct_0(X0))
    | m1_pre_topc(X0,sK5) != iProver_top
    | v2_tex_2(u1_struct_0(X0),sK5) != iProver_top
    | v3_tex_2(u1_struct_0(X0),sK5) = iProver_top
    | v1_xboole_0(sK0(sK5,u1_struct_0(X0))) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4262,c_8012])).

cnf(c_8367,plain,
    ( m1_pre_topc(X0,sK5) != iProver_top
    | u1_struct_0(sK4(sK5,sK0(sK5,u1_struct_0(X0)))) = sK0(sK5,u1_struct_0(X0))
    | v2_tex_2(u1_struct_0(X0),sK5) != iProver_top
    | v3_tex_2(u1_struct_0(X0),sK5) = iProver_top
    | v1_xboole_0(sK0(sK5,u1_struct_0(X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8361,c_47,c_8020])).

cnf(c_8368,plain,
    ( u1_struct_0(sK4(sK5,sK0(sK5,u1_struct_0(X0)))) = sK0(sK5,u1_struct_0(X0))
    | m1_pre_topc(X0,sK5) != iProver_top
    | v2_tex_2(u1_struct_0(X0),sK5) != iProver_top
    | v3_tex_2(u1_struct_0(X0),sK5) = iProver_top
    | v1_xboole_0(sK0(sK5,u1_struct_0(X0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_8367])).

cnf(c_8373,plain,
    ( sK0(sK5,u1_struct_0(X0)) = X1
    | u1_struct_0(sK4(sK5,sK0(sK5,u1_struct_0(X0)))) = sK0(sK5,u1_struct_0(X0))
    | m1_pre_topc(X0,sK5) != iProver_top
    | v2_tex_2(u1_struct_0(X0),sK5) != iProver_top
    | v3_tex_2(u1_struct_0(X0),sK5) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_8368,c_4258])).

cnf(c_8759,plain,
    ( sK0(sK5,u1_struct_0(X0)) = X1
    | u1_struct_0(sK4(sK5,sK0(sK5,u1_struct_0(X0)))) = sK0(sK5,u1_struct_0(X0))
    | m1_pre_topc(X0,sK5) != iProver_top
    | v3_tex_2(u1_struct_0(X0),sK5) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v1_tdlat_3(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4243,c_8373])).

cnf(c_20231,plain,
    ( v1_xboole_0(X1) != iProver_top
    | v1_tdlat_3(X0) != iProver_top
    | sK0(sK5,u1_struct_0(X0)) = X1
    | u1_struct_0(sK4(sK5,sK0(sK5,u1_struct_0(X0)))) = sK0(sK5,u1_struct_0(X0))
    | m1_pre_topc(X0,sK5) != iProver_top
    | v3_tex_2(u1_struct_0(X0),sK5) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8759,c_45,c_47])).

cnf(c_20232,plain,
    ( sK0(sK5,u1_struct_0(X0)) = X1
    | u1_struct_0(sK4(sK5,sK0(sK5,u1_struct_0(X0)))) = sK0(sK5,u1_struct_0(X0))
    | m1_pre_topc(X0,sK5) != iProver_top
    | v3_tex_2(u1_struct_0(X0),sK5) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v1_tdlat_3(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_20231])).

cnf(c_20238,plain,
    ( sK0(sK5,u1_struct_0(X0)) = u1_struct_0(sK6)
    | u1_struct_0(sK4(sK5,sK0(sK5,u1_struct_0(X0)))) = sK0(sK5,u1_struct_0(X0))
    | u1_struct_0(sK4(sK5,u1_struct_0(sK6))) = u1_struct_0(sK6)
    | m1_pre_topc(X0,sK5) != iProver_top
    | v3_tex_2(u1_struct_0(X0),sK5) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v1_tdlat_3(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8449,c_20232])).

cnf(c_30,plain,
    ( v4_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v3_tex_2(u1_struct_0(X0),X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_253,plain,
    ( ~ v3_tex_2(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | v4_tex_2(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_30,c_17])).

cnf(c_254,plain,
    ( v4_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v3_tex_2(u1_struct_0(X0),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_253])).

cnf(c_4246,plain,
    ( v4_tex_2(X0,X1) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | v3_tex_2(u1_struct_0(X0),X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_254])).

cnf(c_20701,plain,
    ( sK0(sK5,u1_struct_0(X0)) = u1_struct_0(sK6)
    | u1_struct_0(sK4(sK5,sK0(sK5,u1_struct_0(X0)))) = sK0(sK5,u1_struct_0(X0))
    | u1_struct_0(sK4(sK5,u1_struct_0(sK6))) = u1_struct_0(sK6)
    | v4_tex_2(X0,sK5) = iProver_top
    | m1_pre_topc(X0,sK5) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v1_tdlat_3(X0) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_20238,c_4246])).

cnf(c_22772,plain,
    ( v1_tdlat_3(X0) != iProver_top
    | sK0(sK5,u1_struct_0(X0)) = u1_struct_0(sK6)
    | u1_struct_0(sK4(sK5,sK0(sK5,u1_struct_0(X0)))) = sK0(sK5,u1_struct_0(X0))
    | u1_struct_0(sK4(sK5,u1_struct_0(sK6))) = u1_struct_0(sK6)
    | v4_tex_2(X0,sK5) = iProver_top
    | m1_pre_topc(X0,sK5) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20701,c_45,c_47])).

cnf(c_22773,plain,
    ( sK0(sK5,u1_struct_0(X0)) = u1_struct_0(sK6)
    | u1_struct_0(sK4(sK5,sK0(sK5,u1_struct_0(X0)))) = sK0(sK5,u1_struct_0(X0))
    | u1_struct_0(sK4(sK5,u1_struct_0(sK6))) = u1_struct_0(sK6)
    | v4_tex_2(X0,sK5) = iProver_top
    | m1_pre_topc(X0,sK5) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v1_tdlat_3(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_22772])).

cnf(c_22779,plain,
    ( sK0(sK5,u1_struct_0(sK6)) = u1_struct_0(sK6)
    | u1_struct_0(sK4(sK5,sK0(sK5,u1_struct_0(sK6)))) = sK0(sK5,u1_struct_0(sK6))
    | u1_struct_0(sK4(sK5,u1_struct_0(sK6))) = u1_struct_0(sK6)
    | v4_tex_2(sK6,sK5) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v1_tdlat_3(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_4250,c_22773])).

cnf(c_37,negated_conjecture,
    ( ~ v4_tex_2(sK6,sK5)
    | ~ v2_struct_0(sK7)
    | ~ v1_tdlat_3(sK6) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_36,negated_conjecture,
    ( ~ v4_tex_2(sK6,sK5)
    | v1_tdlat_3(sK7)
    | ~ v1_tdlat_3(sK6) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_35,negated_conjecture,
    ( ~ v4_tex_2(sK6,sK5)
    | m1_pre_topc(sK7,sK5)
    | ~ v1_tdlat_3(sK6) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_34,negated_conjecture,
    ( ~ v4_tex_2(sK6,sK5)
    | m1_pre_topc(sK6,sK7)
    | ~ v1_tdlat_3(sK6) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_33,negated_conjecture,
    ( ~ v4_tex_2(sK6,sK5)
    | ~ v1_tdlat_3(sK6)
    | g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) != g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_3260,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_3275,plain,
    ( u1_struct_0(sK6) = u1_struct_0(sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_3260])).

cnf(c_3258,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3291,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_3258])).

cnf(c_4402,plain,
    ( v4_tex_2(X0,sK5)
    | ~ m1_pre_topc(X0,sK5)
    | ~ v3_tex_2(u1_struct_0(X0),sK5)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_254])).

cnf(c_4412,plain,
    ( v4_tex_2(sK6,sK5)
    | ~ m1_pre_topc(sK6,sK5)
    | ~ v3_tex_2(u1_struct_0(sK6),sK5)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_4402])).

cnf(c_4367,plain,
    ( ~ m1_pre_topc(sK7,X0)
    | v2_tex_2(u1_struct_0(sK7),X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK7)
    | ~ v1_tdlat_3(sK7)
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_284])).

cnf(c_4591,plain,
    ( ~ m1_pre_topc(sK7,sK5)
    | v2_tex_2(u1_struct_0(sK7),sK5)
    | v2_struct_0(sK5)
    | v2_struct_0(sK7)
    | ~ v1_tdlat_3(sK7)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_4367])).

cnf(c_3,plain,
    ( r1_tarski(X0,sK0(X1,X0))
    | ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_4659,plain,
    ( r1_tarski(u1_struct_0(X0),sK0(sK5,u1_struct_0(X0)))
    | ~ v2_tex_2(u1_struct_0(X0),sK5)
    | v3_tex_2(u1_struct_0(X0),sK5)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4666,plain,
    ( r1_tarski(u1_struct_0(sK6),sK0(sK5,u1_struct_0(sK6)))
    | ~ v2_tex_2(u1_struct_0(sK6),sK5)
    | v3_tex_2(u1_struct_0(sK6),sK5)
    | ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_4659])).

cnf(c_2,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_4658,plain,
    ( ~ v2_tex_2(u1_struct_0(X0),sK5)
    | v3_tex_2(u1_struct_0(X0),sK5)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(sK5)
    | sK0(sK5,u1_struct_0(X0)) != u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_4670,plain,
    ( ~ v2_tex_2(u1_struct_0(sK6),sK5)
    | v3_tex_2(u1_struct_0(sK6),sK5)
    | ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(sK5)
    | sK0(sK5,u1_struct_0(sK6)) != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_4658])).

cnf(c_4385,plain,
    ( ~ m1_pre_topc(sK6,X0)
    | v2_tex_2(u1_struct_0(sK6),X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK6)
    | ~ v1_tdlat_3(sK6)
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_284])).

cnf(c_4681,plain,
    ( ~ m1_pre_topc(sK6,sK5)
    | v2_tex_2(u1_struct_0(sK6),sK5)
    | v2_struct_0(sK5)
    | v2_struct_0(sK6)
    | ~ v1_tdlat_3(sK6)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_4385])).

cnf(c_4716,plain,
    ( ~ m1_pre_topc(sK7,sK5)
    | ~ m1_pre_topc(sK6,sK5)
    | ~ m1_pre_topc(sK6,sK7)
    | r1_tarski(u1_struct_0(sK6),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_715])).

cnf(c_3259,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_4548,plain,
    ( u1_struct_0(sK7) != X0
    | u1_struct_0(sK6) != X0
    | u1_struct_0(sK6) = u1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_3259])).

cnf(c_4884,plain,
    ( u1_struct_0(sK7) != u1_struct_0(X0)
    | u1_struct_0(sK6) != u1_struct_0(X0)
    | u1_struct_0(sK6) = u1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_4548])).

cnf(c_4885,plain,
    ( u1_struct_0(sK7) != u1_struct_0(sK6)
    | u1_struct_0(sK6) = u1_struct_0(sK7)
    | u1_struct_0(sK6) != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_4884])).

cnf(c_5140,plain,
    ( v2_tex_2(u1_struct_0(sK6),sK5)
    | ~ v3_tex_2(u1_struct_0(sK6),sK5)
    | ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_5138])).

cnf(c_19,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_tex_2(u1_struct_0(X0),X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v1_tdlat_3(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_276,plain,
    ( ~ v2_tex_2(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v1_tdlat_3(X0)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19,c_17])).

cnf(c_277,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_tex_2(u1_struct_0(X0),X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v1_tdlat_3(X0)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_276])).

cnf(c_5094,plain,
    ( ~ m1_pre_topc(sK6,X0)
    | ~ v2_tex_2(u1_struct_0(sK6),X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK6)
    | v1_tdlat_3(sK6)
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_277])).

cnf(c_5969,plain,
    ( ~ m1_pre_topc(sK6,sK5)
    | ~ v2_tex_2(u1_struct_0(sK6),sK5)
    | v2_struct_0(sK5)
    | v2_struct_0(sK6)
    | v1_tdlat_3(sK6)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_5094])).

cnf(c_6431,plain,
    ( ~ m1_pre_topc(sK6,sK5)
    | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_6429])).

cnf(c_6222,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X1))
    | X0 = u1_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_11816,plain,
    ( ~ v1_xboole_0(sK0(sK5,u1_struct_0(X0)))
    | ~ v1_xboole_0(u1_struct_0(X1))
    | sK0(sK5,u1_struct_0(X0)) = u1_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_6222])).

cnf(c_11833,plain,
    ( ~ v1_xboole_0(sK0(sK5,u1_struct_0(sK6)))
    | ~ v1_xboole_0(u1_struct_0(sK6))
    | sK0(sK5,u1_struct_0(sK6)) = u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_11816])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v2_tex_2(X1,X2)
    | ~ v3_tex_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_6221,plain,
    ( ~ r1_tarski(u1_struct_0(X0),X1)
    | ~ v2_tex_2(X1,X2)
    | ~ v3_tex_2(u1_struct_0(X0),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | X1 = u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_8893,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ v2_tex_2(u1_struct_0(X1),sK5)
    | ~ v3_tex_2(u1_struct_0(X0),sK5)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(sK5)
    | u1_struct_0(X1) = u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_6221])).

cnf(c_12348,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(sK7))
    | ~ v2_tex_2(u1_struct_0(sK7),sK5)
    | ~ v3_tex_2(u1_struct_0(X0),sK5)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(u1_struct_0(sK7),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(sK5)
    | u1_struct_0(sK7) = u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_8893])).

cnf(c_12350,plain,
    ( ~ r1_tarski(u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ v2_tex_2(u1_struct_0(sK7),sK5)
    | ~ v3_tex_2(u1_struct_0(sK6),sK5)
    | ~ m1_subset_1(u1_struct_0(sK7),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(sK5)
    | u1_struct_0(sK7) = u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_12348])).

cnf(c_14308,plain,
    ( ~ m1_pre_topc(sK7,sK5)
    | m1_subset_1(u1_struct_0(sK7),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_6429])).

cnf(c_18845,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK5) != iProver_top
    | r1_tarski(u1_struct_0(sK6),u1_struct_0(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_18793,c_13153])).

cnf(c_8597,plain,
    ( r1_tarski(u1_struct_0(sK6),u1_struct_0(sK5)) = iProver_top
    | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8595])).

cnf(c_21046,plain,
    ( r1_tarski(u1_struct_0(sK6),u1_struct_0(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18845,c_47,c_49,c_6432,c_8597])).

cnf(c_21059,plain,
    ( u1_struct_0(sK4(sK5,sK0(sK5,u1_struct_0(sK6)))) = sK0(sK5,u1_struct_0(sK6))
    | v2_tex_2(u1_struct_0(sK6),sK5) != iProver_top
    | v3_tex_2(u1_struct_0(sK6),sK5) = iProver_top
    | v1_xboole_0(sK0(sK5,u1_struct_0(sK6))) = iProver_top ),
    inference(superposition,[status(thm)],[c_21046,c_8017])).

cnf(c_21076,plain,
    ( ~ v2_tex_2(u1_struct_0(sK6),sK5)
    | v3_tex_2(u1_struct_0(sK6),sK5)
    | v1_xboole_0(sK0(sK5,u1_struct_0(sK6)))
    | u1_struct_0(sK4(sK5,sK0(sK5,u1_struct_0(sK6)))) = sK0(sK5,u1_struct_0(sK6)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_21059])).

cnf(c_31,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | u1_struct_0(X2) != u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_14717,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(sK6,X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | u1_struct_0(sK6) != u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_20665,plain,
    ( ~ m1_pre_topc(X0,sK5)
    | ~ m1_pre_topc(sK6,sK5)
    | ~ l1_pre_topc(sK5)
    | g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | u1_struct_0(sK6) != u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_14717])).

cnf(c_21860,plain,
    ( ~ m1_pre_topc(sK7,sK5)
    | ~ m1_pre_topc(sK6,sK5)
    | ~ l1_pre_topc(sK5)
    | g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))
    | u1_struct_0(sK6) != u1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_20665])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_361,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_25])).

cnf(c_447,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_1,c_361])).

cnf(c_11852,plain,
    ( ~ r1_tarski(X0,sK0(sK5,u1_struct_0(X1)))
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(sK0(sK5,u1_struct_0(X1))) ),
    inference(instantiation,[status(thm)],[c_447])).

cnf(c_22368,plain,
    ( ~ r1_tarski(u1_struct_0(X0),sK0(sK5,u1_struct_0(X0)))
    | ~ v1_xboole_0(sK0(sK5,u1_struct_0(X0)))
    | v1_xboole_0(u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_11852])).

cnf(c_22370,plain,
    ( ~ r1_tarski(u1_struct_0(sK6),sK0(sK5,u1_struct_0(sK6)))
    | ~ v1_xboole_0(sK0(sK5,u1_struct_0(sK6)))
    | v1_xboole_0(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_22368])).

cnf(c_22890,plain,
    ( u1_struct_0(sK4(sK5,sK0(sK5,u1_struct_0(sK6)))) = sK0(sK5,u1_struct_0(sK6))
    | v4_tex_2(sK6,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22779,c_44,c_42,c_41,c_40,c_37,c_36,c_35,c_34,c_33,c_1429,c_3275,c_3291,c_4412,c_4591,c_4666,c_4670,c_4681,c_4716,c_4885,c_5140,c_5969,c_6431,c_11833,c_12350,c_14308,c_21076,c_21860,c_22370])).

cnf(c_22894,plain,
    ( u1_struct_0(sK4(sK5,sK0(sK5,u1_struct_0(sK6)))) = sK0(sK5,u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22890,c_44,c_42,c_41,c_40,c_37,c_36,c_35,c_34,c_33,c_1429,c_3275,c_3291,c_4412,c_4591,c_4666,c_4670,c_4681,c_4716,c_4885,c_5140,c_5969,c_6431,c_11833,c_12350,c_14308,c_21076,c_21860,c_22370])).

cnf(c_26653,plain,
    ( sK0(sK5,u1_struct_0(sK6)) = X0
    | g1_pre_topc(sK0(sK5,u1_struct_0(sK6)),u1_pre_topc(sK4(sK5,sK0(sK5,u1_struct_0(sK6))))) = sK4(sK5,sK0(sK5,u1_struct_0(sK6)))
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK5) != iProver_top
    | v2_tex_2(u1_struct_0(sK6),sK5) != iProver_top
    | v3_tex_2(u1_struct_0(sK6),sK5) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_26650,c_18793,c_22894])).

cnf(c_4660,plain,
    ( v2_tex_2(sK0(sK5,u1_struct_0(X0)),sK5)
    | ~ v2_tex_2(u1_struct_0(X0),sK5)
    | v3_tex_2(u1_struct_0(X0),sK5)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_4662,plain,
    ( v2_tex_2(sK0(sK5,u1_struct_0(sK6)),sK5)
    | ~ v2_tex_2(u1_struct_0(sK6),sK5)
    | v3_tex_2(u1_struct_0(sK6),sK5)
    | ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_4660])).

cnf(c_8378,plain,
    ( ~ v2_tex_2(u1_struct_0(sK6),sK5)
    | v3_tex_2(u1_struct_0(sK6),sK5)
    | m1_subset_1(sK0(sK5,u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_8488,plain,
    ( m1_pre_topc(sK4(sK5,sK0(sK5,u1_struct_0(X0))),sK5)
    | ~ v2_tex_2(sK0(sK5,u1_struct_0(X0)),sK5)
    | ~ m1_subset_1(sK0(sK5,u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(sK5)))
    | v1_xboole_0(sK0(sK5,u1_struct_0(X0))) ),
    inference(instantiation,[status(thm)],[c_667])).

cnf(c_8490,plain,
    ( m1_pre_topc(sK4(sK5,sK0(sK5,u1_struct_0(sK6))),sK5)
    | ~ v2_tex_2(sK0(sK5,u1_struct_0(sK6)),sK5)
    | ~ m1_subset_1(sK0(sK5,u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK5)))
    | v1_xboole_0(sK0(sK5,u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_8488])).

cnf(c_5443,plain,
    ( m1_pre_topc(sK4(sK5,X0),sK5) = iProver_top
    | r1_tarski(X0,u1_struct_0(sK5)) != iProver_top
    | v2_tex_2(X0,sK5) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4261,c_4241])).

cnf(c_6269,plain,
    ( r1_tarski(X0,u1_struct_0(sK5)) != iProver_top
    | v2_tex_2(X0,sK5) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | l1_pre_topc(sK4(sK5,X0)) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5443,c_4269])).

cnf(c_8270,plain,
    ( l1_pre_topc(sK4(sK5,X0)) = iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v2_tex_2(X0,sK5) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6269,c_47])).

cnf(c_8271,plain,
    ( r1_tarski(X0,u1_struct_0(sK5)) != iProver_top
    | v2_tex_2(X0,sK5) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | l1_pre_topc(sK4(sK5,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_8270])).

cnf(c_8276,plain,
    ( m1_pre_topc(X0,sK5) != iProver_top
    | m1_pre_topc(sK5,sK5) != iProver_top
    | v2_tex_2(u1_struct_0(X0),sK5) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(sK4(sK5,u1_struct_0(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4239,c_8271])).

cnf(c_6387,plain,
    ( m1_pre_topc(X0,sK5) != iProver_top
    | m1_pre_topc(sK4(sK5,u1_struct_0(X0)),sK5) = iProver_top
    | v2_tex_2(u1_struct_0(X0),sK5) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4262,c_4241])).

cnf(c_7027,plain,
    ( v1_xboole_0(u1_struct_0(X0)) = iProver_top
    | v2_tex_2(u1_struct_0(X0),sK5) != iProver_top
    | m1_pre_topc(sK4(sK5,u1_struct_0(X0)),sK5) = iProver_top
    | m1_pre_topc(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6387,c_47])).

cnf(c_7028,plain,
    ( m1_pre_topc(X0,sK5) != iProver_top
    | m1_pre_topc(sK4(sK5,u1_struct_0(X0)),sK5) = iProver_top
    | v2_tex_2(u1_struct_0(X0),sK5) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_7027])).

cnf(c_7033,plain,
    ( m1_pre_topc(X0,sK5) != iProver_top
    | v2_tex_2(u1_struct_0(X0),sK5) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(sK4(sK5,u1_struct_0(X0))) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_7028,c_4269])).

cnf(c_8283,plain,
    ( m1_pre_topc(X0,sK5) != iProver_top
    | v2_tex_2(u1_struct_0(X0),sK5) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(sK4(sK5,u1_struct_0(X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8276,c_47,c_7033])).

cnf(c_8289,plain,
    ( g1_pre_topc(u1_struct_0(sK4(sK5,u1_struct_0(X0))),u1_pre_topc(sK4(sK5,u1_struct_0(X0)))) = sK4(sK5,u1_struct_0(X0))
    | m1_pre_topc(X0,sK5) != iProver_top
    | v2_tex_2(u1_struct_0(X0),sK5) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top
    | v1_pre_topc(sK4(sK5,u1_struct_0(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8283,c_4278])).

cnf(c_6388,plain,
    ( m1_pre_topc(X0,sK5) != iProver_top
    | v2_tex_2(u1_struct_0(X0),sK5) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v1_pre_topc(sK4(sK5,u1_struct_0(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4262,c_4237])).

cnf(c_8748,plain,
    ( v1_xboole_0(u1_struct_0(X0)) = iProver_top
    | v2_tex_2(u1_struct_0(X0),sK5) != iProver_top
    | m1_pre_topc(X0,sK5) != iProver_top
    | g1_pre_topc(u1_struct_0(sK4(sK5,u1_struct_0(X0))),u1_pre_topc(sK4(sK5,u1_struct_0(X0)))) = sK4(sK5,u1_struct_0(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8289,c_47,c_6388])).

cnf(c_8749,plain,
    ( g1_pre_topc(u1_struct_0(sK4(sK5,u1_struct_0(X0))),u1_pre_topc(sK4(sK5,u1_struct_0(X0)))) = sK4(sK5,u1_struct_0(X0))
    | m1_pre_topc(X0,sK5) != iProver_top
    | v2_tex_2(u1_struct_0(X0),sK5) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_8748])).

cnf(c_22944,plain,
    ( g1_pre_topc(u1_struct_0(sK4(sK5,u1_struct_0(sK4(sK5,sK0(sK5,u1_struct_0(sK6)))))),u1_pre_topc(sK4(sK5,u1_struct_0(sK4(sK5,sK0(sK5,u1_struct_0(sK6))))))) = sK4(sK5,u1_struct_0(sK4(sK5,sK0(sK5,u1_struct_0(sK6)))))
    | m1_pre_topc(sK4(sK5,sK0(sK5,u1_struct_0(sK6))),sK5) != iProver_top
    | v2_tex_2(sK0(sK5,u1_struct_0(sK6)),sK5) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4(sK5,sK0(sK5,u1_struct_0(sK6))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_22894,c_8749])).

cnf(c_23004,plain,
    ( g1_pre_topc(sK0(sK5,u1_struct_0(sK6)),u1_pre_topc(sK4(sK5,sK0(sK5,u1_struct_0(sK6))))) = sK4(sK5,sK0(sK5,u1_struct_0(sK6)))
    | m1_pre_topc(sK4(sK5,sK0(sK5,u1_struct_0(sK6))),sK5) != iProver_top
    | v2_tex_2(sK0(sK5,u1_struct_0(sK6)),sK5) != iProver_top
    | v1_xboole_0(sK0(sK5,u1_struct_0(sK6))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_22944,c_22894])).

cnf(c_23129,plain,
    ( ~ m1_pre_topc(sK4(sK5,sK0(sK5,u1_struct_0(sK6))),sK5)
    | ~ v2_tex_2(sK0(sK5,u1_struct_0(sK6)),sK5)
    | v1_xboole_0(sK0(sK5,u1_struct_0(sK6)))
    | g1_pre_topc(sK0(sK5,u1_struct_0(sK6)),u1_pre_topc(sK4(sK5,sK0(sK5,u1_struct_0(sK6))))) = sK4(sK5,sK0(sK5,u1_struct_0(sK6))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_23004])).

cnf(c_30615,plain,
    ( v3_tex_2(u1_struct_0(sK6),sK5) = iProver_top
    | g1_pre_topc(sK0(sK5,u1_struct_0(sK6)),u1_pre_topc(sK4(sK5,sK0(sK5,u1_struct_0(sK6))))) = sK4(sK5,sK0(sK5,u1_struct_0(sK6))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_26653,c_44,c_42,c_41,c_40,c_37,c_36,c_35,c_34,c_33,c_1429,c_3275,c_3291,c_4412,c_4591,c_4662,c_4666,c_4670,c_4681,c_4716,c_4885,c_5140,c_5969,c_6431,c_8378,c_8490,c_11833,c_12350,c_14308,c_21860,c_22370,c_23129])).

cnf(c_30616,plain,
    ( g1_pre_topc(sK0(sK5,u1_struct_0(sK6)),u1_pre_topc(sK4(sK5,sK0(sK5,u1_struct_0(sK6))))) = sK4(sK5,sK0(sK5,u1_struct_0(sK6)))
    | v3_tex_2(u1_struct_0(sK6),sK5) = iProver_top ),
    inference(renaming,[status(thm)],[c_30615])).

cnf(c_30617,plain,
    ( v3_tex_2(u1_struct_0(sK6),sK5)
    | g1_pre_topc(sK0(sK5,u1_struct_0(sK6)),u1_pre_topc(sK4(sK5,sK0(sK5,u1_struct_0(sK6))))) = sK4(sK5,sK0(sK5,u1_struct_0(sK6))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_30616])).

cnf(c_30619,plain,
    ( g1_pre_topc(sK0(sK5,u1_struct_0(sK6)),u1_pre_topc(sK4(sK5,sK0(sK5,u1_struct_0(sK6))))) = sK4(sK5,sK0(sK5,u1_struct_0(sK6))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_30616,c_44,c_42,c_41,c_40,c_37,c_36,c_35,c_34,c_33,c_1429,c_3275,c_3291,c_4412,c_4591,c_4662,c_4666,c_4670,c_4681,c_4716,c_4885,c_5140,c_5969,c_6431,c_8378,c_8490,c_11833,c_12350,c_14308,c_21860,c_22370,c_23129])).

cnf(c_30639,plain,
    ( sK4(sK5,sK0(sK5,u1_struct_0(sK6))) != g1_pre_topc(X0,X1)
    | sK0(sK5,u1_struct_0(sK6)) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_30619,c_4263])).

cnf(c_31880,plain,
    ( sK4(sK5,sK0(sK5,u1_struct_0(sK6))) != g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))
    | sK0(sK5,u1_struct_0(sK6)) = u1_struct_0(sK6)
    | m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_18805,c_30639])).

cnf(c_38,negated_conjecture,
    ( v4_tex_2(sK6,sK5)
    | ~ m1_pre_topc(X0,sK5)
    | ~ m1_pre_topc(sK6,X0)
    | v2_struct_0(X0)
    | ~ v1_tdlat_3(X0)
    | g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_4252,plain,
    ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | v4_tex_2(sK6,sK5) = iProver_top
    | m1_pre_topc(X0,sK5) != iProver_top
    | m1_pre_topc(sK6,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v1_tdlat_3(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_7034,plain,
    ( g1_pre_topc(u1_struct_0(sK4(sK5,u1_struct_0(X0))),u1_pre_topc(sK4(sK5,u1_struct_0(X0)))) = g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))
    | v4_tex_2(sK6,sK5) = iProver_top
    | m1_pre_topc(X0,sK5) != iProver_top
    | m1_pre_topc(sK6,sK4(sK5,u1_struct_0(X0))) != iProver_top
    | v2_tex_2(u1_struct_0(X0),sK5) != iProver_top
    | v2_struct_0(sK4(sK5,u1_struct_0(X0))) = iProver_top
    | v1_tdlat_3(sK4(sK5,u1_struct_0(X0))) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7028,c_4252])).

cnf(c_22,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v1_tdlat_3(sK4(X1,X0))
    | v1_xboole_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_781,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v1_tdlat_3(sK4(X1,X0))
    | v1_xboole_0(X0)
    | ~ l1_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_43])).

cnf(c_782,plain,
    ( ~ v2_tex_2(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | v2_struct_0(sK5)
    | v1_tdlat_3(sK4(sK5,X0))
    | v1_xboole_0(X0)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_781])).

cnf(c_786,plain,
    ( v1_xboole_0(X0)
    | v1_tdlat_3(sK4(sK5,X0))
    | ~ v2_tex_2(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_782,c_44,c_42])).

cnf(c_787,plain,
    ( ~ v2_tex_2(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | v1_tdlat_3(sK4(sK5,X0))
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_786])).

cnf(c_4236,plain,
    ( v2_tex_2(X0,sK5) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v1_tdlat_3(sK4(sK5,X0)) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_787])).

cnf(c_6389,plain,
    ( m1_pre_topc(X0,sK5) != iProver_top
    | v2_tex_2(u1_struct_0(X0),sK5) != iProver_top
    | v1_tdlat_3(sK4(sK5,u1_struct_0(X0))) = iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4262,c_4236])).

cnf(c_24,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK4(X1,X0))
    | v1_xboole_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_733,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK4(X1,X0))
    | v1_xboole_0(X0)
    | ~ l1_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_43])).

cnf(c_734,plain,
    ( ~ v2_tex_2(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v2_struct_0(sK4(sK5,X0))
    | v2_struct_0(sK5)
    | v1_xboole_0(X0)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_733])).

cnf(c_738,plain,
    ( v1_xboole_0(X0)
    | ~ v2_tex_2(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v2_struct_0(sK4(sK5,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_734,c_44,c_42])).

cnf(c_739,plain,
    ( ~ v2_tex_2(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v2_struct_0(sK4(sK5,X0))
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_738])).

cnf(c_4238,plain,
    ( v2_tex_2(X0,sK5) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v2_struct_0(sK4(sK5,X0)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_739])).

cnf(c_6390,plain,
    ( m1_pre_topc(X0,sK5) != iProver_top
    | v2_tex_2(u1_struct_0(X0),sK5) != iProver_top
    | v2_struct_0(sK4(sK5,u1_struct_0(X0))) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4262,c_4238])).

cnf(c_7145,plain,
    ( g1_pre_topc(u1_struct_0(sK4(sK5,u1_struct_0(X0))),u1_pre_topc(sK4(sK5,u1_struct_0(X0)))) = g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))
    | v4_tex_2(sK6,sK5) = iProver_top
    | m1_pre_topc(X0,sK5) != iProver_top
    | m1_pre_topc(sK6,sK4(sK5,u1_struct_0(X0))) != iProver_top
    | v2_tex_2(u1_struct_0(X0),sK5) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7034,c_47,c_6389,c_6390])).

cnf(c_22951,plain,
    ( g1_pre_topc(u1_struct_0(sK4(sK5,u1_struct_0(sK4(sK5,sK0(sK5,u1_struct_0(sK6)))))),u1_pre_topc(sK4(sK5,u1_struct_0(sK4(sK5,sK0(sK5,u1_struct_0(sK6))))))) = g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))
    | v4_tex_2(sK6,sK5) = iProver_top
    | m1_pre_topc(sK4(sK5,sK0(sK5,u1_struct_0(sK6))),sK5) != iProver_top
    | m1_pre_topc(sK6,sK4(sK5,sK0(sK5,u1_struct_0(sK6)))) != iProver_top
    | v2_tex_2(u1_struct_0(sK4(sK5,sK0(sK5,u1_struct_0(sK6)))),sK5) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4(sK5,sK0(sK5,u1_struct_0(sK6))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_22894,c_7145])).

cnf(c_23000,plain,
    ( g1_pre_topc(sK0(sK5,u1_struct_0(sK6)),u1_pre_topc(sK4(sK5,sK0(sK5,u1_struct_0(sK6))))) = g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))
    | v4_tex_2(sK6,sK5) = iProver_top
    | m1_pre_topc(sK4(sK5,sK0(sK5,u1_struct_0(sK6))),sK5) != iProver_top
    | m1_pre_topc(sK6,sK4(sK5,sK0(sK5,u1_struct_0(sK6)))) != iProver_top
    | v2_tex_2(sK0(sK5,u1_struct_0(sK6)),sK5) != iProver_top
    | v1_xboole_0(sK0(sK5,u1_struct_0(sK6))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_22951,c_22894])).

cnf(c_4403,plain,
    ( ~ v4_tex_2(X0,sK5)
    | ~ m1_pre_topc(X0,sK5)
    | v3_tex_2(u1_struct_0(X0),sK5)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_261])).

cnf(c_4408,plain,
    ( ~ v4_tex_2(sK6,sK5)
    | ~ m1_pre_topc(sK6,sK5)
    | v3_tex_2(u1_struct_0(sK6),sK5)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_4403])).

cnf(c_28,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X0,X2)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_685,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X0,X2)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ l1_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_43])).

cnf(c_686,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,sK5)
    | ~ m1_pre_topc(X0,sK5)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_685])).

cnf(c_690,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,sK5)
    | ~ m1_pre_topc(X1,sK5)
    | m1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_686,c_42])).

cnf(c_691,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK5)
    | ~ m1_pre_topc(X1,sK5)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(renaming,[status(thm)],[c_690])).

cnf(c_4240,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,sK5) != iProver_top
    | m1_pre_topc(X1,sK5) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_691])).

cnf(c_22973,plain,
    ( m1_pre_topc(X0,sK4(sK5,sK0(sK5,u1_struct_0(sK6)))) = iProver_top
    | m1_pre_topc(X0,sK5) != iProver_top
    | m1_pre_topc(sK4(sK5,sK0(sK5,u1_struct_0(sK6))),sK5) != iProver_top
    | r1_tarski(u1_struct_0(X0),sK0(sK5,u1_struct_0(sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_22894,c_4240])).

cnf(c_23098,plain,
    ( m1_pre_topc(X0,sK4(sK5,sK0(sK5,u1_struct_0(sK6))))
    | ~ m1_pre_topc(X0,sK5)
    | ~ m1_pre_topc(sK4(sK5,sK0(sK5,u1_struct_0(sK6))),sK5)
    | ~ r1_tarski(u1_struct_0(X0),sK0(sK5,u1_struct_0(sK6))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_22973])).

cnf(c_23100,plain,
    ( ~ m1_pre_topc(sK4(sK5,sK0(sK5,u1_struct_0(sK6))),sK5)
    | m1_pre_topc(sK6,sK4(sK5,sK0(sK5,u1_struct_0(sK6))))
    | ~ m1_pre_topc(sK6,sK5)
    | ~ r1_tarski(u1_struct_0(sK6),sK0(sK5,u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_23098])).

cnf(c_23126,plain,
    ( v4_tex_2(sK6,sK5)
    | ~ m1_pre_topc(sK4(sK5,sK0(sK5,u1_struct_0(sK6))),sK5)
    | ~ m1_pre_topc(sK6,sK4(sK5,sK0(sK5,u1_struct_0(sK6))))
    | ~ v2_tex_2(sK0(sK5,u1_struct_0(sK6)),sK5)
    | v1_xboole_0(sK0(sK5,u1_struct_0(sK6)))
    | g1_pre_topc(sK0(sK5,u1_struct_0(sK6)),u1_pre_topc(sK4(sK5,sK0(sK5,u1_struct_0(sK6))))) = g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_23000])).

cnf(c_31180,plain,
    ( g1_pre_topc(sK0(sK5,u1_struct_0(sK6)),u1_pre_topc(sK4(sK5,sK0(sK5,u1_struct_0(sK6))))) = g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))
    | m1_pre_topc(sK4(sK5,sK0(sK5,u1_struct_0(sK6))),sK5) != iProver_top
    | m1_pre_topc(sK6,sK4(sK5,sK0(sK5,u1_struct_0(sK6)))) != iProver_top
    | v2_tex_2(sK0(sK5,u1_struct_0(sK6)),sK5) != iProver_top
    | v1_xboole_0(sK0(sK5,u1_struct_0(sK6))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_23000,c_44,c_42,c_41,c_40,c_37,c_36,c_35,c_34,c_33,c_1429,c_3275,c_3291,c_4408,c_4412,c_4591,c_4662,c_4666,c_4670,c_4681,c_4716,c_4885,c_5140,c_5969,c_6431,c_8378,c_8490,c_11833,c_12350,c_14308,c_21860,c_22370,c_23100,c_23126])).

cnf(c_31184,plain,
    ( sK4(sK5,sK0(sK5,u1_struct_0(sK6))) = g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))
    | m1_pre_topc(sK4(sK5,sK0(sK5,u1_struct_0(sK6))),sK5) != iProver_top
    | m1_pre_topc(sK6,sK4(sK5,sK0(sK5,u1_struct_0(sK6)))) != iProver_top
    | v2_tex_2(sK0(sK5,u1_struct_0(sK6)),sK5) != iProver_top
    | v1_xboole_0(sK0(sK5,u1_struct_0(sK6))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_31180,c_30619])).

cnf(c_31187,plain,
    ( sK4(sK5,sK0(sK5,u1_struct_0(sK6))) = g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))
    | m1_pre_topc(sK6,sK4(sK5,sK0(sK5,u1_struct_0(sK6)))) != iProver_top
    | v2_tex_2(sK0(sK5,u1_struct_0(sK6)),sK5) != iProver_top
    | v2_tex_2(u1_struct_0(sK6),sK5) != iProver_top
    | v3_tex_2(u1_struct_0(sK6),sK5) = iProver_top
    | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v1_xboole_0(sK0(sK5,u1_struct_0(sK6))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7667,c_31184])).

cnf(c_31189,plain,
    ( ~ m1_pre_topc(sK6,sK4(sK5,sK0(sK5,u1_struct_0(sK6))))
    | ~ v2_tex_2(sK0(sK5,u1_struct_0(sK6)),sK5)
    | ~ v2_tex_2(u1_struct_0(sK6),sK5)
    | v3_tex_2(u1_struct_0(sK6),sK5)
    | ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK5)))
    | v1_xboole_0(sK0(sK5,u1_struct_0(sK6)))
    | sK4(sK5,sK0(sK5,u1_struct_0(sK6))) = g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_31187])).

cnf(c_24695,plain,
    ( m1_pre_topc(X0,sK4(sK5,sK0(sK5,u1_struct_0(sK6)))) = iProver_top
    | m1_pre_topc(X0,sK5) != iProver_top
    | r1_tarski(u1_struct_0(X0),sK0(sK5,u1_struct_0(sK6))) != iProver_top
    | v2_tex_2(u1_struct_0(sK6),sK5) != iProver_top
    | v3_tex_2(u1_struct_0(sK6),sK5) = iProver_top
    | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v1_xboole_0(sK0(sK5,u1_struct_0(sK6))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7667,c_22973])).

cnf(c_24699,plain,
    ( m1_pre_topc(X0,sK4(sK5,sK0(sK5,u1_struct_0(sK6))))
    | ~ m1_pre_topc(X0,sK5)
    | ~ r1_tarski(u1_struct_0(X0),sK0(sK5,u1_struct_0(sK6)))
    | ~ v2_tex_2(u1_struct_0(sK6),sK5)
    | v3_tex_2(u1_struct_0(sK6),sK5)
    | ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK5)))
    | v1_xboole_0(sK0(sK5,u1_struct_0(sK6))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_24695])).

cnf(c_24701,plain,
    ( m1_pre_topc(sK6,sK4(sK5,sK0(sK5,u1_struct_0(sK6))))
    | ~ m1_pre_topc(sK6,sK5)
    | ~ r1_tarski(u1_struct_0(sK6),sK0(sK5,u1_struct_0(sK6)))
    | ~ v2_tex_2(u1_struct_0(sK6),sK5)
    | v3_tex_2(u1_struct_0(sK6),sK5)
    | ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK5)))
    | v1_xboole_0(sK0(sK5,u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_24699])).

cnf(c_4272,plain,
    ( v2_tex_2(X0,X1) = iProver_top
    | v3_tex_2(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6607,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | v2_tex_2(u1_struct_0(X0),X1) = iProver_top
    | v3_tex_2(u1_struct_0(X0),X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4262,c_4272])).

cnf(c_20700,plain,
    ( sK0(sK5,u1_struct_0(X0)) = u1_struct_0(sK6)
    | u1_struct_0(sK4(sK5,sK0(sK5,u1_struct_0(X0)))) = sK0(sK5,u1_struct_0(X0))
    | u1_struct_0(sK4(sK5,u1_struct_0(sK6))) = u1_struct_0(sK6)
    | m1_pre_topc(X0,sK5) != iProver_top
    | v2_tex_2(u1_struct_0(X0),sK5) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v1_tdlat_3(X0) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_20238,c_6607])).

cnf(c_11505,plain,
    ( ~ m1_pre_topc(X0,sK5)
    | v2_tex_2(u1_struct_0(X0),sK5)
    | v2_struct_0(X0)
    | v2_struct_0(sK5)
    | ~ v1_tdlat_3(X0)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_284])).

cnf(c_11506,plain,
    ( m1_pre_topc(X0,sK5) != iProver_top
    | v2_tex_2(u1_struct_0(X0),sK5) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v1_tdlat_3(X0) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11505])).

cnf(c_22177,plain,
    ( v1_tdlat_3(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_tex_2(u1_struct_0(X0),sK5) = iProver_top
    | m1_pre_topc(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20700,c_45,c_47,c_11506])).

cnf(c_22178,plain,
    ( m1_pre_topc(X0,sK5) != iProver_top
    | v2_tex_2(u1_struct_0(X0),sK5) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v1_tdlat_3(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_22177])).

cnf(c_22179,plain,
    ( ~ m1_pre_topc(X0,sK5)
    | v2_tex_2(u1_struct_0(X0),sK5)
    | v2_struct_0(X0)
    | ~ v1_tdlat_3(X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_22178])).

cnf(c_22181,plain,
    ( ~ m1_pre_topc(sK6,sK5)
    | v2_tex_2(u1_struct_0(sK6),sK5)
    | v2_struct_0(sK6)
    | ~ v1_tdlat_3(sK6) ),
    inference(instantiation,[status(thm)],[c_22179])).

cnf(c_18877,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_18793,c_4268])).

cnf(c_5904,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5898])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_31880,c_31189,c_24701,c_22370,c_22181,c_21860,c_18877,c_14308,c_12350,c_11833,c_6431,c_5969,c_5904,c_5140,c_4885,c_4816,c_4716,c_4670,c_4666,c_4662,c_4591,c_4412,c_3291,c_3275,c_1429,c_33,c_34,c_35,c_36,c_37,c_49,c_40,c_41,c_47,c_42,c_44])).


%------------------------------------------------------------------------------
