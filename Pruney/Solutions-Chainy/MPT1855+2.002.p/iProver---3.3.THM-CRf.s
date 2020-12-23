%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:46 EST 2020

% Result     : Theorem 43.38s
% Output     : CNFRefutation 43.38s
% Verified   : 
% Statistics : Number of formulae       :  206 (2679 expanded)
%              Number of clauses        :  120 ( 875 expanded)
%              Number of leaves         :   26 ( 641 expanded)
%              Depth                    :   26
%              Number of atoms          :  808 (13136 expanded)
%              Number of equality atoms :  249 (2533 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f117,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( u1_struct_0(X1) = u1_struct_0(X2)
               => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              | u1_struct_0(X1) != u1_struct_0(X2)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              | u1_struct_0(X1) != u1_struct_0(X2)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
      | u1_struct_0(X1) != u1_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v7_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ? [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2)))
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & v7_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ? [X2] :
                ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2)))
                & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_pre_topc(X1,X0)
          & v7_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_pre_topc(X1,X0)
          & v7_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f73,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_pre_topc(X1,X0)
          & v7_struct_0(X1)
          & ~ v2_struct_0(X1) )
     => ( ! [X2] :
            ( g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2)))
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_pre_topc(sK8,X0)
        & v7_struct_0(sK8)
        & ~ v2_struct_0(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ! [X2] :
                ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2)))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_pre_topc(X1,X0)
            & v7_struct_0(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK7,X2)),u1_pre_topc(k1_tex_2(sK7,X2)))
              | ~ m1_subset_1(X2,u1_struct_0(sK7)) )
          & m1_pre_topc(X1,sK7)
          & v7_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK7)
      & ~ v2_struct_0(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,
    ( ! [X2] :
        ( g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK7,X2)),u1_pre_topc(k1_tex_2(sK7,X2)))
        | ~ m1_subset_1(X2,u1_struct_0(sK7)) )
    & m1_pre_topc(sK8,sK7)
    & v7_struct_0(sK8)
    & ~ v2_struct_0(sK8)
    & l1_pre_topc(sK7)
    & ~ v2_struct_0(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f47,f73,f72])).

fof(f123,plain,(
    ! [X2] :
      ( g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK7,X2)),u1_pre_topc(k1_tex_2(sK7,X2)))
      | ~ m1_subset_1(X2,u1_struct_0(sK7)) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f122,plain,(
    m1_pre_topc(sK8,sK7) ),
    inference(cnf_transformation,[],[f74])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f48,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ( ! [X2] :
            ( ( r2_hidden(X2,u1_pre_topc(X1))
            <=> ? [X3] :
                  ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                  & r2_hidden(X3,u1_pre_topc(X0))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f26,f49,f48])).

fof(f99,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( ( m1_pre_topc(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ m1_pre_topc(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f87,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f101,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f119,plain,(
    l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f74])).

fof(f59,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                  | ~ r2_hidden(X3,u1_pre_topc(X0))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,u1_pre_topc(X1)) )
            & ( ? [X3] :
                  ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                  & r2_hidden(X3,u1_pre_topc(X0))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | r2_hidden(X2,u1_pre_topc(X1)) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
      & ( ( ! [X2] :
              ( ( ( r2_hidden(X2,u1_pre_topc(X1))
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ r2_hidden(X3,u1_pre_topc(X0))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                      & r2_hidden(X3,u1_pre_topc(X0))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,u1_pre_topc(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f60,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                  | ~ r2_hidden(X3,u1_pre_topc(X0))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,u1_pre_topc(X1)) )
            & ( ? [X3] :
                  ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                  & r2_hidden(X3,u1_pre_topc(X0))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | r2_hidden(X2,u1_pre_topc(X1)) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
      & ( ( ! [X2] :
              ( ( ( r2_hidden(X2,u1_pre_topc(X1))
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ r2_hidden(X3,u1_pre_topc(X0))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                      & r2_hidden(X3,u1_pre_topc(X0))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,u1_pre_topc(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
        | ~ sP0(X1,X0) ) ) ),
    inference(flattening,[],[f59])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2
                  | ~ r2_hidden(X3,u1_pre_topc(X1))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r2_hidden(X2,u1_pre_topc(X0)) )
            & ( ? [X4] :
                  ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2
                  & r2_hidden(X4,u1_pre_topc(X1))
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
              | r2_hidden(X2,u1_pre_topc(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
      & ( ( ! [X5] :
              ( ( ( r2_hidden(X5,u1_pre_topc(X0))
                  | ! [X6] :
                      ( k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5
                      | ~ r2_hidden(X6,u1_pre_topc(X1))
                      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ? [X7] :
                      ( k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5
                      & r2_hidden(X7,u1_pre_topc(X1))
                      & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ r2_hidden(X5,u1_pre_topc(X0)) ) )
              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f60])).

fof(f64,plain,(
    ! [X5,X1,X0] :
      ( ? [X7] :
          ( k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5
          & r2_hidden(X7,u1_pre_topc(X1))
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK5(X0,X1,X5),k2_struct_0(X0)) = X5
        & r2_hidden(sK5(X0,X1,X5),u1_pre_topc(X1))
        & m1_subset_1(sK5(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2
          & r2_hidden(X4,u1_pre_topc(X1))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK4(X0,X1),k2_struct_0(X0)) = X2
        & r2_hidden(sK4(X0,X1),u1_pre_topc(X1))
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2
                | ~ r2_hidden(X3,u1_pre_topc(X1))
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r2_hidden(X2,u1_pre_topc(X0)) )
          & ( ? [X4] :
                ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2
                & r2_hidden(X4,u1_pre_topc(X1))
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
            | r2_hidden(X2,u1_pre_topc(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK3(X0,X1)
              | ~ r2_hidden(X3,u1_pre_topc(X1))
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(sK3(X0,X1),u1_pre_topc(X0)) )
        & ( ? [X4] :
              ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = sK3(X0,X1)
              & r2_hidden(X4,u1_pre_topc(X1))
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
          | r2_hidden(sK3(X0,X1),u1_pre_topc(X0)) )
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK3(X0,X1)
                | ~ r2_hidden(X3,u1_pre_topc(X1))
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r2_hidden(sK3(X0,X1),u1_pre_topc(X0)) )
          & ( ( k9_subset_1(u1_struct_0(X0),sK4(X0,X1),k2_struct_0(X0)) = sK3(X0,X1)
              & r2_hidden(sK4(X0,X1),u1_pre_topc(X1))
              & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) )
            | r2_hidden(sK3(X0,X1),u1_pre_topc(X0)) )
          & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
      & ( ( ! [X5] :
              ( ( ( r2_hidden(X5,u1_pre_topc(X0))
                  | ! [X6] :
                      ( k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5
                      | ~ r2_hidden(X6,u1_pre_topc(X1))
                      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ( k9_subset_1(u1_struct_0(X0),sK5(X0,X1,X5),k2_struct_0(X0)) = X5
                    & r2_hidden(sK5(X0,X1,X5),u1_pre_topc(X1))
                    & m1_subset_1(sK5(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ r2_hidden(X5,u1_pre_topc(X0)) ) )
              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f61,f64,f63,f62])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f100,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f86,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_struct_0(X0)
      <=> ? [X1] :
            ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ( v7_struct_0(X0)
      <=> ? [X1] :
            ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f41,plain,(
    ! [X0] :
      ( ( v7_struct_0(X0)
      <=> ? [X1] :
            ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f67,plain,(
    ! [X0] :
      ( ( ( v7_struct_0(X0)
          | ! [X1] :
              ( u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X1] :
              ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
              & m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v7_struct_0(X0) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f68,plain,(
    ! [X0] :
      ( ( ( v7_struct_0(X0)
          | ! [X1] :
              ( u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X2] :
              ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v7_struct_0(X0) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f67])).

fof(f69,plain,(
    ! [X0] :
      ( ? [X2] :
          ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK6(X0))
        & m1_subset_1(sK6(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X0] :
      ( ( ( v7_struct_0(X0)
          | ! [X1] :
              ( u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK6(X0))
            & m1_subset_1(sK6(X0),u1_struct_0(X0)) )
          | ~ v7_struct_0(X0) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f68,f69])).

fof(f110,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(X0),u1_struct_0(X0))
      | ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f120,plain,(
    ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f74])).

fof(f121,plain,(
    v7_struct_0(sK8) ),
    inference(cnf_transformation,[],[f74])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f103,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f51])).

fof(f53,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f52,f53])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f118,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f74])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f107,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f111,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK6(X0))
      | ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_tex_2(X0,X1) = X2
                  | u1_struct_0(X2) != k6_domain_1(u1_struct_0(X0),X1) )
                & ( u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)
                  | k1_tex_2(X0,X1) != X2 ) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)
      | k1_tex_2(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f127,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k1_tex_2(X0,X1)) = k6_domain_1(u1_struct_0(X0),X1)
      | ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ v1_pre_topc(k1_tex_2(X0,X1))
      | v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f113])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f116,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_40,plain,
    ( m1_pre_topc(k1_tex_2(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_83683,plain,
    ( m1_pre_topc(k1_tex_2(sK7,sK6(sK8)),sK7)
    | ~ m1_subset_1(sK6(sK8),u1_struct_0(sK7))
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(instantiation,[status(thm)],[c_40])).

cnf(c_3048,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_49768,plain,
    ( X0 != X1
    | u1_struct_0(sK8) != X1
    | u1_struct_0(sK8) = X0 ),
    inference(instantiation,[status(thm)],[c_3048])).

cnf(c_50356,plain,
    ( X0 != k2_struct_0(sK8)
    | u1_struct_0(sK8) = X0
    | u1_struct_0(sK8) != k2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_49768])).

cnf(c_57797,plain,
    ( u1_struct_0(k1_tex_2(sK7,sK6(sK8))) != k2_struct_0(sK8)
    | u1_struct_0(sK8) = u1_struct_0(k1_tex_2(sK7,sK6(sK8)))
    | u1_struct_0(sK8) != k2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_50356])).

cnf(c_34,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | u1_struct_0(X2) != u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_52280,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK7,sK6(sK8)),X0)
    | ~ m1_pre_topc(sK8,X0)
    | ~ l1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) = g1_pre_topc(u1_struct_0(k1_tex_2(sK7,sK6(sK8))),u1_pre_topc(k1_tex_2(sK7,sK6(sK8))))
    | u1_struct_0(sK8) != u1_struct_0(k1_tex_2(sK7,sK6(sK8))) ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_52283,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK7,sK6(sK8)),sK7)
    | ~ m1_pre_topc(sK8,sK7)
    | ~ l1_pre_topc(sK7)
    | g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) = g1_pre_topc(u1_struct_0(k1_tex_2(sK7,sK6(sK8))),u1_pre_topc(k1_tex_2(sK7,sK6(sK8))))
    | u1_struct_0(sK8) != u1_struct_0(k1_tex_2(sK7,sK6(sK8))) ),
    inference(instantiation,[status(thm)],[c_52280])).

cnf(c_43,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK7,X0)),u1_pre_topc(k1_tex_2(sK7,X0))) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_27846,plain,
    ( ~ m1_subset_1(sK6(sK8),u1_struct_0(sK7))
    | g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK7,sK6(sK8))),u1_pre_topc(k1_tex_2(sK7,sK6(sK8)))) ),
    inference(instantiation,[status(thm)],[c_43])).

cnf(c_3050,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_4076,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,u1_struct_0(sK7))
    | X2 != X0
    | u1_struct_0(sK7) != X1 ),
    inference(instantiation,[status(thm)],[c_3050])).

cnf(c_4332,plain,
    ( r2_hidden(X0,u1_struct_0(sK7))
    | ~ r2_hidden(X1,k2_struct_0(sK7))
    | X0 != X1
    | u1_struct_0(sK7) != k2_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_4076])).

cnf(c_12875,plain,
    ( r2_hidden(X0,u1_struct_0(sK7))
    | ~ r2_hidden(sK6(sK8),k2_struct_0(sK7))
    | X0 != sK6(sK8)
    | u1_struct_0(sK7) != k2_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_4332])).

cnf(c_18390,plain,
    ( r2_hidden(sK6(sK8),u1_struct_0(sK7))
    | ~ r2_hidden(sK6(sK8),k2_struct_0(sK7))
    | sK6(sK8) != sK6(sK8)
    | u1_struct_0(sK7) != k2_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_12875])).

cnf(c_44,negated_conjecture,
    ( m1_pre_topc(sK8,sK7) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_3795,plain,
    ( m1_pre_topc(sK8,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_24,plain,
    ( sP1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_13,plain,
    ( ~ sP1(X0,X1)
    | sP0(X1,X0)
    | ~ m1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_543,plain,
    ( sP0(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_24,c_13])).

cnf(c_26,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_547,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X0,X1)
    | sP0(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_543,c_26])).

cnf(c_548,plain,
    ( sP0(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_547])).

cnf(c_3788,plain,
    ( sP0(X0,X1) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_548])).

cnf(c_5136,plain,
    ( sP0(sK8,sK7) = iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3795,c_3788])).

cnf(c_47,negated_conjecture,
    ( l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_50,plain,
    ( l1_pre_topc(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_5214,plain,
    ( sP0(sK8,sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5136,c_50])).

cnf(c_23,plain,
    ( ~ sP0(X0,X1)
    | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_3806,plain,
    ( sP0(X0,X1) != iProver_top
    | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3805,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4507,plain,
    ( l1_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_3795,c_3805])).

cnf(c_53,plain,
    ( m1_pre_topc(sK8,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_3968,plain,
    ( ~ m1_pre_topc(sK8,X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(sK8) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_3969,plain,
    ( m1_pre_topc(sK8,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3968])).

cnf(c_3971,plain,
    ( m1_pre_topc(sK8,sK7) != iProver_top
    | l1_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK8) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3969])).

cnf(c_4624,plain,
    ( l1_pre_topc(sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4507,c_50,c_53,c_3971])).

cnf(c_25,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_11,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_776,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_25,c_11])).

cnf(c_3782,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_776])).

cnf(c_4628,plain,
    ( u1_struct_0(sK8) = k2_struct_0(sK8) ),
    inference(superposition,[status(thm)],[c_4624,c_3782])).

cnf(c_37,plain,
    ( m1_subset_1(sK6(X0),u1_struct_0(X0))
    | ~ v7_struct_0(X0)
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_716,plain,
    ( m1_subset_1(sK6(X0),u1_struct_0(X0))
    | ~ v7_struct_0(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_25,c_37])).

cnf(c_3786,plain,
    ( m1_subset_1(sK6(X0),u1_struct_0(X0)) = iProver_top
    | v7_struct_0(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_716])).

cnf(c_5268,plain,
    ( m1_subset_1(sK6(sK8),k2_struct_0(sK8)) = iProver_top
    | v7_struct_0(sK8) != iProver_top
    | v2_struct_0(sK8) = iProver_top
    | l1_pre_topc(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_4628,c_3786])).

cnf(c_46,negated_conjecture,
    ( ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_51,plain,
    ( v2_struct_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_45,negated_conjecture,
    ( v7_struct_0(sK8) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_52,plain,
    ( v7_struct_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_5859,plain,
    ( m1_subset_1(sK6(sK8),k2_struct_0(sK8)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5268,c_50,c_51,c_52,c_53,c_3971])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_3816,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5865,plain,
    ( r2_hidden(sK6(sK8),k2_struct_0(sK8)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5859,c_3816])).

cnf(c_28,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_750,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_25,c_28])).

cnf(c_3784,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_750])).

cnf(c_4927,plain,
    ( v2_struct_0(sK8) = iProver_top
    | l1_pre_topc(sK8) != iProver_top
    | v1_xboole_0(k2_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4628,c_3784])).

cnf(c_8510,plain,
    ( r2_hidden(sK6(sK8),k2_struct_0(sK8)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5865,c_50,c_51,c_53,c_3971,c_4927])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_3822,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_8514,plain,
    ( r2_hidden(sK6(sK8),X0) = iProver_top
    | r1_tarski(k2_struct_0(sK8),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8510,c_3822])).

cnf(c_8623,plain,
    ( sP0(sK8,X0) != iProver_top
    | r2_hidden(sK6(sK8),k2_struct_0(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3806,c_8514])).

cnf(c_8628,plain,
    ( sP0(sK8,X0) != iProver_top
    | r2_hidden(sK6(sK8),X1) = iProver_top
    | r1_tarski(k2_struct_0(X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_8623,c_3822])).

cnf(c_10878,plain,
    ( sP0(X0,X1) != iProver_top
    | sP0(sK8,X0) != iProver_top
    | r2_hidden(sK6(sK8),k2_struct_0(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3806,c_8628])).

cnf(c_11093,plain,
    ( sP0(sK8,sK8) != iProver_top
    | r2_hidden(sK6(sK8),k2_struct_0(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5214,c_10878])).

cnf(c_8625,plain,
    ( sP0(sK8,sK7) != iProver_top
    | r2_hidden(sK6(sK8),k2_struct_0(sK7)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_8623])).

cnf(c_11255,plain,
    ( r2_hidden(sK6(sK8),k2_struct_0(sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11093,c_50,c_5136,c_8625])).

cnf(c_8,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_3817,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_11260,plain,
    ( m1_subset_1(sK6(sK8),k2_struct_0(sK7)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11255,c_3817])).

cnf(c_48,negated_conjecture,
    ( ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_49,plain,
    ( v2_struct_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_3792,plain,
    ( l1_pre_topc(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_4195,plain,
    ( u1_struct_0(sK7) = k2_struct_0(sK7) ),
    inference(superposition,[status(thm)],[c_3792,c_3782])).

cnf(c_4448,plain,
    ( v2_struct_0(sK7) = iProver_top
    | l1_pre_topc(sK7) != iProver_top
    | v1_xboole_0(k2_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4195,c_3784])).

cnf(c_8629,plain,
    ( sP0(sK8,X0) != iProver_top
    | m1_subset_1(sK6(sK8),k2_struct_0(X0)) = iProver_top
    | v1_xboole_0(k2_struct_0(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8623,c_3817])).

cnf(c_8634,plain,
    ( sP0(sK8,sK7) != iProver_top
    | m1_subset_1(sK6(sK8),k2_struct_0(sK7)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK7)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_8629])).

cnf(c_11528,plain,
    ( m1_subset_1(sK6(sK8),k2_struct_0(sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11260,c_49,c_50,c_4448,c_5136,c_8634])).

cnf(c_32,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_3803,plain,
    ( k6_domain_1(X0,X1) = k1_tarski(X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_11532,plain,
    ( k6_domain_1(k2_struct_0(sK7),sK6(sK8)) = k1_tarski(sK6(sK8))
    | v1_xboole_0(k2_struct_0(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11528,c_3803])).

cnf(c_5863,plain,
    ( k6_domain_1(k2_struct_0(sK8),sK6(sK8)) = k1_tarski(sK6(sK8))
    | v1_xboole_0(k2_struct_0(sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5859,c_3803])).

cnf(c_3794,plain,
    ( v7_struct_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_36,plain,
    ( ~ v7_struct_0(X0)
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | k6_domain_1(u1_struct_0(X0),sK6(X0)) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_733,plain,
    ( ~ v7_struct_0(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k6_domain_1(u1_struct_0(X0),sK6(X0)) = u1_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_25,c_36])).

cnf(c_3785,plain,
    ( k6_domain_1(u1_struct_0(X0),sK6(X0)) = u1_struct_0(X0)
    | v7_struct_0(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_733])).

cnf(c_4630,plain,
    ( k6_domain_1(u1_struct_0(sK8),sK6(sK8)) = u1_struct_0(sK8)
    | v2_struct_0(sK8) = iProver_top
    | l1_pre_topc(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_3794,c_3785])).

cnf(c_4631,plain,
    ( k6_domain_1(k2_struct_0(sK8),sK6(sK8)) = k2_struct_0(sK8)
    | v2_struct_0(sK8) = iProver_top
    | l1_pre_topc(sK8) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4630,c_4628])).

cnf(c_5019,plain,
    ( k6_domain_1(k2_struct_0(sK8),sK6(sK8)) = k2_struct_0(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4631,c_50,c_51,c_53,c_3971])).

cnf(c_5866,plain,
    ( k1_tarski(sK6(sK8)) = k2_struct_0(sK8)
    | v1_xboole_0(k2_struct_0(sK8)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5863,c_5019])).

cnf(c_6470,plain,
    ( k1_tarski(sK6(sK8)) = k2_struct_0(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5866,c_50,c_51,c_53,c_3971,c_4927])).

cnf(c_39,plain,
    ( ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v1_pre_topc(k1_tex_2(X0,X1))
    | v2_struct_0(X0)
    | v2_struct_0(k1_tex_2(X0,X1))
    | ~ l1_pre_topc(X0)
    | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_274,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v1_pre_topc(k1_tex_2(X0,X1))
    | v2_struct_0(X0)
    | v2_struct_0(k1_tex_2(X0,X1))
    | ~ l1_pre_topc(X0)
    | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_39,c_40])).

cnf(c_275,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v1_pre_topc(k1_tex_2(X1,X0))
    | v2_struct_0(X1)
    | v2_struct_0(k1_tex_2(X1,X0))
    | ~ l1_pre_topc(X1)
    | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
    inference(renaming,[status(thm)],[c_274])).

cnf(c_42,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_41,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v1_pre_topc(k1_tex_2(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_280,plain,
    ( v2_struct_0(X1)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_275,c_42,c_41])).

cnf(c_281,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
    inference(renaming,[status(thm)],[c_280])).

cnf(c_3790,plain,
    ( k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1))
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_281])).

cnf(c_7420,plain,
    ( k6_domain_1(u1_struct_0(sK7),X0) = u1_struct_0(k1_tex_2(sK7,X0))
    | m1_subset_1(X0,k2_struct_0(sK7)) != iProver_top
    | v2_struct_0(sK7) = iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_4195,c_3790])).

cnf(c_7421,plain,
    ( k6_domain_1(k2_struct_0(sK7),X0) = u1_struct_0(k1_tex_2(sK7,X0))
    | m1_subset_1(X0,k2_struct_0(sK7)) != iProver_top
    | v2_struct_0(sK7) = iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7420,c_4195])).

cnf(c_8284,plain,
    ( k6_domain_1(k2_struct_0(sK7),X0) = u1_struct_0(k1_tex_2(sK7,X0))
    | m1_subset_1(X0,k2_struct_0(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7421,c_49,c_50])).

cnf(c_9915,plain,
    ( k6_domain_1(k2_struct_0(sK7),sK6(sK8)) = u1_struct_0(k1_tex_2(sK7,sK6(sK8)))
    | sP0(sK8,sK7) != iProver_top
    | v1_xboole_0(k2_struct_0(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8629,c_8284])).

cnf(c_10239,plain,
    ( k6_domain_1(k2_struct_0(sK7),sK6(sK8)) = u1_struct_0(k1_tex_2(sK7,sK6(sK8))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9915,c_49,c_50,c_4448,c_5136])).

cnf(c_11537,plain,
    ( k6_domain_1(k2_struct_0(sK7),sK6(sK8)) = k2_struct_0(sK8)
    | v1_xboole_0(k2_struct_0(sK7)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11532,c_6470,c_10239])).

cnf(c_11538,plain,
    ( u1_struct_0(k1_tex_2(sK7,sK6(sK8))) = k2_struct_0(sK8)
    | v1_xboole_0(k2_struct_0(sK7)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11537,c_10239])).

cnf(c_8624,plain,
    ( ~ sP0(sK8,X0)
    | r2_hidden(sK6(sK8),k2_struct_0(X0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8623])).

cnf(c_8626,plain,
    ( ~ sP0(sK8,sK7)
    | r2_hidden(sK6(sK8),k2_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_8624])).

cnf(c_4115,plain,
    ( m1_subset_1(X0,u1_struct_0(X1))
    | ~ r2_hidden(X0,u1_struct_0(X1))
    | v1_xboole_0(u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_5597,plain,
    ( m1_subset_1(sK6(sK8),u1_struct_0(X0))
    | ~ r2_hidden(sK6(sK8),u1_struct_0(X0))
    | v1_xboole_0(u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_4115])).

cnf(c_5599,plain,
    ( m1_subset_1(sK6(sK8),u1_struct_0(sK7))
    | ~ r2_hidden(sK6(sK8),u1_struct_0(sK7))
    | v1_xboole_0(u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_5597])).

cnf(c_5140,plain,
    ( sP0(sK8,sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5136])).

cnf(c_3047,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4737,plain,
    ( sK6(sK8) = sK6(sK8) ),
    inference(instantiation,[status(thm)],[c_3047])).

cnf(c_143,plain,
    ( ~ l1_struct_0(sK7)
    | u1_struct_0(sK7) = k2_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_101,plain,
    ( ~ l1_pre_topc(sK7)
    | l1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_96,plain,
    ( v2_struct_0(sK7)
    | ~ l1_struct_0(sK7)
    | ~ v1_xboole_0(u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_83683,c_57797,c_52283,c_27846,c_18390,c_11538,c_8626,c_5599,c_5140,c_4737,c_4628,c_4448,c_143,c_101,c_96,c_44,c_50,c_47,c_49,c_48])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:33:23 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 43.38/6.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 43.38/6.00  
% 43.38/6.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 43.38/6.00  
% 43.38/6.00  ------  iProver source info
% 43.38/6.00  
% 43.38/6.00  git: date: 2020-06-30 10:37:57 +0100
% 43.38/6.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 43.38/6.00  git: non_committed_changes: false
% 43.38/6.00  git: last_make_outside_of_git: false
% 43.38/6.00  
% 43.38/6.00  ------ 
% 43.38/6.00  
% 43.38/6.00  ------ Input Options
% 43.38/6.00  
% 43.38/6.00  --out_options                           all
% 43.38/6.00  --tptp_safe_out                         true
% 43.38/6.00  --problem_path                          ""
% 43.38/6.00  --include_path                          ""
% 43.38/6.00  --clausifier                            res/vclausify_rel
% 43.38/6.00  --clausifier_options                    ""
% 43.38/6.00  --stdin                                 false
% 43.38/6.00  --stats_out                             all
% 43.38/6.00  
% 43.38/6.00  ------ General Options
% 43.38/6.00  
% 43.38/6.00  --fof                                   false
% 43.38/6.00  --time_out_real                         305.
% 43.38/6.00  --time_out_virtual                      -1.
% 43.38/6.00  --symbol_type_check                     false
% 43.38/6.00  --clausify_out                          false
% 43.38/6.00  --sig_cnt_out                           false
% 43.38/6.00  --trig_cnt_out                          false
% 43.38/6.00  --trig_cnt_out_tolerance                1.
% 43.38/6.00  --trig_cnt_out_sk_spl                   false
% 43.38/6.00  --abstr_cl_out                          false
% 43.38/6.00  
% 43.38/6.00  ------ Global Options
% 43.38/6.00  
% 43.38/6.00  --schedule                              default
% 43.38/6.00  --add_important_lit                     false
% 43.38/6.00  --prop_solver_per_cl                    1000
% 43.38/6.00  --min_unsat_core                        false
% 43.38/6.00  --soft_assumptions                      false
% 43.38/6.00  --soft_lemma_size                       3
% 43.38/6.00  --prop_impl_unit_size                   0
% 43.38/6.00  --prop_impl_unit                        []
% 43.38/6.00  --share_sel_clauses                     true
% 43.38/6.00  --reset_solvers                         false
% 43.38/6.00  --bc_imp_inh                            [conj_cone]
% 43.38/6.00  --conj_cone_tolerance                   3.
% 43.38/6.00  --extra_neg_conj                        none
% 43.38/6.00  --large_theory_mode                     true
% 43.38/6.00  --prolific_symb_bound                   200
% 43.38/6.00  --lt_threshold                          2000
% 43.38/6.00  --clause_weak_htbl                      true
% 43.38/6.00  --gc_record_bc_elim                     false
% 43.38/6.00  
% 43.38/6.00  ------ Preprocessing Options
% 43.38/6.00  
% 43.38/6.00  --preprocessing_flag                    true
% 43.38/6.00  --time_out_prep_mult                    0.1
% 43.38/6.00  --splitting_mode                        input
% 43.38/6.00  --splitting_grd                         true
% 43.38/6.00  --splitting_cvd                         false
% 43.38/6.00  --splitting_cvd_svl                     false
% 43.38/6.00  --splitting_nvd                         32
% 43.38/6.00  --sub_typing                            true
% 43.38/6.00  --prep_gs_sim                           true
% 43.38/6.00  --prep_unflatten                        true
% 43.38/6.00  --prep_res_sim                          true
% 43.38/6.00  --prep_upred                            true
% 43.38/6.00  --prep_sem_filter                       exhaustive
% 43.38/6.00  --prep_sem_filter_out                   false
% 43.38/6.00  --pred_elim                             true
% 43.38/6.00  --res_sim_input                         true
% 43.38/6.00  --eq_ax_congr_red                       true
% 43.38/6.00  --pure_diseq_elim                       true
% 43.38/6.00  --brand_transform                       false
% 43.38/6.00  --non_eq_to_eq                          false
% 43.38/6.00  --prep_def_merge                        true
% 43.38/6.00  --prep_def_merge_prop_impl              false
% 43.38/6.00  --prep_def_merge_mbd                    true
% 43.38/6.00  --prep_def_merge_tr_red                 false
% 43.38/6.00  --prep_def_merge_tr_cl                  false
% 43.38/6.00  --smt_preprocessing                     true
% 43.38/6.00  --smt_ac_axioms                         fast
% 43.38/6.00  --preprocessed_out                      false
% 43.38/6.00  --preprocessed_stats                    false
% 43.38/6.00  
% 43.38/6.00  ------ Abstraction refinement Options
% 43.38/6.00  
% 43.38/6.00  --abstr_ref                             []
% 43.38/6.00  --abstr_ref_prep                        false
% 43.38/6.00  --abstr_ref_until_sat                   false
% 43.38/6.00  --abstr_ref_sig_restrict                funpre
% 43.38/6.00  --abstr_ref_af_restrict_to_split_sk     false
% 43.38/6.00  --abstr_ref_under                       []
% 43.38/6.00  
% 43.38/6.00  ------ SAT Options
% 43.38/6.00  
% 43.38/6.00  --sat_mode                              false
% 43.38/6.00  --sat_fm_restart_options                ""
% 43.38/6.00  --sat_gr_def                            false
% 43.38/6.00  --sat_epr_types                         true
% 43.38/6.00  --sat_non_cyclic_types                  false
% 43.38/6.00  --sat_finite_models                     false
% 43.38/6.00  --sat_fm_lemmas                         false
% 43.38/6.00  --sat_fm_prep                           false
% 43.38/6.00  --sat_fm_uc_incr                        true
% 43.38/6.00  --sat_out_model                         small
% 43.38/6.00  --sat_out_clauses                       false
% 43.38/6.00  
% 43.38/6.00  ------ QBF Options
% 43.38/6.00  
% 43.38/6.00  --qbf_mode                              false
% 43.38/6.00  --qbf_elim_univ                         false
% 43.38/6.00  --qbf_dom_inst                          none
% 43.38/6.00  --qbf_dom_pre_inst                      false
% 43.38/6.00  --qbf_sk_in                             false
% 43.38/6.00  --qbf_pred_elim                         true
% 43.38/6.00  --qbf_split                             512
% 43.38/6.00  
% 43.38/6.00  ------ BMC1 Options
% 43.38/6.00  
% 43.38/6.00  --bmc1_incremental                      false
% 43.38/6.00  --bmc1_axioms                           reachable_all
% 43.38/6.00  --bmc1_min_bound                        0
% 43.38/6.00  --bmc1_max_bound                        -1
% 43.38/6.00  --bmc1_max_bound_default                -1
% 43.38/6.00  --bmc1_symbol_reachability              true
% 43.38/6.00  --bmc1_property_lemmas                  false
% 43.38/6.00  --bmc1_k_induction                      false
% 43.38/6.00  --bmc1_non_equiv_states                 false
% 43.38/6.00  --bmc1_deadlock                         false
% 43.38/6.00  --bmc1_ucm                              false
% 43.38/6.00  --bmc1_add_unsat_core                   none
% 43.38/6.00  --bmc1_unsat_core_children              false
% 43.38/6.00  --bmc1_unsat_core_extrapolate_axioms    false
% 43.38/6.00  --bmc1_out_stat                         full
% 43.38/6.00  --bmc1_ground_init                      false
% 43.38/6.00  --bmc1_pre_inst_next_state              false
% 43.38/6.00  --bmc1_pre_inst_state                   false
% 43.38/6.00  --bmc1_pre_inst_reach_state             false
% 43.38/6.00  --bmc1_out_unsat_core                   false
% 43.38/6.00  --bmc1_aig_witness_out                  false
% 43.38/6.00  --bmc1_verbose                          false
% 43.38/6.00  --bmc1_dump_clauses_tptp                false
% 43.38/6.00  --bmc1_dump_unsat_core_tptp             false
% 43.38/6.00  --bmc1_dump_file                        -
% 43.38/6.00  --bmc1_ucm_expand_uc_limit              128
% 43.38/6.00  --bmc1_ucm_n_expand_iterations          6
% 43.38/6.00  --bmc1_ucm_extend_mode                  1
% 43.38/6.00  --bmc1_ucm_init_mode                    2
% 43.38/6.00  --bmc1_ucm_cone_mode                    none
% 43.38/6.00  --bmc1_ucm_reduced_relation_type        0
% 43.38/6.00  --bmc1_ucm_relax_model                  4
% 43.38/6.00  --bmc1_ucm_full_tr_after_sat            true
% 43.38/6.00  --bmc1_ucm_expand_neg_assumptions       false
% 43.38/6.00  --bmc1_ucm_layered_model                none
% 43.38/6.00  --bmc1_ucm_max_lemma_size               10
% 43.38/6.00  
% 43.38/6.00  ------ AIG Options
% 43.38/6.00  
% 43.38/6.00  --aig_mode                              false
% 43.38/6.00  
% 43.38/6.00  ------ Instantiation Options
% 43.38/6.00  
% 43.38/6.00  --instantiation_flag                    true
% 43.38/6.00  --inst_sos_flag                         true
% 43.38/6.00  --inst_sos_phase                        true
% 43.38/6.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 43.38/6.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 43.38/6.00  --inst_lit_sel_side                     num_symb
% 43.38/6.00  --inst_solver_per_active                1400
% 43.38/6.00  --inst_solver_calls_frac                1.
% 43.38/6.00  --inst_passive_queue_type               priority_queues
% 43.38/6.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 43.38/6.00  --inst_passive_queues_freq              [25;2]
% 43.38/6.00  --inst_dismatching                      true
% 43.38/6.00  --inst_eager_unprocessed_to_passive     true
% 43.38/6.00  --inst_prop_sim_given                   true
% 43.38/6.00  --inst_prop_sim_new                     false
% 43.38/6.00  --inst_subs_new                         false
% 43.38/6.00  --inst_eq_res_simp                      false
% 43.38/6.00  --inst_subs_given                       false
% 43.38/6.00  --inst_orphan_elimination               true
% 43.38/6.00  --inst_learning_loop_flag               true
% 43.38/6.00  --inst_learning_start                   3000
% 43.38/6.00  --inst_learning_factor                  2
% 43.38/6.00  --inst_start_prop_sim_after_learn       3
% 43.38/6.00  --inst_sel_renew                        solver
% 43.38/6.00  --inst_lit_activity_flag                true
% 43.38/6.00  --inst_restr_to_given                   false
% 43.38/6.00  --inst_activity_threshold               500
% 43.38/6.00  --inst_out_proof                        true
% 43.38/6.00  
% 43.38/6.00  ------ Resolution Options
% 43.38/6.00  
% 43.38/6.00  --resolution_flag                       true
% 43.38/6.00  --res_lit_sel                           adaptive
% 43.38/6.00  --res_lit_sel_side                      none
% 43.38/6.00  --res_ordering                          kbo
% 43.38/6.00  --res_to_prop_solver                    active
% 43.38/6.00  --res_prop_simpl_new                    false
% 43.38/6.00  --res_prop_simpl_given                  true
% 43.38/6.00  --res_passive_queue_type                priority_queues
% 43.38/6.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 43.38/6.00  --res_passive_queues_freq               [15;5]
% 43.38/6.00  --res_forward_subs                      full
% 43.38/6.00  --res_backward_subs                     full
% 43.38/6.00  --res_forward_subs_resolution           true
% 43.38/6.00  --res_backward_subs_resolution          true
% 43.38/6.00  --res_orphan_elimination                true
% 43.38/6.00  --res_time_limit                        2.
% 43.38/6.00  --res_out_proof                         true
% 43.38/6.00  
% 43.38/6.00  ------ Superposition Options
% 43.38/6.00  
% 43.38/6.00  --superposition_flag                    true
% 43.38/6.00  --sup_passive_queue_type                priority_queues
% 43.38/6.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 43.38/6.00  --sup_passive_queues_freq               [8;1;4]
% 43.38/6.00  --demod_completeness_check              fast
% 43.38/6.00  --demod_use_ground                      true
% 43.38/6.00  --sup_to_prop_solver                    passive
% 43.38/6.00  --sup_prop_simpl_new                    true
% 43.38/6.00  --sup_prop_simpl_given                  true
% 43.38/6.00  --sup_fun_splitting                     true
% 43.38/6.00  --sup_smt_interval                      50000
% 43.38/6.00  
% 43.38/6.00  ------ Superposition Simplification Setup
% 43.38/6.00  
% 43.38/6.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 43.38/6.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 43.38/6.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 43.38/6.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 43.38/6.00  --sup_full_triv                         [TrivRules;PropSubs]
% 43.38/6.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 43.38/6.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 43.38/6.00  --sup_immed_triv                        [TrivRules]
% 43.38/6.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 43.38/6.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.38/6.00  --sup_immed_bw_main                     []
% 43.38/6.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 43.38/6.00  --sup_input_triv                        [Unflattening;TrivRules]
% 43.38/6.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.38/6.00  --sup_input_bw                          []
% 43.38/6.00  
% 43.38/6.00  ------ Combination Options
% 43.38/6.00  
% 43.38/6.00  --comb_res_mult                         3
% 43.38/6.00  --comb_sup_mult                         2
% 43.38/6.00  --comb_inst_mult                        10
% 43.38/6.00  
% 43.38/6.00  ------ Debug Options
% 43.38/6.00  
% 43.38/6.00  --dbg_backtrace                         false
% 43.38/6.00  --dbg_dump_prop_clauses                 false
% 43.38/6.00  --dbg_dump_prop_clauses_file            -
% 43.38/6.00  --dbg_out_stat                          false
% 43.38/6.00  ------ Parsing...
% 43.38/6.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 43.38/6.00  
% 43.38/6.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 43.38/6.00  
% 43.38/6.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 43.38/6.00  
% 43.38/6.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.38/6.00  ------ Proving...
% 43.38/6.00  ------ Problem Properties 
% 43.38/6.00  
% 43.38/6.00  
% 43.38/6.00  clauses                                 44
% 43.38/6.00  conjectures                             6
% 43.38/6.00  EPR                                     16
% 43.38/6.00  Horn                                    29
% 43.38/6.00  unary                                   6
% 43.38/6.00  binary                                  6
% 43.38/6.00  lits                                    141
% 43.38/6.00  lits eq                                 14
% 43.38/6.00  fd_pure                                 0
% 43.38/6.00  fd_pseudo                               0
% 43.38/6.00  fd_cond                                 0
% 43.38/6.00  fd_pseudo_cond                          2
% 43.38/6.00  AC symbols                              0
% 43.38/6.00  
% 43.38/6.00  ------ Schedule dynamic 5 is on 
% 43.38/6.00  
% 43.38/6.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 43.38/6.00  
% 43.38/6.00  
% 43.38/6.00  ------ 
% 43.38/6.00  Current options:
% 43.38/6.00  ------ 
% 43.38/6.00  
% 43.38/6.00  ------ Input Options
% 43.38/6.00  
% 43.38/6.00  --out_options                           all
% 43.38/6.00  --tptp_safe_out                         true
% 43.38/6.00  --problem_path                          ""
% 43.38/6.00  --include_path                          ""
% 43.38/6.00  --clausifier                            res/vclausify_rel
% 43.38/6.00  --clausifier_options                    ""
% 43.38/6.00  --stdin                                 false
% 43.38/6.00  --stats_out                             all
% 43.38/6.00  
% 43.38/6.00  ------ General Options
% 43.38/6.00  
% 43.38/6.00  --fof                                   false
% 43.38/6.00  --time_out_real                         305.
% 43.38/6.00  --time_out_virtual                      -1.
% 43.38/6.00  --symbol_type_check                     false
% 43.38/6.00  --clausify_out                          false
% 43.38/6.00  --sig_cnt_out                           false
% 43.38/6.00  --trig_cnt_out                          false
% 43.38/6.00  --trig_cnt_out_tolerance                1.
% 43.38/6.00  --trig_cnt_out_sk_spl                   false
% 43.38/6.00  --abstr_cl_out                          false
% 43.38/6.00  
% 43.38/6.00  ------ Global Options
% 43.38/6.00  
% 43.38/6.00  --schedule                              default
% 43.38/6.00  --add_important_lit                     false
% 43.38/6.00  --prop_solver_per_cl                    1000
% 43.38/6.00  --min_unsat_core                        false
% 43.38/6.00  --soft_assumptions                      false
% 43.38/6.00  --soft_lemma_size                       3
% 43.38/6.00  --prop_impl_unit_size                   0
% 43.38/6.00  --prop_impl_unit                        []
% 43.38/6.00  --share_sel_clauses                     true
% 43.38/6.00  --reset_solvers                         false
% 43.38/6.00  --bc_imp_inh                            [conj_cone]
% 43.38/6.00  --conj_cone_tolerance                   3.
% 43.38/6.00  --extra_neg_conj                        none
% 43.38/6.00  --large_theory_mode                     true
% 43.38/6.00  --prolific_symb_bound                   200
% 43.38/6.00  --lt_threshold                          2000
% 43.38/6.00  --clause_weak_htbl                      true
% 43.38/6.00  --gc_record_bc_elim                     false
% 43.38/6.00  
% 43.38/6.00  ------ Preprocessing Options
% 43.38/6.00  
% 43.38/6.00  --preprocessing_flag                    true
% 43.38/6.00  --time_out_prep_mult                    0.1
% 43.38/6.00  --splitting_mode                        input
% 43.38/6.00  --splitting_grd                         true
% 43.38/6.00  --splitting_cvd                         false
% 43.38/6.00  --splitting_cvd_svl                     false
% 43.38/6.00  --splitting_nvd                         32
% 43.38/6.00  --sub_typing                            true
% 43.38/6.00  --prep_gs_sim                           true
% 43.38/6.00  --prep_unflatten                        true
% 43.38/6.00  --prep_res_sim                          true
% 43.38/6.00  --prep_upred                            true
% 43.38/6.00  --prep_sem_filter                       exhaustive
% 43.38/6.00  --prep_sem_filter_out                   false
% 43.38/6.00  --pred_elim                             true
% 43.38/6.00  --res_sim_input                         true
% 43.38/6.00  --eq_ax_congr_red                       true
% 43.38/6.00  --pure_diseq_elim                       true
% 43.38/6.00  --brand_transform                       false
% 43.38/6.00  --non_eq_to_eq                          false
% 43.38/6.00  --prep_def_merge                        true
% 43.38/6.00  --prep_def_merge_prop_impl              false
% 43.38/6.00  --prep_def_merge_mbd                    true
% 43.38/6.00  --prep_def_merge_tr_red                 false
% 43.38/6.00  --prep_def_merge_tr_cl                  false
% 43.38/6.00  --smt_preprocessing                     true
% 43.38/6.00  --smt_ac_axioms                         fast
% 43.38/6.00  --preprocessed_out                      false
% 43.38/6.00  --preprocessed_stats                    false
% 43.38/6.00  
% 43.38/6.00  ------ Abstraction refinement Options
% 43.38/6.00  
% 43.38/6.00  --abstr_ref                             []
% 43.38/6.00  --abstr_ref_prep                        false
% 43.38/6.00  --abstr_ref_until_sat                   false
% 43.38/6.00  --abstr_ref_sig_restrict                funpre
% 43.38/6.00  --abstr_ref_af_restrict_to_split_sk     false
% 43.38/6.00  --abstr_ref_under                       []
% 43.38/6.00  
% 43.38/6.00  ------ SAT Options
% 43.38/6.00  
% 43.38/6.00  --sat_mode                              false
% 43.38/6.00  --sat_fm_restart_options                ""
% 43.38/6.00  --sat_gr_def                            false
% 43.38/6.00  --sat_epr_types                         true
% 43.38/6.00  --sat_non_cyclic_types                  false
% 43.38/6.00  --sat_finite_models                     false
% 43.38/6.00  --sat_fm_lemmas                         false
% 43.38/6.00  --sat_fm_prep                           false
% 43.38/6.00  --sat_fm_uc_incr                        true
% 43.38/6.00  --sat_out_model                         small
% 43.38/6.00  --sat_out_clauses                       false
% 43.38/6.00  
% 43.38/6.00  ------ QBF Options
% 43.38/6.00  
% 43.38/6.00  --qbf_mode                              false
% 43.38/6.00  --qbf_elim_univ                         false
% 43.38/6.00  --qbf_dom_inst                          none
% 43.38/6.00  --qbf_dom_pre_inst                      false
% 43.38/6.00  --qbf_sk_in                             false
% 43.38/6.00  --qbf_pred_elim                         true
% 43.38/6.00  --qbf_split                             512
% 43.38/6.00  
% 43.38/6.00  ------ BMC1 Options
% 43.38/6.00  
% 43.38/6.00  --bmc1_incremental                      false
% 43.38/6.00  --bmc1_axioms                           reachable_all
% 43.38/6.00  --bmc1_min_bound                        0
% 43.38/6.00  --bmc1_max_bound                        -1
% 43.38/6.00  --bmc1_max_bound_default                -1
% 43.38/6.00  --bmc1_symbol_reachability              true
% 43.38/6.00  --bmc1_property_lemmas                  false
% 43.38/6.00  --bmc1_k_induction                      false
% 43.38/6.00  --bmc1_non_equiv_states                 false
% 43.38/6.00  --bmc1_deadlock                         false
% 43.38/6.00  --bmc1_ucm                              false
% 43.38/6.00  --bmc1_add_unsat_core                   none
% 43.38/6.00  --bmc1_unsat_core_children              false
% 43.38/6.00  --bmc1_unsat_core_extrapolate_axioms    false
% 43.38/6.00  --bmc1_out_stat                         full
% 43.38/6.00  --bmc1_ground_init                      false
% 43.38/6.00  --bmc1_pre_inst_next_state              false
% 43.38/6.00  --bmc1_pre_inst_state                   false
% 43.38/6.00  --bmc1_pre_inst_reach_state             false
% 43.38/6.00  --bmc1_out_unsat_core                   false
% 43.38/6.00  --bmc1_aig_witness_out                  false
% 43.38/6.00  --bmc1_verbose                          false
% 43.38/6.00  --bmc1_dump_clauses_tptp                false
% 43.38/6.00  --bmc1_dump_unsat_core_tptp             false
% 43.38/6.00  --bmc1_dump_file                        -
% 43.38/6.00  --bmc1_ucm_expand_uc_limit              128
% 43.38/6.00  --bmc1_ucm_n_expand_iterations          6
% 43.38/6.00  --bmc1_ucm_extend_mode                  1
% 43.38/6.00  --bmc1_ucm_init_mode                    2
% 43.38/6.00  --bmc1_ucm_cone_mode                    none
% 43.38/6.00  --bmc1_ucm_reduced_relation_type        0
% 43.38/6.00  --bmc1_ucm_relax_model                  4
% 43.38/6.00  --bmc1_ucm_full_tr_after_sat            true
% 43.38/6.00  --bmc1_ucm_expand_neg_assumptions       false
% 43.38/6.00  --bmc1_ucm_layered_model                none
% 43.38/6.00  --bmc1_ucm_max_lemma_size               10
% 43.38/6.00  
% 43.38/6.00  ------ AIG Options
% 43.38/6.00  
% 43.38/6.00  --aig_mode                              false
% 43.38/6.00  
% 43.38/6.00  ------ Instantiation Options
% 43.38/6.00  
% 43.38/6.00  --instantiation_flag                    true
% 43.38/6.00  --inst_sos_flag                         true
% 43.38/6.00  --inst_sos_phase                        true
% 43.38/6.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 43.38/6.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 43.38/6.00  --inst_lit_sel_side                     none
% 43.38/6.00  --inst_solver_per_active                1400
% 43.38/6.00  --inst_solver_calls_frac                1.
% 43.38/6.00  --inst_passive_queue_type               priority_queues
% 43.38/6.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 43.38/6.00  --inst_passive_queues_freq              [25;2]
% 43.38/6.00  --inst_dismatching                      true
% 43.38/6.00  --inst_eager_unprocessed_to_passive     true
% 43.38/6.00  --inst_prop_sim_given                   true
% 43.38/6.00  --inst_prop_sim_new                     false
% 43.38/6.00  --inst_subs_new                         false
% 43.38/6.00  --inst_eq_res_simp                      false
% 43.38/6.00  --inst_subs_given                       false
% 43.38/6.00  --inst_orphan_elimination               true
% 43.38/6.00  --inst_learning_loop_flag               true
% 43.38/6.00  --inst_learning_start                   3000
% 43.38/6.00  --inst_learning_factor                  2
% 43.38/6.00  --inst_start_prop_sim_after_learn       3
% 43.38/6.00  --inst_sel_renew                        solver
% 43.38/6.00  --inst_lit_activity_flag                true
% 43.38/6.00  --inst_restr_to_given                   false
% 43.38/6.00  --inst_activity_threshold               500
% 43.38/6.00  --inst_out_proof                        true
% 43.38/6.00  
% 43.38/6.00  ------ Resolution Options
% 43.38/6.00  
% 43.38/6.00  --resolution_flag                       false
% 43.38/6.00  --res_lit_sel                           adaptive
% 43.38/6.00  --res_lit_sel_side                      none
% 43.38/6.00  --res_ordering                          kbo
% 43.38/6.00  --res_to_prop_solver                    active
% 43.38/6.00  --res_prop_simpl_new                    false
% 43.38/6.00  --res_prop_simpl_given                  true
% 43.38/6.00  --res_passive_queue_type                priority_queues
% 43.38/6.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 43.38/6.00  --res_passive_queues_freq               [15;5]
% 43.38/6.00  --res_forward_subs                      full
% 43.38/6.00  --res_backward_subs                     full
% 43.38/6.00  --res_forward_subs_resolution           true
% 43.38/6.00  --res_backward_subs_resolution          true
% 43.38/6.00  --res_orphan_elimination                true
% 43.38/6.00  --res_time_limit                        2.
% 43.38/6.00  --res_out_proof                         true
% 43.38/6.00  
% 43.38/6.00  ------ Superposition Options
% 43.38/6.00  
% 43.38/6.00  --superposition_flag                    true
% 43.38/6.00  --sup_passive_queue_type                priority_queues
% 43.38/6.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 43.38/6.00  --sup_passive_queues_freq               [8;1;4]
% 43.38/6.00  --demod_completeness_check              fast
% 43.38/6.00  --demod_use_ground                      true
% 43.38/6.00  --sup_to_prop_solver                    passive
% 43.38/6.00  --sup_prop_simpl_new                    true
% 43.38/6.00  --sup_prop_simpl_given                  true
% 43.38/6.00  --sup_fun_splitting                     true
% 43.38/6.00  --sup_smt_interval                      50000
% 43.38/6.00  
% 43.38/6.00  ------ Superposition Simplification Setup
% 43.38/6.00  
% 43.38/6.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 43.38/6.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 43.38/6.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 43.38/6.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 43.38/6.00  --sup_full_triv                         [TrivRules;PropSubs]
% 43.38/6.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 43.38/6.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 43.38/6.00  --sup_immed_triv                        [TrivRules]
% 43.38/6.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 43.38/6.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.38/6.00  --sup_immed_bw_main                     []
% 43.38/6.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 43.38/6.00  --sup_input_triv                        [Unflattening;TrivRules]
% 43.38/6.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.38/6.00  --sup_input_bw                          []
% 43.38/6.00  
% 43.38/6.00  ------ Combination Options
% 43.38/6.00  
% 43.38/6.00  --comb_res_mult                         3
% 43.38/6.00  --comb_sup_mult                         2
% 43.38/6.00  --comb_inst_mult                        10
% 43.38/6.00  
% 43.38/6.00  ------ Debug Options
% 43.38/6.00  
% 43.38/6.00  --dbg_backtrace                         false
% 43.38/6.00  --dbg_dump_prop_clauses                 false
% 43.38/6.00  --dbg_dump_prop_clauses_file            -
% 43.38/6.00  --dbg_out_stat                          false
% 43.38/6.00  
% 43.38/6.00  
% 43.38/6.00  
% 43.38/6.00  
% 43.38/6.00  ------ Proving...
% 43.38/6.00  
% 43.38/6.00  
% 43.38/6.00  % SZS status Theorem for theBenchmark.p
% 43.38/6.00  
% 43.38/6.00  % SZS output start CNFRefutation for theBenchmark.p
% 43.38/6.00  
% 43.38/6.00  fof(f18,axiom,(
% 43.38/6.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 43.38/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.38/6.00  
% 43.38/6.00  fof(f44,plain,(
% 43.38/6.00    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 43.38/6.00    inference(ennf_transformation,[],[f18])).
% 43.38/6.00  
% 43.38/6.00  fof(f45,plain,(
% 43.38/6.00    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 43.38/6.00    inference(flattening,[],[f44])).
% 43.38/6.00  
% 43.38/6.00  fof(f117,plain,(
% 43.38/6.00    ( ! [X0,X1] : (m1_pre_topc(k1_tex_2(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 43.38/6.00    inference(cnf_transformation,[],[f45])).
% 43.38/6.00  
% 43.38/6.00  fof(f15,axiom,(
% 43.38/6.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (u1_struct_0(X1) = u1_struct_0(X2) => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))),
% 43.38/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.38/6.00  
% 43.38/6.00  fof(f38,plain,(
% 43.38/6.00    ! [X0] : (! [X1] : (! [X2] : ((g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | u1_struct_0(X1) != u1_struct_0(X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 43.38/6.00    inference(ennf_transformation,[],[f15])).
% 43.38/6.00  
% 43.38/6.00  fof(f39,plain,(
% 43.38/6.00    ! [X0] : (! [X1] : (! [X2] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | u1_struct_0(X1) != u1_struct_0(X2) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 43.38/6.00    inference(flattening,[],[f38])).
% 43.38/6.00  
% 43.38/6.00  fof(f109,plain,(
% 43.38/6.00    ( ! [X2,X0,X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | u1_struct_0(X1) != u1_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 43.38/6.00    inference(cnf_transformation,[],[f39])).
% 43.38/6.00  
% 43.38/6.00  fof(f19,conjecture,(
% 43.38/6.00    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v7_struct_0(X1) & ~v2_struct_0(X1)) => ? [X2] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2))) & m1_subset_1(X2,u1_struct_0(X0)))))),
% 43.38/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.38/6.00  
% 43.38/6.00  fof(f20,negated_conjecture,(
% 43.38/6.00    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v7_struct_0(X1) & ~v2_struct_0(X1)) => ? [X2] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2))) & m1_subset_1(X2,u1_struct_0(X0)))))),
% 43.38/6.00    inference(negated_conjecture,[],[f19])).
% 43.38/6.00  
% 43.38/6.00  fof(f46,plain,(
% 43.38/6.00    ? [X0] : (? [X1] : (! [X2] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) & (m1_pre_topc(X1,X0) & v7_struct_0(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 43.38/6.00    inference(ennf_transformation,[],[f20])).
% 43.38/6.00  
% 43.38/6.00  fof(f47,plain,(
% 43.38/6.00    ? [X0] : (? [X1] : (! [X2] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_pre_topc(X1,X0) & v7_struct_0(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 43.38/6.00    inference(flattening,[],[f46])).
% 43.38/6.00  
% 43.38/6.00  fof(f73,plain,(
% 43.38/6.00    ( ! [X0] : (? [X1] : (! [X2] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_pre_topc(X1,X0) & v7_struct_0(X1) & ~v2_struct_0(X1)) => (! [X2] : (g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_pre_topc(sK8,X0) & v7_struct_0(sK8) & ~v2_struct_0(sK8))) )),
% 43.38/6.00    introduced(choice_axiom,[])).
% 43.38/6.00  
% 43.38/6.00  fof(f72,plain,(
% 43.38/6.00    ? [X0] : (? [X1] : (! [X2] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_pre_topc(X1,X0) & v7_struct_0(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (! [X2] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK7,X2)),u1_pre_topc(k1_tex_2(sK7,X2))) | ~m1_subset_1(X2,u1_struct_0(sK7))) & m1_pre_topc(X1,sK7) & v7_struct_0(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK7) & ~v2_struct_0(sK7))),
% 43.38/6.00    introduced(choice_axiom,[])).
% 43.38/6.00  
% 43.38/6.00  fof(f74,plain,(
% 43.38/6.00    (! [X2] : (g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK7,X2)),u1_pre_topc(k1_tex_2(sK7,X2))) | ~m1_subset_1(X2,u1_struct_0(sK7))) & m1_pre_topc(sK8,sK7) & v7_struct_0(sK8) & ~v2_struct_0(sK8)) & l1_pre_topc(sK7) & ~v2_struct_0(sK7)),
% 43.38/6.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f47,f73,f72])).
% 43.38/6.00  
% 43.38/6.00  fof(f123,plain,(
% 43.38/6.00    ( ! [X2] : (g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK7,X2)),u1_pre_topc(k1_tex_2(sK7,X2))) | ~m1_subset_1(X2,u1_struct_0(sK7))) )),
% 43.38/6.00    inference(cnf_transformation,[],[f74])).
% 43.38/6.00  
% 43.38/6.00  fof(f122,plain,(
% 43.38/6.00    m1_pre_topc(sK8,sK7)),
% 43.38/6.00    inference(cnf_transformation,[],[f74])).
% 43.38/6.00  
% 43.38/6.00  fof(f6,axiom,(
% 43.38/6.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 43.38/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.38/6.00  
% 43.38/6.00  fof(f26,plain,(
% 43.38/6.00    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 43.38/6.00    inference(ennf_transformation,[],[f6])).
% 43.38/6.00  
% 43.38/6.00  fof(f49,plain,(
% 43.38/6.00    ! [X0,X1] : ((m1_pre_topc(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 43.38/6.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 43.38/6.00  
% 43.38/6.00  fof(f48,plain,(
% 43.38/6.00    ! [X1,X0] : (sP0(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))),
% 43.38/6.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 43.38/6.00  
% 43.38/6.00  fof(f50,plain,(
% 43.38/6.00    ! [X0] : (! [X1] : (sP1(X0,X1) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 43.38/6.00    inference(definition_folding,[],[f26,f49,f48])).
% 43.38/6.00  
% 43.38/6.00  fof(f99,plain,(
% 43.38/6.00    ( ! [X0,X1] : (sP1(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 43.38/6.00    inference(cnf_transformation,[],[f50])).
% 43.38/6.00  
% 43.38/6.00  fof(f58,plain,(
% 43.38/6.00    ! [X0,X1] : (((m1_pre_topc(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~m1_pre_topc(X1,X0))) | ~sP1(X0,X1))),
% 43.38/6.00    inference(nnf_transformation,[],[f49])).
% 43.38/6.00  
% 43.38/6.00  fof(f87,plain,(
% 43.38/6.00    ( ! [X0,X1] : (sP0(X1,X0) | ~m1_pre_topc(X1,X0) | ~sP1(X0,X1)) )),
% 43.38/6.00    inference(cnf_transformation,[],[f58])).
% 43.38/6.00  
% 43.38/6.00  fof(f8,axiom,(
% 43.38/6.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 43.38/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.38/6.00  
% 43.38/6.00  fof(f28,plain,(
% 43.38/6.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 43.38/6.00    inference(ennf_transformation,[],[f8])).
% 43.38/6.00  
% 43.38/6.00  fof(f101,plain,(
% 43.38/6.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 43.38/6.00    inference(cnf_transformation,[],[f28])).
% 43.38/6.00  
% 43.38/6.00  fof(f119,plain,(
% 43.38/6.00    l1_pre_topc(sK7)),
% 43.38/6.00    inference(cnf_transformation,[],[f74])).
% 43.38/6.00  
% 43.38/6.00  fof(f59,plain,(
% 43.38/6.00    ! [X1,X0] : ((sP0(X1,X0) | (? [X2] : (((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 43.38/6.00    inference(nnf_transformation,[],[f48])).
% 43.38/6.00  
% 43.38/6.00  fof(f60,plain,(
% 43.38/6.00    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 43.38/6.00    inference(flattening,[],[f59])).
% 43.38/6.00  
% 43.38/6.00  fof(f61,plain,(
% 43.38/6.00    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 43.38/6.00    inference(rectify,[],[f60])).
% 43.38/6.00  
% 43.38/6.00  fof(f64,plain,(
% 43.38/6.00    ! [X5,X1,X0] : (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK5(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK5(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK5(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))))),
% 43.38/6.00    introduced(choice_axiom,[])).
% 43.38/6.00  
% 43.38/6.00  fof(f63,plain,(
% 43.38/6.00    ( ! [X2] : (! [X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK4(X0,X1),k2_struct_0(X0)) = X2 & r2_hidden(sK4(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))) )),
% 43.38/6.00    introduced(choice_axiom,[])).
% 43.38/6.00  
% 43.38/6.00  fof(f62,plain,(
% 43.38/6.00    ! [X1,X0] : (? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK3(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK3(X0,X1),u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = sK3(X0,X1) & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK3(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 43.38/6.00    introduced(choice_axiom,[])).
% 43.38/6.00  
% 43.38/6.00  fof(f65,plain,(
% 43.38/6.00    ! [X0,X1] : ((sP0(X0,X1) | ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK3(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK3(X0,X1),u1_pre_topc(X0))) & ((k9_subset_1(u1_struct_0(X0),sK4(X0,X1),k2_struct_0(X0)) = sK3(X0,X1) & r2_hidden(sK4(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK3(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & ((k9_subset_1(u1_struct_0(X0),sK5(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK5(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK5(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 43.38/6.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f61,f64,f63,f62])).
% 43.38/6.00  
% 43.38/6.00  fof(f89,plain,(
% 43.38/6.00    ( ! [X0,X1] : (r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) | ~sP0(X0,X1)) )),
% 43.38/6.00    inference(cnf_transformation,[],[f65])).
% 43.38/6.00  
% 43.38/6.00  fof(f7,axiom,(
% 43.38/6.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 43.38/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.38/6.00  
% 43.38/6.00  fof(f27,plain,(
% 43.38/6.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 43.38/6.00    inference(ennf_transformation,[],[f7])).
% 43.38/6.00  
% 43.38/6.00  fof(f100,plain,(
% 43.38/6.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 43.38/6.00    inference(cnf_transformation,[],[f27])).
% 43.38/6.00  
% 43.38/6.00  fof(f5,axiom,(
% 43.38/6.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 43.38/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.38/6.00  
% 43.38/6.00  fof(f25,plain,(
% 43.38/6.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 43.38/6.00    inference(ennf_transformation,[],[f5])).
% 43.38/6.00  
% 43.38/6.00  fof(f86,plain,(
% 43.38/6.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 43.38/6.00    inference(cnf_transformation,[],[f25])).
% 43.38/6.00  
% 43.38/6.00  fof(f16,axiom,(
% 43.38/6.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_struct_0(X0) <=> ? [X1] : (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 43.38/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.38/6.00  
% 43.38/6.00  fof(f40,plain,(
% 43.38/6.00    ! [X0] : ((v7_struct_0(X0) <=> ? [X1] : (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 43.38/6.00    inference(ennf_transformation,[],[f16])).
% 43.38/6.00  
% 43.38/6.00  fof(f41,plain,(
% 43.38/6.00    ! [X0] : ((v7_struct_0(X0) <=> ? [X1] : (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 43.38/6.00    inference(flattening,[],[f40])).
% 43.38/6.00  
% 43.38/6.00  fof(f67,plain,(
% 43.38/6.00    ! [X0] : (((v7_struct_0(X0) | ! [X1] : (u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X1] : (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) | ~v7_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 43.38/6.00    inference(nnf_transformation,[],[f41])).
% 43.38/6.00  
% 43.38/6.00  fof(f68,plain,(
% 43.38/6.00    ! [X0] : (((v7_struct_0(X0) | ! [X1] : (u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X2] : (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~v7_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 43.38/6.00    inference(rectify,[],[f67])).
% 43.38/6.00  
% 43.38/6.00  fof(f69,plain,(
% 43.38/6.00    ! [X0] : (? [X2] : (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X2) & m1_subset_1(X2,u1_struct_0(X0))) => (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK6(X0)) & m1_subset_1(sK6(X0),u1_struct_0(X0))))),
% 43.38/6.00    introduced(choice_axiom,[])).
% 43.38/6.00  
% 43.38/6.00  fof(f70,plain,(
% 43.38/6.00    ! [X0] : (((v7_struct_0(X0) | ! [X1] : (u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)))) & ((u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK6(X0)) & m1_subset_1(sK6(X0),u1_struct_0(X0))) | ~v7_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 43.38/6.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f68,f69])).
% 43.38/6.00  
% 43.38/6.00  fof(f110,plain,(
% 43.38/6.00    ( ! [X0] : (m1_subset_1(sK6(X0),u1_struct_0(X0)) | ~v7_struct_0(X0) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 43.38/6.00    inference(cnf_transformation,[],[f70])).
% 43.38/6.00  
% 43.38/6.00  fof(f120,plain,(
% 43.38/6.00    ~v2_struct_0(sK8)),
% 43.38/6.00    inference(cnf_transformation,[],[f74])).
% 43.38/6.00  
% 43.38/6.00  fof(f121,plain,(
% 43.38/6.00    v7_struct_0(sK8)),
% 43.38/6.00    inference(cnf_transformation,[],[f74])).
% 43.38/6.00  
% 43.38/6.00  fof(f4,axiom,(
% 43.38/6.00    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 43.38/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.38/6.00  
% 43.38/6.00  fof(f23,plain,(
% 43.38/6.00    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 43.38/6.00    inference(ennf_transformation,[],[f4])).
% 43.38/6.00  
% 43.38/6.00  fof(f24,plain,(
% 43.38/6.00    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 43.38/6.00    inference(flattening,[],[f23])).
% 43.38/6.00  
% 43.38/6.00  fof(f85,plain,(
% 43.38/6.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 43.38/6.00    inference(cnf_transformation,[],[f24])).
% 43.38/6.00  
% 43.38/6.00  fof(f10,axiom,(
% 43.38/6.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 43.38/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.38/6.00  
% 43.38/6.00  fof(f31,plain,(
% 43.38/6.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 43.38/6.00    inference(ennf_transformation,[],[f10])).
% 43.38/6.00  
% 43.38/6.00  fof(f32,plain,(
% 43.38/6.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 43.38/6.00    inference(flattening,[],[f31])).
% 43.38/6.00  
% 43.38/6.00  fof(f103,plain,(
% 43.38/6.00    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 43.38/6.00    inference(cnf_transformation,[],[f32])).
% 43.38/6.00  
% 43.38/6.00  fof(f1,axiom,(
% 43.38/6.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 43.38/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.38/6.00  
% 43.38/6.00  fof(f21,plain,(
% 43.38/6.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 43.38/6.00    inference(ennf_transformation,[],[f1])).
% 43.38/6.00  
% 43.38/6.00  fof(f51,plain,(
% 43.38/6.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 43.38/6.00    inference(nnf_transformation,[],[f21])).
% 43.38/6.00  
% 43.38/6.00  fof(f52,plain,(
% 43.38/6.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 43.38/6.00    inference(rectify,[],[f51])).
% 43.38/6.00  
% 43.38/6.00  fof(f53,plain,(
% 43.38/6.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 43.38/6.00    introduced(choice_axiom,[])).
% 43.38/6.00  
% 43.38/6.00  fof(f54,plain,(
% 43.38/6.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 43.38/6.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f52,f53])).
% 43.38/6.00  
% 43.38/6.00  fof(f75,plain,(
% 43.38/6.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 43.38/6.00    inference(cnf_transformation,[],[f54])).
% 43.38/6.00  
% 43.38/6.00  fof(f3,axiom,(
% 43.38/6.00    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 43.38/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.38/6.00  
% 43.38/6.00  fof(f22,plain,(
% 43.38/6.00    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 43.38/6.00    inference(ennf_transformation,[],[f3])).
% 43.38/6.00  
% 43.38/6.00  fof(f57,plain,(
% 43.38/6.00    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 43.38/6.00    inference(nnf_transformation,[],[f22])).
% 43.38/6.00  
% 43.38/6.00  fof(f82,plain,(
% 43.38/6.00    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 43.38/6.00    inference(cnf_transformation,[],[f57])).
% 43.38/6.00  
% 43.38/6.00  fof(f118,plain,(
% 43.38/6.00    ~v2_struct_0(sK7)),
% 43.38/6.00    inference(cnf_transformation,[],[f74])).
% 43.38/6.00  
% 43.38/6.00  fof(f13,axiom,(
% 43.38/6.00    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 43.38/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.38/6.00  
% 43.38/6.00  fof(f35,plain,(
% 43.38/6.00    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 43.38/6.00    inference(ennf_transformation,[],[f13])).
% 43.38/6.00  
% 43.38/6.00  fof(f36,plain,(
% 43.38/6.00    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 43.38/6.00    inference(flattening,[],[f35])).
% 43.38/6.00  
% 43.38/6.00  fof(f107,plain,(
% 43.38/6.00    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 43.38/6.00    inference(cnf_transformation,[],[f36])).
% 43.38/6.00  
% 43.38/6.00  fof(f111,plain,(
% 43.38/6.00    ( ! [X0] : (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK6(X0)) | ~v7_struct_0(X0) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 43.38/6.00    inference(cnf_transformation,[],[f70])).
% 43.38/6.00  
% 43.38/6.00  fof(f17,axiom,(
% 43.38/6.00    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => (k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)))))),
% 43.38/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.38/6.00  
% 43.38/6.00  fof(f42,plain,(
% 43.38/6.00    ! [X0] : (! [X1] : (! [X2] : ((k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 43.38/6.00    inference(ennf_transformation,[],[f17])).
% 43.38/6.00  
% 43.38/6.00  fof(f43,plain,(
% 43.38/6.00    ! [X0] : (! [X1] : (! [X2] : ((k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 43.38/6.00    inference(flattening,[],[f42])).
% 43.38/6.00  
% 43.38/6.00  fof(f71,plain,(
% 43.38/6.00    ! [X0] : (! [X1] : (! [X2] : (((k1_tex_2(X0,X1) = X2 | u1_struct_0(X2) != k6_domain_1(u1_struct_0(X0),X1)) & (u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) | k1_tex_2(X0,X1) != X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 43.38/6.00    inference(nnf_transformation,[],[f43])).
% 43.38/6.00  
% 43.38/6.00  fof(f113,plain,(
% 43.38/6.00    ( ! [X2,X0,X1] : (u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) | k1_tex_2(X0,X1) != X2 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 43.38/6.00    inference(cnf_transformation,[],[f71])).
% 43.38/6.00  
% 43.38/6.00  fof(f127,plain,(
% 43.38/6.00    ( ! [X0,X1] : (u1_struct_0(k1_tex_2(X0,X1)) = k6_domain_1(u1_struct_0(X0),X1) | ~m1_pre_topc(k1_tex_2(X0,X1),X0) | ~v1_pre_topc(k1_tex_2(X0,X1)) | v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 43.38/6.00    inference(equality_resolution,[],[f113])).
% 43.38/6.00  
% 43.38/6.00  fof(f115,plain,(
% 43.38/6.00    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 43.38/6.00    inference(cnf_transformation,[],[f45])).
% 43.38/6.00  
% 43.38/6.00  fof(f116,plain,(
% 43.38/6.00    ( ! [X0,X1] : (v1_pre_topc(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 43.38/6.00    inference(cnf_transformation,[],[f45])).
% 43.38/6.00  
% 43.38/6.00  cnf(c_40,plain,
% 43.38/6.00      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
% 43.38/6.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 43.38/6.00      | v2_struct_0(X0)
% 43.38/6.00      | ~ l1_pre_topc(X0) ),
% 43.38/6.00      inference(cnf_transformation,[],[f117]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_83683,plain,
% 43.38/6.00      ( m1_pre_topc(k1_tex_2(sK7,sK6(sK8)),sK7)
% 43.38/6.00      | ~ m1_subset_1(sK6(sK8),u1_struct_0(sK7))
% 43.38/6.00      | v2_struct_0(sK7)
% 43.38/6.00      | ~ l1_pre_topc(sK7) ),
% 43.38/6.00      inference(instantiation,[status(thm)],[c_40]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_3048,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_49768,plain,
% 43.38/6.00      ( X0 != X1 | u1_struct_0(sK8) != X1 | u1_struct_0(sK8) = X0 ),
% 43.38/6.00      inference(instantiation,[status(thm)],[c_3048]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_50356,plain,
% 43.38/6.00      ( X0 != k2_struct_0(sK8)
% 43.38/6.00      | u1_struct_0(sK8) = X0
% 43.38/6.00      | u1_struct_0(sK8) != k2_struct_0(sK8) ),
% 43.38/6.00      inference(instantiation,[status(thm)],[c_49768]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_57797,plain,
% 43.38/6.00      ( u1_struct_0(k1_tex_2(sK7,sK6(sK8))) != k2_struct_0(sK8)
% 43.38/6.00      | u1_struct_0(sK8) = u1_struct_0(k1_tex_2(sK7,sK6(sK8)))
% 43.38/6.00      | u1_struct_0(sK8) != k2_struct_0(sK8) ),
% 43.38/6.00      inference(instantiation,[status(thm)],[c_50356]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_34,plain,
% 43.38/6.00      ( ~ m1_pre_topc(X0,X1)
% 43.38/6.00      | ~ m1_pre_topc(X2,X1)
% 43.38/6.00      | ~ l1_pre_topc(X1)
% 43.38/6.00      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
% 43.38/6.00      | u1_struct_0(X2) != u1_struct_0(X0) ),
% 43.38/6.00      inference(cnf_transformation,[],[f109]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_52280,plain,
% 43.38/6.00      ( ~ m1_pre_topc(k1_tex_2(sK7,sK6(sK8)),X0)
% 43.38/6.00      | ~ m1_pre_topc(sK8,X0)
% 43.38/6.00      | ~ l1_pre_topc(X0)
% 43.38/6.00      | g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) = g1_pre_topc(u1_struct_0(k1_tex_2(sK7,sK6(sK8))),u1_pre_topc(k1_tex_2(sK7,sK6(sK8))))
% 43.38/6.00      | u1_struct_0(sK8) != u1_struct_0(k1_tex_2(sK7,sK6(sK8))) ),
% 43.38/6.00      inference(instantiation,[status(thm)],[c_34]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_52283,plain,
% 43.38/6.00      ( ~ m1_pre_topc(k1_tex_2(sK7,sK6(sK8)),sK7)
% 43.38/6.00      | ~ m1_pre_topc(sK8,sK7)
% 43.38/6.00      | ~ l1_pre_topc(sK7)
% 43.38/6.00      | g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) = g1_pre_topc(u1_struct_0(k1_tex_2(sK7,sK6(sK8))),u1_pre_topc(k1_tex_2(sK7,sK6(sK8))))
% 43.38/6.00      | u1_struct_0(sK8) != u1_struct_0(k1_tex_2(sK7,sK6(sK8))) ),
% 43.38/6.00      inference(instantiation,[status(thm)],[c_52280]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_43,negated_conjecture,
% 43.38/6.00      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 43.38/6.00      | g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK7,X0)),u1_pre_topc(k1_tex_2(sK7,X0))) ),
% 43.38/6.00      inference(cnf_transformation,[],[f123]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_27846,plain,
% 43.38/6.00      ( ~ m1_subset_1(sK6(sK8),u1_struct_0(sK7))
% 43.38/6.00      | g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK7,sK6(sK8))),u1_pre_topc(k1_tex_2(sK7,sK6(sK8)))) ),
% 43.38/6.00      inference(instantiation,[status(thm)],[c_43]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_3050,plain,
% 43.38/6.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 43.38/6.00      theory(equality) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_4076,plain,
% 43.38/6.00      ( ~ r2_hidden(X0,X1)
% 43.38/6.00      | r2_hidden(X2,u1_struct_0(sK7))
% 43.38/6.00      | X2 != X0
% 43.38/6.00      | u1_struct_0(sK7) != X1 ),
% 43.38/6.00      inference(instantiation,[status(thm)],[c_3050]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_4332,plain,
% 43.38/6.00      ( r2_hidden(X0,u1_struct_0(sK7))
% 43.38/6.00      | ~ r2_hidden(X1,k2_struct_0(sK7))
% 43.38/6.00      | X0 != X1
% 43.38/6.00      | u1_struct_0(sK7) != k2_struct_0(sK7) ),
% 43.38/6.00      inference(instantiation,[status(thm)],[c_4076]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_12875,plain,
% 43.38/6.00      ( r2_hidden(X0,u1_struct_0(sK7))
% 43.38/6.00      | ~ r2_hidden(sK6(sK8),k2_struct_0(sK7))
% 43.38/6.00      | X0 != sK6(sK8)
% 43.38/6.00      | u1_struct_0(sK7) != k2_struct_0(sK7) ),
% 43.38/6.00      inference(instantiation,[status(thm)],[c_4332]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_18390,plain,
% 43.38/6.00      ( r2_hidden(sK6(sK8),u1_struct_0(sK7))
% 43.38/6.00      | ~ r2_hidden(sK6(sK8),k2_struct_0(sK7))
% 43.38/6.00      | sK6(sK8) != sK6(sK8)
% 43.38/6.00      | u1_struct_0(sK7) != k2_struct_0(sK7) ),
% 43.38/6.00      inference(instantiation,[status(thm)],[c_12875]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_44,negated_conjecture,
% 43.38/6.00      ( m1_pre_topc(sK8,sK7) ),
% 43.38/6.00      inference(cnf_transformation,[],[f122]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_3795,plain,
% 43.38/6.00      ( m1_pre_topc(sK8,sK7) = iProver_top ),
% 43.38/6.00      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_24,plain,
% 43.38/6.00      ( sP1(X0,X1) | ~ l1_pre_topc(X1) | ~ l1_pre_topc(X0) ),
% 43.38/6.00      inference(cnf_transformation,[],[f99]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_13,plain,
% 43.38/6.00      ( ~ sP1(X0,X1) | sP0(X1,X0) | ~ m1_pre_topc(X1,X0) ),
% 43.38/6.00      inference(cnf_transformation,[],[f87]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_543,plain,
% 43.38/6.00      ( sP0(X0,X1)
% 43.38/6.00      | ~ m1_pre_topc(X0,X1)
% 43.38/6.00      | ~ l1_pre_topc(X1)
% 43.38/6.00      | ~ l1_pre_topc(X0) ),
% 43.38/6.00      inference(resolution,[status(thm)],[c_24,c_13]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_26,plain,
% 43.38/6.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 43.38/6.00      inference(cnf_transformation,[],[f101]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_547,plain,
% 43.38/6.00      ( ~ l1_pre_topc(X1) | ~ m1_pre_topc(X0,X1) | sP0(X0,X1) ),
% 43.38/6.00      inference(global_propositional_subsumption,
% 43.38/6.00                [status(thm)],
% 43.38/6.00                [c_543,c_26]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_548,plain,
% 43.38/6.00      ( sP0(X0,X1) | ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) ),
% 43.38/6.00      inference(renaming,[status(thm)],[c_547]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_3788,plain,
% 43.38/6.00      ( sP0(X0,X1) = iProver_top
% 43.38/6.00      | m1_pre_topc(X0,X1) != iProver_top
% 43.38/6.00      | l1_pre_topc(X1) != iProver_top ),
% 43.38/6.00      inference(predicate_to_equality,[status(thm)],[c_548]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_5136,plain,
% 43.38/6.00      ( sP0(sK8,sK7) = iProver_top | l1_pre_topc(sK7) != iProver_top ),
% 43.38/6.00      inference(superposition,[status(thm)],[c_3795,c_3788]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_47,negated_conjecture,
% 43.38/6.00      ( l1_pre_topc(sK7) ),
% 43.38/6.00      inference(cnf_transformation,[],[f119]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_50,plain,
% 43.38/6.00      ( l1_pre_topc(sK7) = iProver_top ),
% 43.38/6.00      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_5214,plain,
% 43.38/6.00      ( sP0(sK8,sK7) = iProver_top ),
% 43.38/6.00      inference(global_propositional_subsumption,
% 43.38/6.00                [status(thm)],
% 43.38/6.00                [c_5136,c_50]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_23,plain,
% 43.38/6.00      ( ~ sP0(X0,X1) | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
% 43.38/6.00      inference(cnf_transformation,[],[f89]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_3806,plain,
% 43.38/6.00      ( sP0(X0,X1) != iProver_top
% 43.38/6.00      | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) = iProver_top ),
% 43.38/6.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_3805,plain,
% 43.38/6.00      ( m1_pre_topc(X0,X1) != iProver_top
% 43.38/6.00      | l1_pre_topc(X1) != iProver_top
% 43.38/6.00      | l1_pre_topc(X0) = iProver_top ),
% 43.38/6.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_4507,plain,
% 43.38/6.00      ( l1_pre_topc(sK7) != iProver_top
% 43.38/6.00      | l1_pre_topc(sK8) = iProver_top ),
% 43.38/6.00      inference(superposition,[status(thm)],[c_3795,c_3805]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_53,plain,
% 43.38/6.00      ( m1_pre_topc(sK8,sK7) = iProver_top ),
% 43.38/6.00      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_3968,plain,
% 43.38/6.00      ( ~ m1_pre_topc(sK8,X0) | ~ l1_pre_topc(X0) | l1_pre_topc(sK8) ),
% 43.38/6.00      inference(instantiation,[status(thm)],[c_26]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_3969,plain,
% 43.38/6.00      ( m1_pre_topc(sK8,X0) != iProver_top
% 43.38/6.00      | l1_pre_topc(X0) != iProver_top
% 43.38/6.00      | l1_pre_topc(sK8) = iProver_top ),
% 43.38/6.00      inference(predicate_to_equality,[status(thm)],[c_3968]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_3971,plain,
% 43.38/6.00      ( m1_pre_topc(sK8,sK7) != iProver_top
% 43.38/6.00      | l1_pre_topc(sK7) != iProver_top
% 43.38/6.00      | l1_pre_topc(sK8) = iProver_top ),
% 43.38/6.00      inference(instantiation,[status(thm)],[c_3969]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_4624,plain,
% 43.38/6.00      ( l1_pre_topc(sK8) = iProver_top ),
% 43.38/6.00      inference(global_propositional_subsumption,
% 43.38/6.00                [status(thm)],
% 43.38/6.00                [c_4507,c_50,c_53,c_3971]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_25,plain,
% 43.38/6.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 43.38/6.00      inference(cnf_transformation,[],[f100]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_11,plain,
% 43.38/6.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 43.38/6.00      inference(cnf_transformation,[],[f86]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_776,plain,
% 43.38/6.00      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 43.38/6.00      inference(resolution,[status(thm)],[c_25,c_11]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_3782,plain,
% 43.38/6.00      ( u1_struct_0(X0) = k2_struct_0(X0)
% 43.38/6.00      | l1_pre_topc(X0) != iProver_top ),
% 43.38/6.00      inference(predicate_to_equality,[status(thm)],[c_776]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_4628,plain,
% 43.38/6.00      ( u1_struct_0(sK8) = k2_struct_0(sK8) ),
% 43.38/6.00      inference(superposition,[status(thm)],[c_4624,c_3782]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_37,plain,
% 43.38/6.00      ( m1_subset_1(sK6(X0),u1_struct_0(X0))
% 43.38/6.00      | ~ v7_struct_0(X0)
% 43.38/6.00      | v2_struct_0(X0)
% 43.38/6.00      | ~ l1_struct_0(X0) ),
% 43.38/6.00      inference(cnf_transformation,[],[f110]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_716,plain,
% 43.38/6.00      ( m1_subset_1(sK6(X0),u1_struct_0(X0))
% 43.38/6.00      | ~ v7_struct_0(X0)
% 43.38/6.00      | v2_struct_0(X0)
% 43.38/6.00      | ~ l1_pre_topc(X0) ),
% 43.38/6.00      inference(resolution,[status(thm)],[c_25,c_37]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_3786,plain,
% 43.38/6.00      ( m1_subset_1(sK6(X0),u1_struct_0(X0)) = iProver_top
% 43.38/6.00      | v7_struct_0(X0) != iProver_top
% 43.38/6.00      | v2_struct_0(X0) = iProver_top
% 43.38/6.00      | l1_pre_topc(X0) != iProver_top ),
% 43.38/6.00      inference(predicate_to_equality,[status(thm)],[c_716]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_5268,plain,
% 43.38/6.00      ( m1_subset_1(sK6(sK8),k2_struct_0(sK8)) = iProver_top
% 43.38/6.00      | v7_struct_0(sK8) != iProver_top
% 43.38/6.00      | v2_struct_0(sK8) = iProver_top
% 43.38/6.00      | l1_pre_topc(sK8) != iProver_top ),
% 43.38/6.00      inference(superposition,[status(thm)],[c_4628,c_3786]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_46,negated_conjecture,
% 43.38/6.00      ( ~ v2_struct_0(sK8) ),
% 43.38/6.00      inference(cnf_transformation,[],[f120]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_51,plain,
% 43.38/6.00      ( v2_struct_0(sK8) != iProver_top ),
% 43.38/6.00      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_45,negated_conjecture,
% 43.38/6.00      ( v7_struct_0(sK8) ),
% 43.38/6.00      inference(cnf_transformation,[],[f121]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_52,plain,
% 43.38/6.00      ( v7_struct_0(sK8) = iProver_top ),
% 43.38/6.00      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_5859,plain,
% 43.38/6.00      ( m1_subset_1(sK6(sK8),k2_struct_0(sK8)) = iProver_top ),
% 43.38/6.00      inference(global_propositional_subsumption,
% 43.38/6.00                [status(thm)],
% 43.38/6.00                [c_5268,c_50,c_51,c_52,c_53,c_3971]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_10,plain,
% 43.38/6.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 43.38/6.00      inference(cnf_transformation,[],[f85]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_3816,plain,
% 43.38/6.00      ( m1_subset_1(X0,X1) != iProver_top
% 43.38/6.00      | r2_hidden(X0,X1) = iProver_top
% 43.38/6.00      | v1_xboole_0(X1) = iProver_top ),
% 43.38/6.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_5865,plain,
% 43.38/6.00      ( r2_hidden(sK6(sK8),k2_struct_0(sK8)) = iProver_top
% 43.38/6.00      | v1_xboole_0(k2_struct_0(sK8)) = iProver_top ),
% 43.38/6.00      inference(superposition,[status(thm)],[c_5859,c_3816]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_28,plain,
% 43.38/6.00      ( v2_struct_0(X0)
% 43.38/6.00      | ~ l1_struct_0(X0)
% 43.38/6.00      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 43.38/6.00      inference(cnf_transformation,[],[f103]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_750,plain,
% 43.38/6.00      ( v2_struct_0(X0)
% 43.38/6.00      | ~ l1_pre_topc(X0)
% 43.38/6.00      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 43.38/6.00      inference(resolution,[status(thm)],[c_25,c_28]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_3784,plain,
% 43.38/6.00      ( v2_struct_0(X0) = iProver_top
% 43.38/6.00      | l1_pre_topc(X0) != iProver_top
% 43.38/6.00      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 43.38/6.00      inference(predicate_to_equality,[status(thm)],[c_750]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_4927,plain,
% 43.38/6.00      ( v2_struct_0(sK8) = iProver_top
% 43.38/6.00      | l1_pre_topc(sK8) != iProver_top
% 43.38/6.00      | v1_xboole_0(k2_struct_0(sK8)) != iProver_top ),
% 43.38/6.00      inference(superposition,[status(thm)],[c_4628,c_3784]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_8510,plain,
% 43.38/6.00      ( r2_hidden(sK6(sK8),k2_struct_0(sK8)) = iProver_top ),
% 43.38/6.00      inference(global_propositional_subsumption,
% 43.38/6.00                [status(thm)],
% 43.38/6.00                [c_5865,c_50,c_51,c_53,c_3971,c_4927]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_2,plain,
% 43.38/6.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 43.38/6.00      inference(cnf_transformation,[],[f75]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_3822,plain,
% 43.38/6.00      ( r2_hidden(X0,X1) != iProver_top
% 43.38/6.00      | r2_hidden(X0,X2) = iProver_top
% 43.38/6.00      | r1_tarski(X1,X2) != iProver_top ),
% 43.38/6.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_8514,plain,
% 43.38/6.00      ( r2_hidden(sK6(sK8),X0) = iProver_top
% 43.38/6.00      | r1_tarski(k2_struct_0(sK8),X0) != iProver_top ),
% 43.38/6.00      inference(superposition,[status(thm)],[c_8510,c_3822]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_8623,plain,
% 43.38/6.00      ( sP0(sK8,X0) != iProver_top
% 43.38/6.00      | r2_hidden(sK6(sK8),k2_struct_0(X0)) = iProver_top ),
% 43.38/6.00      inference(superposition,[status(thm)],[c_3806,c_8514]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_8628,plain,
% 43.38/6.00      ( sP0(sK8,X0) != iProver_top
% 43.38/6.00      | r2_hidden(sK6(sK8),X1) = iProver_top
% 43.38/6.00      | r1_tarski(k2_struct_0(X0),X1) != iProver_top ),
% 43.38/6.00      inference(superposition,[status(thm)],[c_8623,c_3822]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_10878,plain,
% 43.38/6.00      ( sP0(X0,X1) != iProver_top
% 43.38/6.00      | sP0(sK8,X0) != iProver_top
% 43.38/6.00      | r2_hidden(sK6(sK8),k2_struct_0(X1)) = iProver_top ),
% 43.38/6.00      inference(superposition,[status(thm)],[c_3806,c_8628]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_11093,plain,
% 43.38/6.00      ( sP0(sK8,sK8) != iProver_top
% 43.38/6.00      | r2_hidden(sK6(sK8),k2_struct_0(sK7)) = iProver_top ),
% 43.38/6.00      inference(superposition,[status(thm)],[c_5214,c_10878]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_8625,plain,
% 43.38/6.00      ( sP0(sK8,sK7) != iProver_top
% 43.38/6.00      | r2_hidden(sK6(sK8),k2_struct_0(sK7)) = iProver_top ),
% 43.38/6.00      inference(instantiation,[status(thm)],[c_8623]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_11255,plain,
% 43.38/6.00      ( r2_hidden(sK6(sK8),k2_struct_0(sK7)) = iProver_top ),
% 43.38/6.00      inference(global_propositional_subsumption,
% 43.38/6.00                [status(thm)],
% 43.38/6.00                [c_11093,c_50,c_5136,c_8625]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_8,plain,
% 43.38/6.00      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 43.38/6.00      inference(cnf_transformation,[],[f82]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_3817,plain,
% 43.38/6.00      ( m1_subset_1(X0,X1) = iProver_top
% 43.38/6.00      | r2_hidden(X0,X1) != iProver_top
% 43.38/6.00      | v1_xboole_0(X1) = iProver_top ),
% 43.38/6.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_11260,plain,
% 43.38/6.00      ( m1_subset_1(sK6(sK8),k2_struct_0(sK7)) = iProver_top
% 43.38/6.00      | v1_xboole_0(k2_struct_0(sK7)) = iProver_top ),
% 43.38/6.00      inference(superposition,[status(thm)],[c_11255,c_3817]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_48,negated_conjecture,
% 43.38/6.00      ( ~ v2_struct_0(sK7) ),
% 43.38/6.00      inference(cnf_transformation,[],[f118]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_49,plain,
% 43.38/6.00      ( v2_struct_0(sK7) != iProver_top ),
% 43.38/6.00      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_3792,plain,
% 43.38/6.00      ( l1_pre_topc(sK7) = iProver_top ),
% 43.38/6.00      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_4195,plain,
% 43.38/6.00      ( u1_struct_0(sK7) = k2_struct_0(sK7) ),
% 43.38/6.00      inference(superposition,[status(thm)],[c_3792,c_3782]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_4448,plain,
% 43.38/6.00      ( v2_struct_0(sK7) = iProver_top
% 43.38/6.00      | l1_pre_topc(sK7) != iProver_top
% 43.38/6.00      | v1_xboole_0(k2_struct_0(sK7)) != iProver_top ),
% 43.38/6.00      inference(superposition,[status(thm)],[c_4195,c_3784]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_8629,plain,
% 43.38/6.00      ( sP0(sK8,X0) != iProver_top
% 43.38/6.00      | m1_subset_1(sK6(sK8),k2_struct_0(X0)) = iProver_top
% 43.38/6.00      | v1_xboole_0(k2_struct_0(X0)) = iProver_top ),
% 43.38/6.00      inference(superposition,[status(thm)],[c_8623,c_3817]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_8634,plain,
% 43.38/6.00      ( sP0(sK8,sK7) != iProver_top
% 43.38/6.00      | m1_subset_1(sK6(sK8),k2_struct_0(sK7)) = iProver_top
% 43.38/6.00      | v1_xboole_0(k2_struct_0(sK7)) = iProver_top ),
% 43.38/6.00      inference(instantiation,[status(thm)],[c_8629]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_11528,plain,
% 43.38/6.00      ( m1_subset_1(sK6(sK8),k2_struct_0(sK7)) = iProver_top ),
% 43.38/6.00      inference(global_propositional_subsumption,
% 43.38/6.00                [status(thm)],
% 43.38/6.00                [c_11260,c_49,c_50,c_4448,c_5136,c_8634]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_32,plain,
% 43.38/6.00      ( ~ m1_subset_1(X0,X1)
% 43.38/6.00      | v1_xboole_0(X1)
% 43.38/6.00      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 43.38/6.00      inference(cnf_transformation,[],[f107]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_3803,plain,
% 43.38/6.00      ( k6_domain_1(X0,X1) = k1_tarski(X1)
% 43.38/6.00      | m1_subset_1(X1,X0) != iProver_top
% 43.38/6.00      | v1_xboole_0(X0) = iProver_top ),
% 43.38/6.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_11532,plain,
% 43.38/6.00      ( k6_domain_1(k2_struct_0(sK7),sK6(sK8)) = k1_tarski(sK6(sK8))
% 43.38/6.00      | v1_xboole_0(k2_struct_0(sK7)) = iProver_top ),
% 43.38/6.00      inference(superposition,[status(thm)],[c_11528,c_3803]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_5863,plain,
% 43.38/6.00      ( k6_domain_1(k2_struct_0(sK8),sK6(sK8)) = k1_tarski(sK6(sK8))
% 43.38/6.00      | v1_xboole_0(k2_struct_0(sK8)) = iProver_top ),
% 43.38/6.00      inference(superposition,[status(thm)],[c_5859,c_3803]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_3794,plain,
% 43.38/6.00      ( v7_struct_0(sK8) = iProver_top ),
% 43.38/6.00      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_36,plain,
% 43.38/6.00      ( ~ v7_struct_0(X0)
% 43.38/6.00      | v2_struct_0(X0)
% 43.38/6.00      | ~ l1_struct_0(X0)
% 43.38/6.00      | k6_domain_1(u1_struct_0(X0),sK6(X0)) = u1_struct_0(X0) ),
% 43.38/6.00      inference(cnf_transformation,[],[f111]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_733,plain,
% 43.38/6.00      ( ~ v7_struct_0(X0)
% 43.38/6.00      | v2_struct_0(X0)
% 43.38/6.00      | ~ l1_pre_topc(X0)
% 43.38/6.00      | k6_domain_1(u1_struct_0(X0),sK6(X0)) = u1_struct_0(X0) ),
% 43.38/6.00      inference(resolution,[status(thm)],[c_25,c_36]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_3785,plain,
% 43.38/6.00      ( k6_domain_1(u1_struct_0(X0),sK6(X0)) = u1_struct_0(X0)
% 43.38/6.00      | v7_struct_0(X0) != iProver_top
% 43.38/6.00      | v2_struct_0(X0) = iProver_top
% 43.38/6.00      | l1_pre_topc(X0) != iProver_top ),
% 43.38/6.00      inference(predicate_to_equality,[status(thm)],[c_733]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_4630,plain,
% 43.38/6.00      ( k6_domain_1(u1_struct_0(sK8),sK6(sK8)) = u1_struct_0(sK8)
% 43.38/6.00      | v2_struct_0(sK8) = iProver_top
% 43.38/6.00      | l1_pre_topc(sK8) != iProver_top ),
% 43.38/6.00      inference(superposition,[status(thm)],[c_3794,c_3785]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_4631,plain,
% 43.38/6.00      ( k6_domain_1(k2_struct_0(sK8),sK6(sK8)) = k2_struct_0(sK8)
% 43.38/6.00      | v2_struct_0(sK8) = iProver_top
% 43.38/6.00      | l1_pre_topc(sK8) != iProver_top ),
% 43.38/6.00      inference(light_normalisation,[status(thm)],[c_4630,c_4628]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_5019,plain,
% 43.38/6.00      ( k6_domain_1(k2_struct_0(sK8),sK6(sK8)) = k2_struct_0(sK8) ),
% 43.38/6.00      inference(global_propositional_subsumption,
% 43.38/6.00                [status(thm)],
% 43.38/6.00                [c_4631,c_50,c_51,c_53,c_3971]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_5866,plain,
% 43.38/6.00      ( k1_tarski(sK6(sK8)) = k2_struct_0(sK8)
% 43.38/6.00      | v1_xboole_0(k2_struct_0(sK8)) = iProver_top ),
% 43.38/6.00      inference(light_normalisation,[status(thm)],[c_5863,c_5019]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_6470,plain,
% 43.38/6.00      ( k1_tarski(sK6(sK8)) = k2_struct_0(sK8) ),
% 43.38/6.00      inference(global_propositional_subsumption,
% 43.38/6.00                [status(thm)],
% 43.38/6.00                [c_5866,c_50,c_51,c_53,c_3971,c_4927]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_39,plain,
% 43.38/6.00      ( ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
% 43.38/6.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 43.38/6.00      | ~ v1_pre_topc(k1_tex_2(X0,X1))
% 43.38/6.00      | v2_struct_0(X0)
% 43.38/6.00      | v2_struct_0(k1_tex_2(X0,X1))
% 43.38/6.00      | ~ l1_pre_topc(X0)
% 43.38/6.00      | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) ),
% 43.38/6.00      inference(cnf_transformation,[],[f127]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_274,plain,
% 43.38/6.00      ( ~ m1_subset_1(X1,u1_struct_0(X0))
% 43.38/6.00      | ~ v1_pre_topc(k1_tex_2(X0,X1))
% 43.38/6.00      | v2_struct_0(X0)
% 43.38/6.00      | v2_struct_0(k1_tex_2(X0,X1))
% 43.38/6.00      | ~ l1_pre_topc(X0)
% 43.38/6.00      | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) ),
% 43.38/6.00      inference(global_propositional_subsumption,
% 43.38/6.00                [status(thm)],
% 43.38/6.00                [c_39,c_40]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_275,plain,
% 43.38/6.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 43.38/6.00      | ~ v1_pre_topc(k1_tex_2(X1,X0))
% 43.38/6.00      | v2_struct_0(X1)
% 43.38/6.00      | v2_struct_0(k1_tex_2(X1,X0))
% 43.38/6.00      | ~ l1_pre_topc(X1)
% 43.38/6.00      | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
% 43.38/6.00      inference(renaming,[status(thm)],[c_274]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_42,plain,
% 43.38/6.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 43.38/6.00      | v2_struct_0(X1)
% 43.38/6.00      | ~ v2_struct_0(k1_tex_2(X1,X0))
% 43.38/6.00      | ~ l1_pre_topc(X1) ),
% 43.38/6.00      inference(cnf_transformation,[],[f115]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_41,plain,
% 43.38/6.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 43.38/6.00      | v1_pre_topc(k1_tex_2(X1,X0))
% 43.38/6.00      | v2_struct_0(X1)
% 43.38/6.00      | ~ l1_pre_topc(X1) ),
% 43.38/6.00      inference(cnf_transformation,[],[f116]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_280,plain,
% 43.38/6.00      ( v2_struct_0(X1)
% 43.38/6.00      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 43.38/6.00      | ~ l1_pre_topc(X1)
% 43.38/6.00      | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
% 43.38/6.00      inference(global_propositional_subsumption,
% 43.38/6.00                [status(thm)],
% 43.38/6.00                [c_275,c_42,c_41]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_281,plain,
% 43.38/6.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 43.38/6.00      | v2_struct_0(X1)
% 43.38/6.00      | ~ l1_pre_topc(X1)
% 43.38/6.00      | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
% 43.38/6.00      inference(renaming,[status(thm)],[c_280]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_3790,plain,
% 43.38/6.00      ( k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1))
% 43.38/6.00      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 43.38/6.00      | v2_struct_0(X0) = iProver_top
% 43.38/6.00      | l1_pre_topc(X0) != iProver_top ),
% 43.38/6.00      inference(predicate_to_equality,[status(thm)],[c_281]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_7420,plain,
% 43.38/6.00      ( k6_domain_1(u1_struct_0(sK7),X0) = u1_struct_0(k1_tex_2(sK7,X0))
% 43.38/6.00      | m1_subset_1(X0,k2_struct_0(sK7)) != iProver_top
% 43.38/6.00      | v2_struct_0(sK7) = iProver_top
% 43.38/6.00      | l1_pre_topc(sK7) != iProver_top ),
% 43.38/6.00      inference(superposition,[status(thm)],[c_4195,c_3790]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_7421,plain,
% 43.38/6.00      ( k6_domain_1(k2_struct_0(sK7),X0) = u1_struct_0(k1_tex_2(sK7,X0))
% 43.38/6.00      | m1_subset_1(X0,k2_struct_0(sK7)) != iProver_top
% 43.38/6.00      | v2_struct_0(sK7) = iProver_top
% 43.38/6.00      | l1_pre_topc(sK7) != iProver_top ),
% 43.38/6.00      inference(light_normalisation,[status(thm)],[c_7420,c_4195]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_8284,plain,
% 43.38/6.00      ( k6_domain_1(k2_struct_0(sK7),X0) = u1_struct_0(k1_tex_2(sK7,X0))
% 43.38/6.00      | m1_subset_1(X0,k2_struct_0(sK7)) != iProver_top ),
% 43.38/6.00      inference(global_propositional_subsumption,
% 43.38/6.00                [status(thm)],
% 43.38/6.00                [c_7421,c_49,c_50]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_9915,plain,
% 43.38/6.00      ( k6_domain_1(k2_struct_0(sK7),sK6(sK8)) = u1_struct_0(k1_tex_2(sK7,sK6(sK8)))
% 43.38/6.00      | sP0(sK8,sK7) != iProver_top
% 43.38/6.00      | v1_xboole_0(k2_struct_0(sK7)) = iProver_top ),
% 43.38/6.00      inference(superposition,[status(thm)],[c_8629,c_8284]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_10239,plain,
% 43.38/6.00      ( k6_domain_1(k2_struct_0(sK7),sK6(sK8)) = u1_struct_0(k1_tex_2(sK7,sK6(sK8))) ),
% 43.38/6.00      inference(global_propositional_subsumption,
% 43.38/6.00                [status(thm)],
% 43.38/6.00                [c_9915,c_49,c_50,c_4448,c_5136]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_11537,plain,
% 43.38/6.00      ( k6_domain_1(k2_struct_0(sK7),sK6(sK8)) = k2_struct_0(sK8)
% 43.38/6.00      | v1_xboole_0(k2_struct_0(sK7)) = iProver_top ),
% 43.38/6.00      inference(light_normalisation,
% 43.38/6.00                [status(thm)],
% 43.38/6.00                [c_11532,c_6470,c_10239]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_11538,plain,
% 43.38/6.00      ( u1_struct_0(k1_tex_2(sK7,sK6(sK8))) = k2_struct_0(sK8)
% 43.38/6.00      | v1_xboole_0(k2_struct_0(sK7)) = iProver_top ),
% 43.38/6.00      inference(demodulation,[status(thm)],[c_11537,c_10239]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_8624,plain,
% 43.38/6.00      ( ~ sP0(sK8,X0) | r2_hidden(sK6(sK8),k2_struct_0(X0)) ),
% 43.38/6.00      inference(predicate_to_equality_rev,[status(thm)],[c_8623]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_8626,plain,
% 43.38/6.00      ( ~ sP0(sK8,sK7) | r2_hidden(sK6(sK8),k2_struct_0(sK7)) ),
% 43.38/6.00      inference(instantiation,[status(thm)],[c_8624]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_4115,plain,
% 43.38/6.00      ( m1_subset_1(X0,u1_struct_0(X1))
% 43.38/6.00      | ~ r2_hidden(X0,u1_struct_0(X1))
% 43.38/6.00      | v1_xboole_0(u1_struct_0(X1)) ),
% 43.38/6.00      inference(instantiation,[status(thm)],[c_8]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_5597,plain,
% 43.38/6.00      ( m1_subset_1(sK6(sK8),u1_struct_0(X0))
% 43.38/6.00      | ~ r2_hidden(sK6(sK8),u1_struct_0(X0))
% 43.38/6.00      | v1_xboole_0(u1_struct_0(X0)) ),
% 43.38/6.00      inference(instantiation,[status(thm)],[c_4115]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_5599,plain,
% 43.38/6.00      ( m1_subset_1(sK6(sK8),u1_struct_0(sK7))
% 43.38/6.00      | ~ r2_hidden(sK6(sK8),u1_struct_0(sK7))
% 43.38/6.00      | v1_xboole_0(u1_struct_0(sK7)) ),
% 43.38/6.00      inference(instantiation,[status(thm)],[c_5597]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_5140,plain,
% 43.38/6.00      ( sP0(sK8,sK7) | ~ l1_pre_topc(sK7) ),
% 43.38/6.00      inference(predicate_to_equality_rev,[status(thm)],[c_5136]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_3047,plain,( X0 = X0 ),theory(equality) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_4737,plain,
% 43.38/6.00      ( sK6(sK8) = sK6(sK8) ),
% 43.38/6.00      inference(instantiation,[status(thm)],[c_3047]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_143,plain,
% 43.38/6.00      ( ~ l1_struct_0(sK7) | u1_struct_0(sK7) = k2_struct_0(sK7) ),
% 43.38/6.00      inference(instantiation,[status(thm)],[c_11]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_101,plain,
% 43.38/6.00      ( ~ l1_pre_topc(sK7) | l1_struct_0(sK7) ),
% 43.38/6.00      inference(instantiation,[status(thm)],[c_25]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(c_96,plain,
% 43.38/6.00      ( v2_struct_0(sK7)
% 43.38/6.00      | ~ l1_struct_0(sK7)
% 43.38/6.00      | ~ v1_xboole_0(u1_struct_0(sK7)) ),
% 43.38/6.00      inference(instantiation,[status(thm)],[c_28]) ).
% 43.38/6.00  
% 43.38/6.00  cnf(contradiction,plain,
% 43.38/6.00      ( $false ),
% 43.38/6.00      inference(minisat,
% 43.38/6.00                [status(thm)],
% 43.38/6.00                [c_83683,c_57797,c_52283,c_27846,c_18390,c_11538,c_8626,
% 43.38/6.00                 c_5599,c_5140,c_4737,c_4628,c_4448,c_143,c_101,c_96,
% 43.38/6.00                 c_44,c_50,c_47,c_49,c_48]) ).
% 43.38/6.00  
% 43.38/6.00  
% 43.38/6.00  % SZS output end CNFRefutation for theBenchmark.p
% 43.38/6.00  
% 43.38/6.00  ------                               Statistics
% 43.38/6.00  
% 43.38/6.00  ------ General
% 43.38/6.00  
% 43.38/6.00  abstr_ref_over_cycles:                  0
% 43.38/6.00  abstr_ref_under_cycles:                 0
% 43.38/6.00  gc_basic_clause_elim:                   0
% 43.38/6.00  forced_gc_time:                         0
% 43.38/6.00  parsing_time:                           0.009
% 43.38/6.00  unif_index_cands_time:                  0.
% 43.38/6.00  unif_index_add_time:                    0.
% 43.38/6.00  orderings_time:                         0.
% 43.38/6.00  out_proof_time:                         0.016
% 43.38/6.00  total_time:                             5.036
% 43.38/6.00  num_of_symbols:                         59
% 43.38/6.00  num_of_terms:                           49435
% 43.38/6.00  
% 43.38/6.00  ------ Preprocessing
% 43.38/6.00  
% 43.38/6.00  num_of_splits:                          0
% 43.38/6.00  num_of_split_atoms:                     0
% 43.38/6.00  num_of_reused_defs:                     0
% 43.38/6.00  num_eq_ax_congr_red:                    48
% 43.38/6.00  num_of_sem_filtered_clauses:            1
% 43.38/6.00  num_of_subtypes:                        0
% 43.38/6.00  monotx_restored_types:                  0
% 43.38/6.00  sat_num_of_epr_types:                   0
% 43.38/6.00  sat_num_of_non_cyclic_types:            0
% 43.38/6.00  sat_guarded_non_collapsed_types:        0
% 43.38/6.00  num_pure_diseq_elim:                    0
% 43.38/6.00  simp_replaced_by:                       0
% 43.38/6.00  res_preprocessed:                       215
% 43.38/6.00  prep_upred:                             0
% 43.38/6.00  prep_unflattend:                        15
% 43.38/6.00  smt_new_axioms:                         0
% 43.38/6.00  pred_elim_cands:                        10
% 43.38/6.00  pred_elim:                              2
% 43.38/6.00  pred_elim_cl:                           2
% 43.38/6.00  pred_elim_cycles:                       9
% 43.38/6.00  merged_defs:                            0
% 43.38/6.00  merged_defs_ncl:                        0
% 43.38/6.00  bin_hyper_res:                          0
% 43.38/6.00  prep_cycles:                            4
% 43.38/6.00  pred_elim_time:                         0.056
% 43.38/6.00  splitting_time:                         0.
% 43.38/6.00  sem_filter_time:                        0.
% 43.38/6.00  monotx_time:                            0.001
% 43.38/6.00  subtype_inf_time:                       0.
% 43.38/6.00  
% 43.38/6.00  ------ Problem properties
% 43.38/6.00  
% 43.38/6.00  clauses:                                44
% 43.38/6.00  conjectures:                            6
% 43.38/6.00  epr:                                    16
% 43.38/6.00  horn:                                   29
% 43.38/6.00  ground:                                 5
% 43.38/6.00  unary:                                  6
% 43.38/6.00  binary:                                 6
% 43.38/6.00  lits:                                   141
% 43.38/6.00  lits_eq:                                14
% 43.38/6.00  fd_pure:                                0
% 43.38/6.00  fd_pseudo:                              0
% 43.38/6.00  fd_cond:                                0
% 43.38/6.00  fd_pseudo_cond:                         2
% 43.38/6.00  ac_symbols:                             0
% 43.38/6.00  
% 43.38/6.00  ------ Propositional Solver
% 43.38/6.00  
% 43.38/6.00  prop_solver_calls:                      44
% 43.38/6.00  prop_fast_solver_calls:                 11320
% 43.38/6.00  smt_solver_calls:                       0
% 43.38/6.00  smt_fast_solver_calls:                  0
% 43.38/6.00  prop_num_of_clauses:                    34486
% 43.38/6.00  prop_preprocess_simplified:             62313
% 43.38/6.00  prop_fo_subsumed:                       360
% 43.38/6.00  prop_solver_time:                       0.
% 43.38/6.00  smt_solver_time:                        0.
% 43.38/6.00  smt_fast_solver_time:                   0.
% 43.38/6.00  prop_fast_solver_time:                  0.
% 43.38/6.00  prop_unsat_core_time:                   0.002
% 43.38/6.00  
% 43.38/6.00  ------ QBF
% 43.38/6.00  
% 43.38/6.00  qbf_q_res:                              0
% 43.38/6.00  qbf_num_tautologies:                    0
% 43.38/6.00  qbf_prep_cycles:                        0
% 43.38/6.00  
% 43.38/6.00  ------ BMC1
% 43.38/6.00  
% 43.38/6.00  bmc1_current_bound:                     -1
% 43.38/6.00  bmc1_last_solved_bound:                 -1
% 43.38/6.00  bmc1_unsat_core_size:                   -1
% 43.38/6.00  bmc1_unsat_core_parents_size:           -1
% 43.38/6.00  bmc1_merge_next_fun:                    0
% 43.38/6.00  bmc1_unsat_core_clauses_time:           0.
% 43.38/6.00  
% 43.38/6.00  ------ Instantiation
% 43.38/6.00  
% 43.38/6.00  inst_num_of_clauses:                    3161
% 43.38/6.00  inst_num_in_passive:                    1589
% 43.38/6.00  inst_num_in_active:                     3737
% 43.38/6.00  inst_num_in_unprocessed:                105
% 43.38/6.00  inst_num_of_loops:                      4710
% 43.38/6.00  inst_num_of_learning_restarts:          1
% 43.38/6.00  inst_num_moves_active_passive:          966
% 43.38/6.00  inst_lit_activity:                      0
% 43.38/6.00  inst_lit_activity_moves:                0
% 43.38/6.00  inst_num_tautologies:                   0
% 43.38/6.00  inst_num_prop_implied:                  0
% 43.38/6.00  inst_num_existing_simplified:           0
% 43.38/6.00  inst_num_eq_res_simplified:             0
% 43.38/6.00  inst_num_child_elim:                    0
% 43.38/6.00  inst_num_of_dismatching_blockings:      4826
% 43.38/6.00  inst_num_of_non_proper_insts:           9971
% 43.38/6.00  inst_num_of_duplicates:                 0
% 43.38/6.00  inst_inst_num_from_inst_to_res:         0
% 43.38/6.00  inst_dismatching_checking_time:         0.
% 43.38/6.00  
% 43.38/6.00  ------ Resolution
% 43.38/6.00  
% 43.38/6.00  res_num_of_clauses:                     62
% 43.38/6.00  res_num_in_passive:                     62
% 43.38/6.00  res_num_in_active:                      0
% 43.38/6.00  res_num_of_loops:                       219
% 43.38/6.00  res_forward_subset_subsumed:            191
% 43.38/6.00  res_backward_subset_subsumed:           0
% 43.38/6.00  res_forward_subsumed:                   0
% 43.38/6.00  res_backward_subsumed:                  0
% 43.38/6.00  res_forward_subsumption_resolution:     1
% 43.38/6.00  res_backward_subsumption_resolution:    0
% 43.38/6.00  res_clause_to_clause_subsumption:       27330
% 43.38/6.00  res_orphan_elimination:                 0
% 43.38/6.00  res_tautology_del:                      1258
% 43.38/6.00  res_num_eq_res_simplified:              0
% 43.38/6.00  res_num_sel_changes:                    0
% 43.38/6.00  res_moves_from_active_to_pass:          0
% 43.38/6.00  
% 43.38/6.00  ------ Superposition
% 43.38/6.00  
% 43.38/6.00  sup_time_total:                         0.
% 43.38/6.00  sup_time_generating:                    0.
% 43.38/6.00  sup_time_sim_full:                      0.
% 43.38/6.00  sup_time_sim_immed:                     0.
% 43.38/6.00  
% 43.38/6.00  sup_num_of_clauses:                     5800
% 43.38/6.00  sup_num_in_active:                      898
% 43.38/6.00  sup_num_in_passive:                     4902
% 43.38/6.00  sup_num_of_loops:                       942
% 43.38/6.00  sup_fw_superposition:                   3775
% 43.38/6.00  sup_bw_superposition:                   4930
% 43.38/6.00  sup_immediate_simplified:               2375
% 43.38/6.00  sup_given_eliminated:                   19
% 43.38/6.00  comparisons_done:                       0
% 43.38/6.00  comparisons_avoided:                    532
% 43.38/6.00  
% 43.38/6.00  ------ Simplifications
% 43.38/6.00  
% 43.38/6.00  
% 43.38/6.00  sim_fw_subset_subsumed:                 958
% 43.38/6.00  sim_bw_subset_subsumed:                 86
% 43.38/6.00  sim_fw_subsumed:                        592
% 43.38/6.00  sim_bw_subsumed:                        268
% 43.38/6.00  sim_fw_subsumption_res:                 0
% 43.38/6.00  sim_bw_subsumption_res:                 0
% 43.38/6.00  sim_tautology_del:                      418
% 43.38/6.00  sim_eq_tautology_del:                   108
% 43.38/6.00  sim_eq_res_simp:                        0
% 43.38/6.00  sim_fw_demodulated:                     12
% 43.38/6.00  sim_bw_demodulated:                     9
% 43.38/6.00  sim_light_normalised:                   751
% 43.38/6.00  sim_joinable_taut:                      0
% 43.38/6.00  sim_joinable_simp:                      0
% 43.38/6.00  sim_ac_normalised:                      0
% 43.38/6.00  sim_smt_subsumption:                    0
% 43.38/6.00  
%------------------------------------------------------------------------------
