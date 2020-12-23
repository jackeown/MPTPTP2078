%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:24 EST 2020

% Result     : Theorem 11.60s
% Output     : CNFRefutation 11.60s
% Verified   : 
% Statistics : Number of formulae       :  243 (3726 expanded)
%              Number of clauses        :  157 (1181 expanded)
%              Number of leaves         :   25 (1021 expanded)
%              Depth                    :   26
%              Number of atoms          :  807 (17003 expanded)
%              Number of equality atoms :  343 (3884 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f34,plain,(
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

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f21,f35,f34])).

fof(f79,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f16,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( ( v1_tex_2(X1,X0)
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
               => v1_tex_2(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( ( v1_tex_2(X1,X0)
                    & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
                 => v1_tex_2(X2,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,X0)
              & v1_tex_2(X1,X0)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,X0)
              & v1_tex_2(X1,X0)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v1_tex_2(X2,X0)
          & v1_tex_2(X1,X0)
          & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
          & m1_pre_topc(X2,X0) )
     => ( ~ v1_tex_2(sK8,X0)
        & v1_tex_2(X1,X0)
        & g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
        & m1_pre_topc(sK8,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,X0)
              & v1_tex_2(X1,X0)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
     => ( ? [X2] :
            ( ~ v1_tex_2(X2,X0)
            & v1_tex_2(sK7,X0)
            & g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
            & m1_pre_topc(X2,X0) )
        & m1_pre_topc(sK7,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v1_tex_2(X2,X0)
                & v1_tex_2(X1,X0)
                & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                & m1_pre_topc(X2,X0) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,sK6)
              & v1_tex_2(X1,sK6)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,sK6) )
          & m1_pre_topc(X1,sK6) )
      & l1_pre_topc(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ~ v1_tex_2(sK8,sK6)
    & v1_tex_2(sK7,sK6)
    & g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) = g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))
    & m1_pre_topc(sK8,sK6)
    & m1_pre_topc(sK7,sK6)
    & l1_pre_topc(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f33,f56,f55,f54])).

fof(f96,plain,(
    m1_pre_topc(sK8,sK6) ),
    inference(cnf_transformation,[],[f57])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f83,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f94,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f57])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f82,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f66,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f95,plain,(
    m1_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f57])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f97,plain,(
    g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) = g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) ),
    inference(cnf_transformation,[],[f57])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( m1_pre_topc(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ m1_pre_topc(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f67,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f46,plain,(
    ! [X5,X1,X0] :
      ( ? [X7] :
          ( k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5
          & r2_hidden(X7,u1_pre_topc(X1))
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5
        & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1))
        & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2
          & r2_hidden(X4,u1_pre_topc(X1))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = X2
        & r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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
              ( k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1)
              | ~ r2_hidden(X3,u1_pre_topc(X1))
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(sK2(X0,X1),u1_pre_topc(X0)) )
        & ( ? [X4] :
              ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = sK2(X0,X1)
              & r2_hidden(X4,u1_pre_topc(X1))
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
          | r2_hidden(sK2(X0,X1),u1_pre_topc(X0)) )
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1)
                | ~ r2_hidden(X3,u1_pre_topc(X1))
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r2_hidden(sK2(X0,X1),u1_pre_topc(X0)) )
          & ( ( k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = sK2(X0,X1)
              & r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
              & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) )
            | r2_hidden(sK2(X0,X1),u1_pre_topc(X0)) )
          & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
      & ( ( ! [X5] :
              ( ( ( r2_hidden(X5,u1_pre_topc(X0))
                  | ! [X6] :
                      ( k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5
                      | ~ r2_hidden(X6,u1_pre_topc(X1))
                      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ( k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5
                    & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1))
                    & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ r2_hidden(X5,u1_pre_topc(X0)) ) )
              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f43,f46,f45,f44])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f60,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2) )
             => ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_pre_topc(X0,X1) = X2
                  | k2_struct_0(X2) != X1 )
                & ( k2_struct_0(X2) = X1
                  | k1_pre_topc(X0,X1) != X2 ) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X2) = X1
      | k1_pre_topc(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f103,plain,(
    ! [X0,X1] :
      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v1_subset_1(X2,u1_struct_0(X0))
                  | u1_struct_0(X1) != X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f49])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK5(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK5(X0,X1)
        & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ( ~ v1_subset_1(sK5(X0,X1),u1_struct_0(X0))
                & u1_struct_0(X1) = sK5(X0,X1)
                & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f50,f51])).

fof(f90,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | u1_struct_0(X1) = sK5(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f99,plain,(
    ~ v1_tex_2(sK8,sK6) ),
    inference(cnf_transformation,[],[f57])).

fof(f89,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f93,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f91,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | ~ v1_subset_1(sK5(X0,X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f88,plain,(
    ! [X0,X3,X1] :
      ( v1_subset_1(X3,u1_struct_0(X0))
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f105,plain,(
    ! [X0,X1] :
      ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f88])).

fof(f98,plain,(
    v1_tex_2(sK7,sK6) ),
    inference(cnf_transformation,[],[f57])).

fof(f4,axiom,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f4])).

cnf(c_21,plain,
    ( sP1(X0,X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1220,plain,
    ( sP1(X0,X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_39,negated_conjecture,
    ( m1_pre_topc(sK8,sK6) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1206,plain,
    ( m1_pre_topc(sK8,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_25,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1216,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2379,plain,
    ( l1_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_1206,c_1216])).

cnf(c_41,negated_conjecture,
    ( l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_42,plain,
    ( l1_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_1646,plain,
    ( ~ l1_pre_topc(sK6)
    | l1_pre_topc(sK8) ),
    inference(resolution,[status(thm)],[c_25,c_39])).

cnf(c_1647,plain,
    ( l1_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1646])).

cnf(c_2547,plain,
    ( l1_pre_topc(sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2379,c_42,c_1647])).

cnf(c_24,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1217,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2553,plain,
    ( l1_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2547,c_1217])).

cnf(c_8,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1233,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2631,plain,
    ( u1_struct_0(sK8) = k2_struct_0(sK8) ),
    inference(superposition,[status(thm)],[c_2553,c_1233])).

cnf(c_4,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1236,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1256,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1236,c_3])).

cnf(c_22,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1219,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4469,plain,
    ( m1_pre_topc(k1_pre_topc(X0,u1_struct_0(X0)),X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1256,c_1219])).

cnf(c_9906,plain,
    ( m1_pre_topc(k1_pre_topc(sK8,k2_struct_0(sK8)),sK8) = iProver_top
    | l1_pre_topc(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_2631,c_4469])).

cnf(c_12370,plain,
    ( m1_pre_topc(k1_pre_topc(sK8,k2_struct_0(sK8)),sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9906,c_42,c_1647])).

cnf(c_28,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_322,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_28,c_25])).

cnf(c_323,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_322])).

cnf(c_1203,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_323])).

cnf(c_3159,plain,
    ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK8),u1_pre_topc(sK8))) = iProver_top
    | m1_pre_topc(X0,sK8) != iProver_top
    | l1_pre_topc(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_2631,c_1203])).

cnf(c_14298,plain,
    ( m1_pre_topc(X0,sK8) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK8),u1_pre_topc(sK8))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3159,c_42,c_1647])).

cnf(c_14299,plain,
    ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK8),u1_pre_topc(sK8))) = iProver_top
    | m1_pre_topc(X0,sK8) != iProver_top ),
    inference(renaming,[status(thm)],[c_14298])).

cnf(c_40,negated_conjecture,
    ( m1_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1205,plain,
    ( m1_pre_topc(sK7,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_2380,plain,
    ( l1_pre_topc(sK7) = iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1205,c_1216])).

cnf(c_1648,plain,
    ( l1_pre_topc(sK7)
    | ~ l1_pre_topc(sK6) ),
    inference(resolution,[status(thm)],[c_25,c_40])).

cnf(c_1649,plain,
    ( l1_pre_topc(sK7) = iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1648])).

cnf(c_2560,plain,
    ( l1_pre_topc(sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2380,c_42,c_1649])).

cnf(c_2566,plain,
    ( l1_struct_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_2560,c_1217])).

cnf(c_2634,plain,
    ( u1_struct_0(sK7) = k2_struct_0(sK7) ),
    inference(superposition,[status(thm)],[c_2566,c_1233])).

cnf(c_26,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1215,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4432,plain,
    ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
    | m1_pre_topc(X0,sK7) = iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2634,c_1215])).

cnf(c_38,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) = g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_2950,plain,
    ( g1_pre_topc(k2_struct_0(sK8),u1_pre_topc(sK8)) = g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) ),
    inference(demodulation,[status(thm)],[c_2631,c_38])).

cnf(c_4025,plain,
    ( g1_pre_topc(k2_struct_0(sK7),u1_pre_topc(sK7)) = g1_pre_topc(k2_struct_0(sK8),u1_pre_topc(sK8)) ),
    inference(demodulation,[status(thm)],[c_2634,c_2950])).

cnf(c_4450,plain,
    ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK8),u1_pre_topc(sK8))) != iProver_top
    | m1_pre_topc(X0,sK7) = iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4432,c_4025])).

cnf(c_5011,plain,
    ( m1_pre_topc(X0,sK7) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK8),u1_pre_topc(sK8))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4450,c_42,c_1649])).

cnf(c_5012,plain,
    ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK8),u1_pre_topc(sK8))) != iProver_top
    | m1_pre_topc(X0,sK7) = iProver_top ),
    inference(renaming,[status(thm)],[c_5011])).

cnf(c_14309,plain,
    ( m1_pre_topc(X0,sK7) = iProver_top
    | m1_pre_topc(X0,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_14299,c_5012])).

cnf(c_15252,plain,
    ( m1_pre_topc(k1_pre_topc(sK8,k2_struct_0(sK8)),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_12370,c_14309])).

cnf(c_10,plain,
    ( ~ sP1(X0,X1)
    | sP0(X1,X0)
    | ~ m1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1231,plain,
    ( sP1(X0,X1) != iProver_top
    | sP0(X1,X0) = iProver_top
    | m1_pre_topc(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_27989,plain,
    ( sP1(sK7,k1_pre_topc(sK8,k2_struct_0(sK8))) != iProver_top
    | sP0(k1_pre_topc(sK8,k2_struct_0(sK8)),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_15252,c_1231])).

cnf(c_29102,plain,
    ( sP0(k1_pre_topc(sK8,k2_struct_0(sK8)),sK7) = iProver_top
    | l1_pre_topc(k1_pre_topc(sK8,k2_struct_0(sK8))) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1220,c_27989])).

cnf(c_9907,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(k1_pre_topc(X0,u1_struct_0(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4469,c_1216])).

cnf(c_10909,plain,
    ( l1_pre_topc(k1_pre_topc(sK8,k2_struct_0(sK8))) = iProver_top
    | l1_pre_topc(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_2631,c_9907])).

cnf(c_42032,plain,
    ( sP0(k1_pre_topc(sK8,k2_struct_0(sK8)),sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_29102,c_42,c_1647,c_1649,c_10909])).

cnf(c_20,plain,
    ( ~ sP0(X0,X1)
    | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1221,plain,
    ( sP0(X0,X1) != iProver_top
    | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1238,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2479,plain,
    ( k2_struct_0(X0) = k2_struct_0(X1)
    | sP0(X1,X0) != iProver_top
    | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1221,c_1238])).

cnf(c_21006,plain,
    ( k2_struct_0(X0) = k2_struct_0(X1)
    | sP0(X1,X0) != iProver_top
    | sP0(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1221,c_2479])).

cnf(c_42037,plain,
    ( k2_struct_0(k1_pre_topc(sK8,k2_struct_0(sK8))) = k2_struct_0(sK7)
    | sP0(sK7,k1_pre_topc(sK8,k2_struct_0(sK8))) != iProver_top ),
    inference(superposition,[status(thm)],[c_42032,c_21006])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(k1_pre_topc(X0,X1))
    | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_354,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(k1_pre_topc(X0,X1))
    | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7,c_22])).

cnf(c_355,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(k1_pre_topc(X1,X0))
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(renaming,[status(thm)],[c_354])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(k1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_360,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_355,c_23])).

cnf(c_361,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(renaming,[status(thm)],[c_360])).

cnf(c_1201,plain,
    ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_361])).

cnf(c_1768,plain,
    ( k2_struct_0(k1_pre_topc(X0,u1_struct_0(X0))) = u1_struct_0(X0)
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1256,c_1201])).

cnf(c_2552,plain,
    ( k2_struct_0(k1_pre_topc(sK8,u1_struct_0(sK8))) = u1_struct_0(sK8) ),
    inference(superposition,[status(thm)],[c_2547,c_1768])).

cnf(c_2949,plain,
    ( k2_struct_0(k1_pre_topc(sK8,k2_struct_0(sK8))) = k2_struct_0(sK8) ),
    inference(demodulation,[status(thm)],[c_2631,c_2552])).

cnf(c_42044,plain,
    ( k2_struct_0(sK7) = k2_struct_0(sK8)
    | sP0(sK7,k1_pre_topc(sK8,k2_struct_0(sK8))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_42037,c_2949])).

cnf(c_43,plain,
    ( m1_pre_topc(sK7,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_29,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1214,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4467,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(k1_pre_topc(X1,u1_struct_0(X0)),X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1214,c_1219])).

cnf(c_24342,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(k1_pre_topc(X1,u1_struct_0(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4467,c_1216])).

cnf(c_24634,plain,
    ( m1_pre_topc(sK7,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(k1_pre_topc(X0,k2_struct_0(sK7))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2634,c_24342])).

cnf(c_24698,plain,
    ( m1_pre_topc(sK7,sK6) != iProver_top
    | l1_pre_topc(k1_pre_topc(sK6,k2_struct_0(sK7))) = iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_24634])).

cnf(c_1204,plain,
    ( l1_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_1775,plain,
    ( l1_struct_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1204,c_1217])).

cnf(c_1917,plain,
    ( u1_struct_0(sK6) = k2_struct_0(sK6) ),
    inference(superposition,[status(thm)],[c_1775,c_1233])).

cnf(c_3411,plain,
    ( m1_pre_topc(X0,sK6) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK6))) = iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1917,c_1214])).

cnf(c_6115,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK6))) = iProver_top
    | m1_pre_topc(X0,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3411,c_42])).

cnf(c_6116,plain,
    ( m1_pre_topc(X0,sK6) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK6))) = iProver_top ),
    inference(renaming,[status(thm)],[c_6115])).

cnf(c_4472,plain,
    ( m1_pre_topc(k1_pre_topc(sK6,X0),sK6) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6))) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1917,c_1219])).

cnf(c_6456,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6))) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK6,X0),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4472,c_42])).

cnf(c_6457,plain,
    ( m1_pre_topc(k1_pre_topc(sK6,X0),sK6) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6456])).

cnf(c_6465,plain,
    ( m1_pre_topc(X0,sK6) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK6,u1_struct_0(X0)),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_6116,c_6457])).

cnf(c_29382,plain,
    ( m1_pre_topc(k1_pre_topc(sK6,k2_struct_0(sK7)),sK6) = iProver_top
    | m1_pre_topc(sK7,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2634,c_6465])).

cnf(c_4031,plain,
    ( m1_pre_topc(sK7,X0) != iProver_top
    | m1_subset_1(k2_struct_0(sK7),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2634,c_1214])).

cnf(c_22974,plain,
    ( m1_pre_topc(k1_pre_topc(X0,k2_struct_0(sK7)),X0) = iProver_top
    | m1_pre_topc(sK7,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4031,c_1219])).

cnf(c_23026,plain,
    ( m1_pre_topc(k1_pre_topc(sK6,k2_struct_0(sK7)),sK6) = iProver_top
    | m1_pre_topc(sK7,sK6) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_22974])).

cnf(c_29956,plain,
    ( m1_pre_topc(k1_pre_topc(sK6,k2_struct_0(sK7)),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_29382,c_42,c_43,c_23026])).

cnf(c_29964,plain,
    ( sP1(sK6,k1_pre_topc(sK6,k2_struct_0(sK7))) != iProver_top
    | sP0(k1_pre_topc(sK6,k2_struct_0(sK7)),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_29956,c_1231])).

cnf(c_30613,plain,
    ( sP0(k1_pre_topc(sK6,k2_struct_0(sK7)),sK6) = iProver_top
    | l1_pre_topc(k1_pre_topc(sK6,k2_struct_0(sK7))) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1220,c_29964])).

cnf(c_2002,plain,
    ( k2_struct_0(k1_pre_topc(sK6,X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6))) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1917,c_1201])).

cnf(c_2007,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6))) != iProver_top
    | k2_struct_0(k1_pre_topc(sK6,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2002,c_42])).

cnf(c_2008,plain,
    ( k2_struct_0(k1_pre_topc(sK6,X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2007])).

cnf(c_6127,plain,
    ( k2_struct_0(k1_pre_topc(sK6,u1_struct_0(X0))) = u1_struct_0(X0)
    | m1_pre_topc(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_6116,c_2008])).

cnf(c_13863,plain,
    ( k2_struct_0(k1_pre_topc(sK6,u1_struct_0(sK7))) = u1_struct_0(sK7) ),
    inference(superposition,[status(thm)],[c_1205,c_6127])).

cnf(c_13872,plain,
    ( k2_struct_0(k1_pre_topc(sK6,k2_struct_0(sK7))) = k2_struct_0(sK7) ),
    inference(light_normalisation,[status(thm)],[c_13863,c_2634])).

cnf(c_31,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK5(X1,X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1212,plain,
    ( sK5(X0,X1) = u1_struct_0(X1)
    | v1_tex_2(X1,X0) = iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_4832,plain,
    ( sK5(sK6,sK8) = u1_struct_0(sK8)
    | v1_tex_2(sK8,sK6) = iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1206,c_1212])).

cnf(c_4846,plain,
    ( sK5(sK6,sK8) = k2_struct_0(sK8)
    | v1_tex_2(sK8,sK6) = iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4832,c_2631])).

cnf(c_36,negated_conjecture,
    ( ~ v1_tex_2(sK8,sK6) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_46,plain,
    ( v1_tex_2(sK8,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_5022,plain,
    ( sK5(sK6,sK8) = k2_struct_0(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4846,c_42,c_46])).

cnf(c_32,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | m1_subset_1(sK5(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1211,plain,
    ( v1_tex_2(X0,X1) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(sK5(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_5025,plain,
    ( v1_tex_2(sK8,sK6) = iProver_top
    | m1_pre_topc(sK8,sK6) != iProver_top
    | m1_subset_1(k2_struct_0(sK8),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5022,c_1211])).

cnf(c_5026,plain,
    ( v1_tex_2(sK8,sK6) = iProver_top
    | m1_pre_topc(sK8,sK6) != iProver_top
    | m1_subset_1(k2_struct_0(sK8),k1_zfmisc_1(k2_struct_0(sK6))) = iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5025,c_1917])).

cnf(c_44,plain,
    ( m1_pre_topc(sK8,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_8731,plain,
    ( m1_subset_1(k2_struct_0(sK8),k1_zfmisc_1(k2_struct_0(sK6))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5026,c_42,c_44,c_46])).

cnf(c_34,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1210,plain,
    ( X0 = X1
    | v1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_8736,plain,
    ( k2_struct_0(sK8) = k2_struct_0(sK6)
    | v1_subset_1(k2_struct_0(sK8),k2_struct_0(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8731,c_1210])).

cnf(c_30,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_subset_1(sK5(X1,X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1213,plain,
    ( v1_tex_2(X0,X1) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | v1_subset_1(sK5(X1,X0),u1_struct_0(X1)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_5345,plain,
    ( v1_tex_2(sK8,sK6) = iProver_top
    | m1_pre_topc(sK8,sK6) != iProver_top
    | v1_subset_1(k2_struct_0(sK8),u1_struct_0(sK6)) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5022,c_1213])).

cnf(c_5377,plain,
    ( v1_tex_2(sK8,sK6) = iProver_top
    | m1_pre_topc(sK8,sK6) != iProver_top
    | v1_subset_1(k2_struct_0(sK8),k2_struct_0(sK6)) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5345,c_1917])).

cnf(c_9422,plain,
    ( k2_struct_0(sK8) = k2_struct_0(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8736,c_42,c_44,c_46,c_5377])).

cnf(c_9645,plain,
    ( sP0(X0,sK6) != iProver_top
    | r1_tarski(k2_struct_0(X0),k2_struct_0(sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9422,c_1221])).

cnf(c_11980,plain,
    ( k2_struct_0(X0) = k2_struct_0(sK8)
    | sP0(X0,sK6) != iProver_top
    | r1_tarski(k2_struct_0(sK8),k2_struct_0(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9645,c_1238])).

cnf(c_32157,plain,
    ( k2_struct_0(k1_pre_topc(sK6,k2_struct_0(sK7))) = k2_struct_0(sK8)
    | sP0(k1_pre_topc(sK6,k2_struct_0(sK7)),sK6) != iProver_top
    | r1_tarski(k2_struct_0(sK8),k2_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13872,c_11980])).

cnf(c_32171,plain,
    ( k2_struct_0(sK7) = k2_struct_0(sK8)
    | sP0(k1_pre_topc(sK6,k2_struct_0(sK7)),sK6) != iProver_top
    | r1_tarski(k2_struct_0(sK8),k2_struct_0(sK7)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_32157,c_13872])).

cnf(c_4215,plain,
    ( sP0(k1_pre_topc(sK8,k2_struct_0(sK8)),X0) != iProver_top
    | r1_tarski(k2_struct_0(sK8),k2_struct_0(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2949,c_1221])).

cnf(c_42039,plain,
    ( r1_tarski(k2_struct_0(sK8),k2_struct_0(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_42032,c_4215])).

cnf(c_43516,plain,
    ( k2_struct_0(sK7) = k2_struct_0(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_42044,c_42,c_43,c_24698,c_30613,c_32171,c_42039])).

cnf(c_10912,plain,
    ( l1_struct_0(k1_pre_topc(X0,u1_struct_0(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9907,c_1217])).

cnf(c_11799,plain,
    ( u1_struct_0(k1_pre_topc(X0,u1_struct_0(X0))) = k2_struct_0(k1_pre_topc(X0,u1_struct_0(X0)))
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10912,c_1233])).

cnf(c_14805,plain,
    ( u1_struct_0(k1_pre_topc(sK6,u1_struct_0(sK6))) = k2_struct_0(k1_pre_topc(sK6,u1_struct_0(sK6))) ),
    inference(superposition,[status(thm)],[c_1204,c_11799])).

cnf(c_8739,plain,
    ( k2_struct_0(k1_pre_topc(sK6,k2_struct_0(sK8))) = k2_struct_0(sK8) ),
    inference(superposition,[status(thm)],[c_8731,c_2008])).

cnf(c_9452,plain,
    ( u1_struct_0(sK6) = k2_struct_0(sK8) ),
    inference(demodulation,[status(thm)],[c_9422,c_1917])).

cnf(c_14826,plain,
    ( u1_struct_0(k1_pre_topc(sK6,k2_struct_0(sK8))) = k2_struct_0(sK8) ),
    inference(light_normalisation,[status(thm)],[c_14805,c_8739,c_9452])).

cnf(c_33,plain,
    ( ~ v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_343,plain,
    ( v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_tex_2(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_33,c_29])).

cnf(c_344,plain,
    ( ~ v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_343])).

cnf(c_1202,plain,
    ( v1_tex_2(X0,X1) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_344])).

cnf(c_4032,plain,
    ( v1_tex_2(sK7,X0) != iProver_top
    | m1_pre_topc(sK7,X0) != iProver_top
    | v1_subset_1(k2_struct_0(sK7),u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2634,c_1202])).

cnf(c_24157,plain,
    ( v1_tex_2(sK7,k1_pre_topc(sK6,k2_struct_0(sK8))) != iProver_top
    | m1_pre_topc(sK7,k1_pre_topc(sK6,k2_struct_0(sK8))) != iProver_top
    | v1_subset_1(k2_struct_0(sK7),k2_struct_0(sK8)) = iProver_top
    | l1_pre_topc(k1_pre_topc(sK6,k2_struct_0(sK8))) != iProver_top ),
    inference(superposition,[status(thm)],[c_14826,c_4032])).

cnf(c_37,negated_conjecture,
    ( v1_tex_2(sK7,sK6) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_45,plain,
    ( v1_tex_2(sK7,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_24154,plain,
    ( v1_tex_2(sK7,sK6) != iProver_top
    | m1_pre_topc(sK7,sK6) != iProver_top
    | v1_subset_1(k2_struct_0(sK7),k2_struct_0(sK8)) = iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_9452,c_4032])).

cnf(c_25488,plain,
    ( v1_subset_1(k2_struct_0(sK7),k2_struct_0(sK8)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24157,c_42,c_43,c_45,c_24154])).

cnf(c_43555,plain,
    ( v1_subset_1(k2_struct_0(sK8),k2_struct_0(sK8)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_43516,c_25488])).

cnf(c_5,plain,
    ( ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1235,plain,
    ( v1_subset_1(k2_subset_1(X0),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1253,plain,
    ( v1_subset_1(X0,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1235,c_3])).

cnf(c_44850,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_43555,c_1253])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:45:45 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.60/1.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.60/1.98  
% 11.60/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.60/1.98  
% 11.60/1.98  ------  iProver source info
% 11.60/1.98  
% 11.60/1.98  git: date: 2020-06-30 10:37:57 +0100
% 11.60/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.60/1.98  git: non_committed_changes: false
% 11.60/1.98  git: last_make_outside_of_git: false
% 11.60/1.98  
% 11.60/1.98  ------ 
% 11.60/1.98  ------ Parsing...
% 11.60/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.60/1.98  
% 11.60/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 11.60/1.98  
% 11.60/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.60/1.98  
% 11.60/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.60/1.98  ------ Proving...
% 11.60/1.98  ------ Problem Properties 
% 11.60/1.98  
% 11.60/1.98  
% 11.60/1.98  clauses                                 40
% 11.60/1.98  conjectures                             6
% 11.60/1.98  EPR                                     12
% 11.60/1.98  Horn                                    33
% 11.60/1.98  unary                                   10
% 11.60/1.98  binary                                  4
% 11.60/1.98  lits                                    113
% 11.60/1.98  lits eq                                 11
% 11.60/1.98  fd_pure                                 0
% 11.60/1.98  fd_pseudo                               0
% 11.60/1.98  fd_cond                                 0
% 11.60/1.98  fd_pseudo_cond                          2
% 11.60/1.98  AC symbols                              0
% 11.60/1.98  
% 11.60/1.98  ------ Input Options Time Limit: Unbounded
% 11.60/1.98  
% 11.60/1.98  
% 11.60/1.98  ------ 
% 11.60/1.98  Current options:
% 11.60/1.98  ------ 
% 11.60/1.98  
% 11.60/1.98  
% 11.60/1.98  
% 11.60/1.98  
% 11.60/1.98  ------ Proving...
% 11.60/1.98  
% 11.60/1.98  
% 11.60/1.98  % SZS status Theorem for theBenchmark.p
% 11.60/1.98  
% 11.60/1.98   Resolution empty clause
% 11.60/1.98  
% 11.60/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 11.60/1.98  
% 11.60/1.98  fof(f7,axiom,(
% 11.60/1.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 11.60/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.98  
% 11.60/1.98  fof(f21,plain,(
% 11.60/1.98    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 11.60/1.98    inference(ennf_transformation,[],[f7])).
% 11.60/1.98  
% 11.60/1.98  fof(f35,plain,(
% 11.60/1.98    ! [X0,X1] : ((m1_pre_topc(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 11.60/1.98    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 11.60/1.98  
% 11.60/1.98  fof(f34,plain,(
% 11.60/1.98    ! [X1,X0] : (sP0(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))),
% 11.60/1.98    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 11.60/1.98  
% 11.60/1.98  fof(f36,plain,(
% 11.60/1.98    ! [X0] : (! [X1] : (sP1(X0,X1) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 11.60/1.98    inference(definition_folding,[],[f21,f35,f34])).
% 11.60/1.98  
% 11.60/1.98  fof(f79,plain,(
% 11.60/1.98    ( ! [X0,X1] : (sP1(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 11.60/1.98    inference(cnf_transformation,[],[f36])).
% 11.60/1.98  
% 11.60/1.98  fof(f16,conjecture,(
% 11.60/1.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ((v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) => v1_tex_2(X2,X0)))))),
% 11.60/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.98  
% 11.60/1.98  fof(f17,negated_conjecture,(
% 11.60/1.98    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ((v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) => v1_tex_2(X2,X0)))))),
% 11.60/1.98    inference(negated_conjecture,[],[f16])).
% 11.60/1.98  
% 11.60/1.98  fof(f32,plain,(
% 11.60/1.98    ? [X0] : (? [X1] : (? [X2] : ((~v1_tex_2(X2,X0) & (v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 11.60/1.98    inference(ennf_transformation,[],[f17])).
% 11.60/1.98  
% 11.60/1.98  fof(f33,plain,(
% 11.60/1.98    ? [X0] : (? [X1] : (? [X2] : (~v1_tex_2(X2,X0) & v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 11.60/1.98    inference(flattening,[],[f32])).
% 11.60/1.98  
% 11.60/1.98  fof(f56,plain,(
% 11.60/1.98    ( ! [X0,X1] : (? [X2] : (~v1_tex_2(X2,X0) & v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,X0)) => (~v1_tex_2(sK8,X0) & v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_pre_topc(sK8,X0))) )),
% 11.60/1.98    introduced(choice_axiom,[])).
% 11.60/1.98  
% 11.60/1.98  fof(f55,plain,(
% 11.60/1.98    ( ! [X0] : (? [X1] : (? [X2] : (~v1_tex_2(X2,X0) & v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) => (? [X2] : (~v1_tex_2(X2,X0) & v1_tex_2(sK7,X0) & g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,X0)) & m1_pre_topc(sK7,X0))) )),
% 11.60/1.98    introduced(choice_axiom,[])).
% 11.60/1.98  
% 11.60/1.98  fof(f54,plain,(
% 11.60/1.98    ? [X0] : (? [X1] : (? [X2] : (~v1_tex_2(X2,X0) & v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tex_2(X2,sK6) & v1_tex_2(X1,sK6) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,sK6)) & m1_pre_topc(X1,sK6)) & l1_pre_topc(sK6))),
% 11.60/1.98    introduced(choice_axiom,[])).
% 11.60/1.98  
% 11.60/1.98  fof(f57,plain,(
% 11.60/1.98    ((~v1_tex_2(sK8,sK6) & v1_tex_2(sK7,sK6) & g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) = g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) & m1_pre_topc(sK8,sK6)) & m1_pre_topc(sK7,sK6)) & l1_pre_topc(sK6)),
% 11.60/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f33,f56,f55,f54])).
% 11.60/1.98  
% 11.60/1.98  fof(f96,plain,(
% 11.60/1.98    m1_pre_topc(sK8,sK6)),
% 11.60/1.98    inference(cnf_transformation,[],[f57])).
% 11.60/1.98  
% 11.60/1.98  fof(f10,axiom,(
% 11.60/1.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 11.60/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.98  
% 11.60/1.98  fof(f25,plain,(
% 11.60/1.98    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 11.60/1.98    inference(ennf_transformation,[],[f10])).
% 11.60/1.98  
% 11.60/1.98  fof(f83,plain,(
% 11.60/1.98    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 11.60/1.98    inference(cnf_transformation,[],[f25])).
% 11.60/1.98  
% 11.60/1.98  fof(f94,plain,(
% 11.60/1.98    l1_pre_topc(sK6)),
% 11.60/1.98    inference(cnf_transformation,[],[f57])).
% 11.60/1.98  
% 11.60/1.98  fof(f9,axiom,(
% 11.60/1.98    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 11.60/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.98  
% 11.60/1.98  fof(f24,plain,(
% 11.60/1.98    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 11.60/1.98    inference(ennf_transformation,[],[f9])).
% 11.60/1.98  
% 11.60/1.98  fof(f82,plain,(
% 11.60/1.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 11.60/1.98    inference(cnf_transformation,[],[f24])).
% 11.60/1.98  
% 11.60/1.98  fof(f6,axiom,(
% 11.60/1.98    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 11.60/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.98  
% 11.60/1.98  fof(f20,plain,(
% 11.60/1.98    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 11.60/1.98    inference(ennf_transformation,[],[f6])).
% 11.60/1.98  
% 11.60/1.98  fof(f66,plain,(
% 11.60/1.98    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 11.60/1.98    inference(cnf_transformation,[],[f20])).
% 11.60/1.98  
% 11.60/1.98  fof(f3,axiom,(
% 11.60/1.98    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 11.60/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.98  
% 11.60/1.98  fof(f62,plain,(
% 11.60/1.98    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 11.60/1.98    inference(cnf_transformation,[],[f3])).
% 11.60/1.98  
% 11.60/1.98  fof(f2,axiom,(
% 11.60/1.98    ! [X0] : k2_subset_1(X0) = X0),
% 11.60/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.98  
% 11.60/1.98  fof(f61,plain,(
% 11.60/1.98    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 11.60/1.98    inference(cnf_transformation,[],[f2])).
% 11.60/1.98  
% 11.60/1.98  fof(f8,axiom,(
% 11.60/1.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 11.60/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.98  
% 11.60/1.98  fof(f22,plain,(
% 11.60/1.98    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 11.60/1.98    inference(ennf_transformation,[],[f8])).
% 11.60/1.98  
% 11.60/1.98  fof(f23,plain,(
% 11.60/1.98    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 11.60/1.98    inference(flattening,[],[f22])).
% 11.60/1.98  
% 11.60/1.98  fof(f81,plain,(
% 11.60/1.98    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.60/1.98    inference(cnf_transformation,[],[f23])).
% 11.60/1.98  
% 11.60/1.98  fof(f12,axiom,(
% 11.60/1.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 11.60/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.98  
% 11.60/1.98  fof(f27,plain,(
% 11.60/1.98    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 11.60/1.98    inference(ennf_transformation,[],[f12])).
% 11.60/1.98  
% 11.60/1.98  fof(f48,plain,(
% 11.60/1.98    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 11.60/1.98    inference(nnf_transformation,[],[f27])).
% 11.60/1.98  
% 11.60/1.98  fof(f85,plain,(
% 11.60/1.98    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 11.60/1.98    inference(cnf_transformation,[],[f48])).
% 11.60/1.98  
% 11.60/1.98  fof(f95,plain,(
% 11.60/1.98    m1_pre_topc(sK7,sK6)),
% 11.60/1.98    inference(cnf_transformation,[],[f57])).
% 11.60/1.98  
% 11.60/1.98  fof(f11,axiom,(
% 11.60/1.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 11.60/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.98  
% 11.60/1.98  fof(f26,plain,(
% 11.60/1.98    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 11.60/1.98    inference(ennf_transformation,[],[f11])).
% 11.60/1.98  
% 11.60/1.98  fof(f84,plain,(
% 11.60/1.98    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 11.60/1.98    inference(cnf_transformation,[],[f26])).
% 11.60/1.98  
% 11.60/1.98  fof(f97,plain,(
% 11.60/1.98    g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) = g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))),
% 11.60/1.98    inference(cnf_transformation,[],[f57])).
% 11.60/1.98  
% 11.60/1.98  fof(f40,plain,(
% 11.60/1.98    ! [X0,X1] : (((m1_pre_topc(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~m1_pre_topc(X1,X0))) | ~sP1(X0,X1))),
% 11.60/1.98    inference(nnf_transformation,[],[f35])).
% 11.60/1.98  
% 11.60/1.98  fof(f67,plain,(
% 11.60/1.98    ( ! [X0,X1] : (sP0(X1,X0) | ~m1_pre_topc(X1,X0) | ~sP1(X0,X1)) )),
% 11.60/1.98    inference(cnf_transformation,[],[f40])).
% 11.60/1.98  
% 11.60/1.98  fof(f41,plain,(
% 11.60/1.98    ! [X1,X0] : ((sP0(X1,X0) | (? [X2] : (((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 11.60/1.98    inference(nnf_transformation,[],[f34])).
% 11.60/1.98  
% 11.60/1.98  fof(f42,plain,(
% 11.60/1.98    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 11.60/1.98    inference(flattening,[],[f41])).
% 11.60/1.98  
% 11.60/1.98  fof(f43,plain,(
% 11.60/1.98    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 11.60/1.98    inference(rectify,[],[f42])).
% 11.60/1.98  
% 11.60/1.98  fof(f46,plain,(
% 11.60/1.98    ! [X5,X1,X0] : (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))))),
% 11.60/1.98    introduced(choice_axiom,[])).
% 11.60/1.98  
% 11.60/1.98  fof(f45,plain,(
% 11.60/1.98    ( ! [X2] : (! [X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = X2 & r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))) )),
% 11.60/1.98    introduced(choice_axiom,[])).
% 11.60/1.98  
% 11.60/1.98  fof(f44,plain,(
% 11.60/1.98    ! [X1,X0] : (? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = sK2(X0,X1) & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 11.60/1.98    introduced(choice_axiom,[])).
% 11.60/1.98  
% 11.60/1.98  fof(f47,plain,(
% 11.60/1.98    ! [X0,X1] : ((sP0(X0,X1) | ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & ((k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = sK2(X0,X1) & r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & ((k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 11.60/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f43,f46,f45,f44])).
% 11.60/1.98  
% 11.60/1.98  fof(f69,plain,(
% 11.60/1.98    ( ! [X0,X1] : (r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) | ~sP0(X0,X1)) )),
% 11.60/1.98    inference(cnf_transformation,[],[f47])).
% 11.60/1.98  
% 11.60/1.98  fof(f1,axiom,(
% 11.60/1.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.60/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.98  
% 11.60/1.98  fof(f37,plain,(
% 11.60/1.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.60/1.98    inference(nnf_transformation,[],[f1])).
% 11.60/1.98  
% 11.60/1.98  fof(f38,plain,(
% 11.60/1.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.60/1.98    inference(flattening,[],[f37])).
% 11.60/1.98  
% 11.60/1.98  fof(f60,plain,(
% 11.60/1.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.60/1.98    inference(cnf_transformation,[],[f38])).
% 11.60/1.98  
% 11.60/1.98  fof(f5,axiom,(
% 11.60/1.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2)) => (k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1))))),
% 11.60/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.98  
% 11.60/1.98  fof(f18,plain,(
% 11.60/1.98    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.60/1.98    inference(ennf_transformation,[],[f5])).
% 11.60/1.98  
% 11.60/1.98  fof(f19,plain,(
% 11.60/1.98    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.60/1.98    inference(flattening,[],[f18])).
% 11.60/1.98  
% 11.60/1.98  fof(f39,plain,(
% 11.60/1.98    ! [X0] : (! [X1] : (! [X2] : (((k1_pre_topc(X0,X1) = X2 | k2_struct_0(X2) != X1) & (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.60/1.98    inference(nnf_transformation,[],[f19])).
% 11.60/1.98  
% 11.60/1.98  fof(f64,plain,(
% 11.60/1.98    ( ! [X2,X0,X1] : (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.60/1.98    inference(cnf_transformation,[],[f39])).
% 11.60/1.98  
% 11.60/1.98  fof(f103,plain,(
% 11.60/1.98    ( ! [X0,X1] : (k2_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.60/1.98    inference(equality_resolution,[],[f64])).
% 11.60/1.98  
% 11.60/1.98  fof(f80,plain,(
% 11.60/1.98    ( ! [X0,X1] : (v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.60/1.98    inference(cnf_transformation,[],[f23])).
% 11.60/1.98  
% 11.60/1.98  fof(f13,axiom,(
% 11.60/1.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 11.60/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.98  
% 11.60/1.98  fof(f28,plain,(
% 11.60/1.98    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 11.60/1.98    inference(ennf_transformation,[],[f13])).
% 11.60/1.98  
% 11.60/1.98  fof(f87,plain,(
% 11.60/1.98    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 11.60/1.98    inference(cnf_transformation,[],[f28])).
% 11.60/1.98  
% 11.60/1.98  fof(f14,axiom,(
% 11.60/1.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 11.60/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.98  
% 11.60/1.98  fof(f29,plain,(
% 11.60/1.98    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 11.60/1.98    inference(ennf_transformation,[],[f14])).
% 11.60/1.98  
% 11.60/1.98  fof(f30,plain,(
% 11.60/1.98    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 11.60/1.98    inference(flattening,[],[f29])).
% 11.60/1.98  
% 11.60/1.98  fof(f49,plain,(
% 11.60/1.98    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 11.60/1.98    inference(nnf_transformation,[],[f30])).
% 11.60/1.98  
% 11.60/1.98  fof(f50,plain,(
% 11.60/1.98    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 11.60/1.98    inference(rectify,[],[f49])).
% 11.60/1.98  
% 11.60/1.98  fof(f51,plain,(
% 11.60/1.98    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK5(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK5(X0,X1) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 11.60/1.98    introduced(choice_axiom,[])).
% 11.60/1.98  
% 11.60/1.98  fof(f52,plain,(
% 11.60/1.98    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK5(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK5(X0,X1) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 11.60/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f50,f51])).
% 11.60/1.98  
% 11.60/1.98  fof(f90,plain,(
% 11.60/1.98    ( ! [X0,X1] : (v1_tex_2(X1,X0) | u1_struct_0(X1) = sK5(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 11.60/1.98    inference(cnf_transformation,[],[f52])).
% 11.60/1.98  
% 11.60/1.98  fof(f99,plain,(
% 11.60/1.98    ~v1_tex_2(sK8,sK6)),
% 11.60/1.98    inference(cnf_transformation,[],[f57])).
% 11.60/1.98  
% 11.60/1.98  fof(f89,plain,(
% 11.60/1.98    ( ! [X0,X1] : (v1_tex_2(X1,X0) | m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 11.60/1.98    inference(cnf_transformation,[],[f52])).
% 11.60/1.98  
% 11.60/1.98  fof(f15,axiom,(
% 11.60/1.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 11.60/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.98  
% 11.60/1.98  fof(f31,plain,(
% 11.60/1.98    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.60/1.98    inference(ennf_transformation,[],[f15])).
% 11.60/1.98  
% 11.60/1.98  fof(f53,plain,(
% 11.60/1.98    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.60/1.98    inference(nnf_transformation,[],[f31])).
% 11.60/1.98  
% 11.60/1.98  fof(f93,plain,(
% 11.60/1.98    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.60/1.98    inference(cnf_transformation,[],[f53])).
% 11.60/1.98  
% 11.60/1.98  fof(f91,plain,(
% 11.60/1.98    ( ! [X0,X1] : (v1_tex_2(X1,X0) | ~v1_subset_1(sK5(X0,X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 11.60/1.98    inference(cnf_transformation,[],[f52])).
% 11.60/1.98  
% 11.60/1.98  fof(f88,plain,(
% 11.60/1.98    ( ! [X0,X3,X1] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 11.60/1.98    inference(cnf_transformation,[],[f52])).
% 11.60/1.98  
% 11.60/1.98  fof(f105,plain,(
% 11.60/1.98    ( ! [X0,X1] : (v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 11.60/1.98    inference(equality_resolution,[],[f88])).
% 11.60/1.98  
% 11.60/1.98  fof(f98,plain,(
% 11.60/1.98    v1_tex_2(sK7,sK6)),
% 11.60/1.98    inference(cnf_transformation,[],[f57])).
% 11.60/1.98  
% 11.60/1.98  fof(f4,axiom,(
% 11.60/1.98    ! [X0] : ~v1_subset_1(k2_subset_1(X0),X0)),
% 11.60/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.98  
% 11.60/1.98  fof(f63,plain,(
% 11.60/1.98    ( ! [X0] : (~v1_subset_1(k2_subset_1(X0),X0)) )),
% 11.60/1.98    inference(cnf_transformation,[],[f4])).
% 11.60/1.98  
% 11.60/1.98  cnf(c_21,plain,
% 11.60/1.98      ( sP1(X0,X1) | ~ l1_pre_topc(X0) | ~ l1_pre_topc(X1) ),
% 11.60/1.98      inference(cnf_transformation,[],[f79]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1220,plain,
% 11.60/1.98      ( sP1(X0,X1) = iProver_top
% 11.60/1.98      | l1_pre_topc(X1) != iProver_top
% 11.60/1.98      | l1_pre_topc(X0) != iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_39,negated_conjecture,
% 11.60/1.98      ( m1_pre_topc(sK8,sK6) ),
% 11.60/1.98      inference(cnf_transformation,[],[f96]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1206,plain,
% 11.60/1.98      ( m1_pre_topc(sK8,sK6) = iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_25,plain,
% 11.60/1.98      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 11.60/1.98      inference(cnf_transformation,[],[f83]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1216,plain,
% 11.60/1.98      ( m1_pre_topc(X0,X1) != iProver_top
% 11.60/1.98      | l1_pre_topc(X1) != iProver_top
% 11.60/1.98      | l1_pre_topc(X0) = iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_2379,plain,
% 11.60/1.98      ( l1_pre_topc(sK6) != iProver_top | l1_pre_topc(sK8) = iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_1206,c_1216]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_41,negated_conjecture,
% 11.60/1.98      ( l1_pre_topc(sK6) ),
% 11.60/1.98      inference(cnf_transformation,[],[f94]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_42,plain,
% 11.60/1.98      ( l1_pre_topc(sK6) = iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1646,plain,
% 11.60/1.98      ( ~ l1_pre_topc(sK6) | l1_pre_topc(sK8) ),
% 11.60/1.98      inference(resolution,[status(thm)],[c_25,c_39]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1647,plain,
% 11.60/1.98      ( l1_pre_topc(sK6) != iProver_top | l1_pre_topc(sK8) = iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_1646]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_2547,plain,
% 11.60/1.98      ( l1_pre_topc(sK8) = iProver_top ),
% 11.60/1.98      inference(global_propositional_subsumption,
% 11.60/1.98                [status(thm)],
% 11.60/1.98                [c_2379,c_42,c_1647]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_24,plain,
% 11.60/1.98      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 11.60/1.98      inference(cnf_transformation,[],[f82]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1217,plain,
% 11.60/1.98      ( l1_struct_0(X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_2553,plain,
% 11.60/1.98      ( l1_struct_0(sK8) = iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_2547,c_1217]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_8,plain,
% 11.60/1.98      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 11.60/1.98      inference(cnf_transformation,[],[f66]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1233,plain,
% 11.60/1.98      ( u1_struct_0(X0) = k2_struct_0(X0) | l1_struct_0(X0) != iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_2631,plain,
% 11.60/1.98      ( u1_struct_0(sK8) = k2_struct_0(sK8) ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_2553,c_1233]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_4,plain,
% 11.60/1.98      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 11.60/1.98      inference(cnf_transformation,[],[f62]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1236,plain,
% 11.60/1.98      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_3,plain,
% 11.60/1.98      ( k2_subset_1(X0) = X0 ),
% 11.60/1.98      inference(cnf_transformation,[],[f61]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1256,plain,
% 11.60/1.98      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 11.60/1.98      inference(light_normalisation,[status(thm)],[c_1236,c_3]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_22,plain,
% 11.60/1.98      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
% 11.60/1.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 11.60/1.98      | ~ l1_pre_topc(X0) ),
% 11.60/1.98      inference(cnf_transformation,[],[f81]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1219,plain,
% 11.60/1.98      ( m1_pre_topc(k1_pre_topc(X0,X1),X0) = iProver_top
% 11.60/1.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.60/1.98      | l1_pre_topc(X0) != iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_4469,plain,
% 11.60/1.98      ( m1_pre_topc(k1_pre_topc(X0,u1_struct_0(X0)),X0) = iProver_top
% 11.60/1.98      | l1_pre_topc(X0) != iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_1256,c_1219]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_9906,plain,
% 11.60/1.98      ( m1_pre_topc(k1_pre_topc(sK8,k2_struct_0(sK8)),sK8) = iProver_top
% 11.60/1.98      | l1_pre_topc(sK8) != iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_2631,c_4469]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_12370,plain,
% 11.60/1.98      ( m1_pre_topc(k1_pre_topc(sK8,k2_struct_0(sK8)),sK8) = iProver_top ),
% 11.60/1.98      inference(global_propositional_subsumption,
% 11.60/1.98                [status(thm)],
% 11.60/1.98                [c_9906,c_42,c_1647]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_28,plain,
% 11.60/1.98      ( ~ m1_pre_topc(X0,X1)
% 11.60/1.98      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 11.60/1.98      | ~ l1_pre_topc(X0)
% 11.60/1.98      | ~ l1_pre_topc(X1) ),
% 11.60/1.98      inference(cnf_transformation,[],[f85]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_322,plain,
% 11.60/1.98      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 11.60/1.98      | ~ m1_pre_topc(X0,X1)
% 11.60/1.98      | ~ l1_pre_topc(X1) ),
% 11.60/1.98      inference(global_propositional_subsumption,[status(thm)],[c_28,c_25]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_323,plain,
% 11.60/1.98      ( ~ m1_pre_topc(X0,X1)
% 11.60/1.98      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 11.60/1.98      | ~ l1_pre_topc(X1) ),
% 11.60/1.98      inference(renaming,[status(thm)],[c_322]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1203,plain,
% 11.60/1.98      ( m1_pre_topc(X0,X1) != iProver_top
% 11.60/1.98      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 11.60/1.98      | l1_pre_topc(X1) != iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_323]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_3159,plain,
% 11.60/1.98      ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK8),u1_pre_topc(sK8))) = iProver_top
% 11.60/1.98      | m1_pre_topc(X0,sK8) != iProver_top
% 11.60/1.98      | l1_pre_topc(sK8) != iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_2631,c_1203]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_14298,plain,
% 11.60/1.98      ( m1_pre_topc(X0,sK8) != iProver_top
% 11.60/1.98      | m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK8),u1_pre_topc(sK8))) = iProver_top ),
% 11.60/1.98      inference(global_propositional_subsumption,
% 11.60/1.98                [status(thm)],
% 11.60/1.98                [c_3159,c_42,c_1647]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_14299,plain,
% 11.60/1.98      ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK8),u1_pre_topc(sK8))) = iProver_top
% 11.60/1.98      | m1_pre_topc(X0,sK8) != iProver_top ),
% 11.60/1.98      inference(renaming,[status(thm)],[c_14298]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_40,negated_conjecture,
% 11.60/1.98      ( m1_pre_topc(sK7,sK6) ),
% 11.60/1.98      inference(cnf_transformation,[],[f95]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1205,plain,
% 11.60/1.98      ( m1_pre_topc(sK7,sK6) = iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_2380,plain,
% 11.60/1.98      ( l1_pre_topc(sK7) = iProver_top | l1_pre_topc(sK6) != iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_1205,c_1216]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1648,plain,
% 11.60/1.98      ( l1_pre_topc(sK7) | ~ l1_pre_topc(sK6) ),
% 11.60/1.98      inference(resolution,[status(thm)],[c_25,c_40]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1649,plain,
% 11.60/1.98      ( l1_pre_topc(sK7) = iProver_top | l1_pre_topc(sK6) != iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_1648]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_2560,plain,
% 11.60/1.98      ( l1_pre_topc(sK7) = iProver_top ),
% 11.60/1.98      inference(global_propositional_subsumption,
% 11.60/1.98                [status(thm)],
% 11.60/1.98                [c_2380,c_42,c_1649]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_2566,plain,
% 11.60/1.98      ( l1_struct_0(sK7) = iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_2560,c_1217]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_2634,plain,
% 11.60/1.98      ( u1_struct_0(sK7) = k2_struct_0(sK7) ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_2566,c_1233]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_26,plain,
% 11.60/1.98      ( m1_pre_topc(X0,X1)
% 11.60/1.98      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 11.60/1.98      | ~ l1_pre_topc(X1) ),
% 11.60/1.98      inference(cnf_transformation,[],[f84]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1215,plain,
% 11.60/1.98      ( m1_pre_topc(X0,X1) = iProver_top
% 11.60/1.98      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 11.60/1.98      | l1_pre_topc(X1) != iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_4432,plain,
% 11.60/1.98      ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
% 11.60/1.98      | m1_pre_topc(X0,sK7) = iProver_top
% 11.60/1.98      | l1_pre_topc(sK7) != iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_2634,c_1215]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_38,negated_conjecture,
% 11.60/1.98      ( g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) = g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) ),
% 11.60/1.98      inference(cnf_transformation,[],[f97]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_2950,plain,
% 11.60/1.98      ( g1_pre_topc(k2_struct_0(sK8),u1_pre_topc(sK8)) = g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) ),
% 11.60/1.98      inference(demodulation,[status(thm)],[c_2631,c_38]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_4025,plain,
% 11.60/1.98      ( g1_pre_topc(k2_struct_0(sK7),u1_pre_topc(sK7)) = g1_pre_topc(k2_struct_0(sK8),u1_pre_topc(sK8)) ),
% 11.60/1.98      inference(demodulation,[status(thm)],[c_2634,c_2950]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_4450,plain,
% 11.60/1.98      ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK8),u1_pre_topc(sK8))) != iProver_top
% 11.60/1.98      | m1_pre_topc(X0,sK7) = iProver_top
% 11.60/1.98      | l1_pre_topc(sK7) != iProver_top ),
% 11.60/1.98      inference(light_normalisation,[status(thm)],[c_4432,c_4025]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_5011,plain,
% 11.60/1.98      ( m1_pre_topc(X0,sK7) = iProver_top
% 11.60/1.98      | m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK8),u1_pre_topc(sK8))) != iProver_top ),
% 11.60/1.98      inference(global_propositional_subsumption,
% 11.60/1.98                [status(thm)],
% 11.60/1.98                [c_4450,c_42,c_1649]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_5012,plain,
% 11.60/1.98      ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK8),u1_pre_topc(sK8))) != iProver_top
% 11.60/1.98      | m1_pre_topc(X0,sK7) = iProver_top ),
% 11.60/1.98      inference(renaming,[status(thm)],[c_5011]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_14309,plain,
% 11.60/1.98      ( m1_pre_topc(X0,sK7) = iProver_top
% 11.60/1.98      | m1_pre_topc(X0,sK8) != iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_14299,c_5012]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_15252,plain,
% 11.60/1.98      ( m1_pre_topc(k1_pre_topc(sK8,k2_struct_0(sK8)),sK7) = iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_12370,c_14309]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_10,plain,
% 11.60/1.98      ( ~ sP1(X0,X1) | sP0(X1,X0) | ~ m1_pre_topc(X1,X0) ),
% 11.60/1.98      inference(cnf_transformation,[],[f67]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1231,plain,
% 11.60/1.98      ( sP1(X0,X1) != iProver_top
% 11.60/1.98      | sP0(X1,X0) = iProver_top
% 11.60/1.98      | m1_pre_topc(X1,X0) != iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_27989,plain,
% 11.60/1.98      ( sP1(sK7,k1_pre_topc(sK8,k2_struct_0(sK8))) != iProver_top
% 11.60/1.98      | sP0(k1_pre_topc(sK8,k2_struct_0(sK8)),sK7) = iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_15252,c_1231]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_29102,plain,
% 11.60/1.98      ( sP0(k1_pre_topc(sK8,k2_struct_0(sK8)),sK7) = iProver_top
% 11.60/1.98      | l1_pre_topc(k1_pre_topc(sK8,k2_struct_0(sK8))) != iProver_top
% 11.60/1.98      | l1_pre_topc(sK7) != iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_1220,c_27989]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_9907,plain,
% 11.60/1.98      ( l1_pre_topc(X0) != iProver_top
% 11.60/1.98      | l1_pre_topc(k1_pre_topc(X0,u1_struct_0(X0))) = iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_4469,c_1216]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_10909,plain,
% 11.60/1.98      ( l1_pre_topc(k1_pre_topc(sK8,k2_struct_0(sK8))) = iProver_top
% 11.60/1.98      | l1_pre_topc(sK8) != iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_2631,c_9907]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_42032,plain,
% 11.60/1.98      ( sP0(k1_pre_topc(sK8,k2_struct_0(sK8)),sK7) = iProver_top ),
% 11.60/1.98      inference(global_propositional_subsumption,
% 11.60/1.98                [status(thm)],
% 11.60/1.98                [c_29102,c_42,c_1647,c_1649,c_10909]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_20,plain,
% 11.60/1.98      ( ~ sP0(X0,X1) | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
% 11.60/1.98      inference(cnf_transformation,[],[f69]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1221,plain,
% 11.60/1.98      ( sP0(X0,X1) != iProver_top
% 11.60/1.98      | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) = iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_0,plain,
% 11.60/1.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 11.60/1.98      inference(cnf_transformation,[],[f60]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1238,plain,
% 11.60/1.98      ( X0 = X1
% 11.60/1.98      | r1_tarski(X0,X1) != iProver_top
% 11.60/1.98      | r1_tarski(X1,X0) != iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_2479,plain,
% 11.60/1.98      ( k2_struct_0(X0) = k2_struct_0(X1)
% 11.60/1.98      | sP0(X1,X0) != iProver_top
% 11.60/1.98      | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) != iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_1221,c_1238]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_21006,plain,
% 11.60/1.98      ( k2_struct_0(X0) = k2_struct_0(X1)
% 11.60/1.98      | sP0(X1,X0) != iProver_top
% 11.60/1.98      | sP0(X0,X1) != iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_1221,c_2479]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_42037,plain,
% 11.60/1.98      ( k2_struct_0(k1_pre_topc(sK8,k2_struct_0(sK8))) = k2_struct_0(sK7)
% 11.60/1.98      | sP0(sK7,k1_pre_topc(sK8,k2_struct_0(sK8))) != iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_42032,c_21006]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_7,plain,
% 11.60/1.98      ( ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
% 11.60/1.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 11.60/1.98      | ~ l1_pre_topc(X0)
% 11.60/1.98      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
% 11.60/1.98      | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ),
% 11.60/1.98      inference(cnf_transformation,[],[f103]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_354,plain,
% 11.60/1.98      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 11.60/1.98      | ~ l1_pre_topc(X0)
% 11.60/1.98      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
% 11.60/1.98      | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ),
% 11.60/1.98      inference(global_propositional_subsumption,[status(thm)],[c_7,c_22]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_355,plain,
% 11.60/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.60/1.98      | ~ l1_pre_topc(X1)
% 11.60/1.98      | ~ v1_pre_topc(k1_pre_topc(X1,X0))
% 11.60/1.98      | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 11.60/1.98      inference(renaming,[status(thm)],[c_354]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_23,plain,
% 11.60/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.60/1.98      | ~ l1_pre_topc(X1)
% 11.60/1.98      | v1_pre_topc(k1_pre_topc(X1,X0)) ),
% 11.60/1.98      inference(cnf_transformation,[],[f80]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_360,plain,
% 11.60/1.98      ( ~ l1_pre_topc(X1)
% 11.60/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.60/1.98      | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 11.60/1.98      inference(global_propositional_subsumption,[status(thm)],[c_355,c_23]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_361,plain,
% 11.60/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.60/1.98      | ~ l1_pre_topc(X1)
% 11.60/1.98      | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 11.60/1.98      inference(renaming,[status(thm)],[c_360]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1201,plain,
% 11.60/1.98      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
% 11.60/1.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.60/1.98      | l1_pre_topc(X0) != iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_361]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1768,plain,
% 11.60/1.98      ( k2_struct_0(k1_pre_topc(X0,u1_struct_0(X0))) = u1_struct_0(X0)
% 11.60/1.98      | l1_pre_topc(X0) != iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_1256,c_1201]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_2552,plain,
% 11.60/1.98      ( k2_struct_0(k1_pre_topc(sK8,u1_struct_0(sK8))) = u1_struct_0(sK8) ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_2547,c_1768]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_2949,plain,
% 11.60/1.98      ( k2_struct_0(k1_pre_topc(sK8,k2_struct_0(sK8))) = k2_struct_0(sK8) ),
% 11.60/1.98      inference(demodulation,[status(thm)],[c_2631,c_2552]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_42044,plain,
% 11.60/1.98      ( k2_struct_0(sK7) = k2_struct_0(sK8)
% 11.60/1.98      | sP0(sK7,k1_pre_topc(sK8,k2_struct_0(sK8))) != iProver_top ),
% 11.60/1.98      inference(light_normalisation,[status(thm)],[c_42037,c_2949]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_43,plain,
% 11.60/1.98      ( m1_pre_topc(sK7,sK6) = iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_29,plain,
% 11.60/1.98      ( ~ m1_pre_topc(X0,X1)
% 11.60/1.98      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.60/1.98      | ~ l1_pre_topc(X1) ),
% 11.60/1.98      inference(cnf_transformation,[],[f87]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1214,plain,
% 11.60/1.98      ( m1_pre_topc(X0,X1) != iProver_top
% 11.60/1.98      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 11.60/1.98      | l1_pre_topc(X1) != iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_4467,plain,
% 11.60/1.98      ( m1_pre_topc(X0,X1) != iProver_top
% 11.60/1.98      | m1_pre_topc(k1_pre_topc(X1,u1_struct_0(X0)),X1) = iProver_top
% 11.60/1.98      | l1_pre_topc(X1) != iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_1214,c_1219]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_24342,plain,
% 11.60/1.98      ( m1_pre_topc(X0,X1) != iProver_top
% 11.60/1.98      | l1_pre_topc(X1) != iProver_top
% 11.60/1.98      | l1_pre_topc(k1_pre_topc(X1,u1_struct_0(X0))) = iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_4467,c_1216]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_24634,plain,
% 11.60/1.98      ( m1_pre_topc(sK7,X0) != iProver_top
% 11.60/1.98      | l1_pre_topc(X0) != iProver_top
% 11.60/1.98      | l1_pre_topc(k1_pre_topc(X0,k2_struct_0(sK7))) = iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_2634,c_24342]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_24698,plain,
% 11.60/1.98      ( m1_pre_topc(sK7,sK6) != iProver_top
% 11.60/1.98      | l1_pre_topc(k1_pre_topc(sK6,k2_struct_0(sK7))) = iProver_top
% 11.60/1.98      | l1_pre_topc(sK6) != iProver_top ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_24634]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1204,plain,
% 11.60/1.98      ( l1_pre_topc(sK6) = iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1775,plain,
% 11.60/1.98      ( l1_struct_0(sK6) = iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_1204,c_1217]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1917,plain,
% 11.60/1.98      ( u1_struct_0(sK6) = k2_struct_0(sK6) ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_1775,c_1233]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_3411,plain,
% 11.60/1.98      ( m1_pre_topc(X0,sK6) != iProver_top
% 11.60/1.98      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK6))) = iProver_top
% 11.60/1.98      | l1_pre_topc(sK6) != iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_1917,c_1214]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_6115,plain,
% 11.60/1.98      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK6))) = iProver_top
% 11.60/1.98      | m1_pre_topc(X0,sK6) != iProver_top ),
% 11.60/1.98      inference(global_propositional_subsumption,[status(thm)],[c_3411,c_42]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_6116,plain,
% 11.60/1.98      ( m1_pre_topc(X0,sK6) != iProver_top
% 11.60/1.98      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK6))) = iProver_top ),
% 11.60/1.98      inference(renaming,[status(thm)],[c_6115]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_4472,plain,
% 11.60/1.98      ( m1_pre_topc(k1_pre_topc(sK6,X0),sK6) = iProver_top
% 11.60/1.98      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6))) != iProver_top
% 11.60/1.98      | l1_pre_topc(sK6) != iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_1917,c_1219]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_6456,plain,
% 11.60/1.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6))) != iProver_top
% 11.60/1.98      | m1_pre_topc(k1_pre_topc(sK6,X0),sK6) = iProver_top ),
% 11.60/1.98      inference(global_propositional_subsumption,[status(thm)],[c_4472,c_42]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_6457,plain,
% 11.60/1.98      ( m1_pre_topc(k1_pre_topc(sK6,X0),sK6) = iProver_top
% 11.60/1.98      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6))) != iProver_top ),
% 11.60/1.98      inference(renaming,[status(thm)],[c_6456]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_6465,plain,
% 11.60/1.98      ( m1_pre_topc(X0,sK6) != iProver_top
% 11.60/1.98      | m1_pre_topc(k1_pre_topc(sK6,u1_struct_0(X0)),sK6) = iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_6116,c_6457]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_29382,plain,
% 11.60/1.98      ( m1_pre_topc(k1_pre_topc(sK6,k2_struct_0(sK7)),sK6) = iProver_top
% 11.60/1.98      | m1_pre_topc(sK7,sK6) != iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_2634,c_6465]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_4031,plain,
% 11.60/1.98      ( m1_pre_topc(sK7,X0) != iProver_top
% 11.60/1.98      | m1_subset_1(k2_struct_0(sK7),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 11.60/1.98      | l1_pre_topc(X0) != iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_2634,c_1214]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_22974,plain,
% 11.60/1.98      ( m1_pre_topc(k1_pre_topc(X0,k2_struct_0(sK7)),X0) = iProver_top
% 11.60/1.98      | m1_pre_topc(sK7,X0) != iProver_top
% 11.60/1.98      | l1_pre_topc(X0) != iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_4031,c_1219]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_23026,plain,
% 11.60/1.98      ( m1_pre_topc(k1_pre_topc(sK6,k2_struct_0(sK7)),sK6) = iProver_top
% 11.60/1.98      | m1_pre_topc(sK7,sK6) != iProver_top
% 11.60/1.98      | l1_pre_topc(sK6) != iProver_top ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_22974]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_29956,plain,
% 11.60/1.98      ( m1_pre_topc(k1_pre_topc(sK6,k2_struct_0(sK7)),sK6) = iProver_top ),
% 11.60/1.98      inference(global_propositional_subsumption,
% 11.60/1.98                [status(thm)],
% 11.60/1.98                [c_29382,c_42,c_43,c_23026]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_29964,plain,
% 11.60/1.98      ( sP1(sK6,k1_pre_topc(sK6,k2_struct_0(sK7))) != iProver_top
% 11.60/1.98      | sP0(k1_pre_topc(sK6,k2_struct_0(sK7)),sK6) = iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_29956,c_1231]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_30613,plain,
% 11.60/1.98      ( sP0(k1_pre_topc(sK6,k2_struct_0(sK7)),sK6) = iProver_top
% 11.60/1.98      | l1_pre_topc(k1_pre_topc(sK6,k2_struct_0(sK7))) != iProver_top
% 11.60/1.98      | l1_pre_topc(sK6) != iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_1220,c_29964]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_2002,plain,
% 11.60/1.98      ( k2_struct_0(k1_pre_topc(sK6,X0)) = X0
% 11.60/1.98      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6))) != iProver_top
% 11.60/1.98      | l1_pre_topc(sK6) != iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_1917,c_1201]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_2007,plain,
% 11.60/1.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6))) != iProver_top
% 11.60/1.98      | k2_struct_0(k1_pre_topc(sK6,X0)) = X0 ),
% 11.60/1.98      inference(global_propositional_subsumption,[status(thm)],[c_2002,c_42]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_2008,plain,
% 11.60/1.98      ( k2_struct_0(k1_pre_topc(sK6,X0)) = X0
% 11.60/1.98      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6))) != iProver_top ),
% 11.60/1.98      inference(renaming,[status(thm)],[c_2007]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_6127,plain,
% 11.60/1.98      ( k2_struct_0(k1_pre_topc(sK6,u1_struct_0(X0))) = u1_struct_0(X0)
% 11.60/1.98      | m1_pre_topc(X0,sK6) != iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_6116,c_2008]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_13863,plain,
% 11.60/1.98      ( k2_struct_0(k1_pre_topc(sK6,u1_struct_0(sK7))) = u1_struct_0(sK7) ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_1205,c_6127]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_13872,plain,
% 11.60/1.98      ( k2_struct_0(k1_pre_topc(sK6,k2_struct_0(sK7))) = k2_struct_0(sK7) ),
% 11.60/1.98      inference(light_normalisation,[status(thm)],[c_13863,c_2634]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_31,plain,
% 11.60/1.98      ( v1_tex_2(X0,X1)
% 11.60/1.98      | ~ m1_pre_topc(X0,X1)
% 11.60/1.98      | ~ l1_pre_topc(X1)
% 11.60/1.98      | sK5(X1,X0) = u1_struct_0(X0) ),
% 11.60/1.98      inference(cnf_transformation,[],[f90]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1212,plain,
% 11.60/1.98      ( sK5(X0,X1) = u1_struct_0(X1)
% 11.60/1.98      | v1_tex_2(X1,X0) = iProver_top
% 11.60/1.98      | m1_pre_topc(X1,X0) != iProver_top
% 11.60/1.98      | l1_pre_topc(X0) != iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_4832,plain,
% 11.60/1.98      ( sK5(sK6,sK8) = u1_struct_0(sK8)
% 11.60/1.98      | v1_tex_2(sK8,sK6) = iProver_top
% 11.60/1.98      | l1_pre_topc(sK6) != iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_1206,c_1212]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_4846,plain,
% 11.60/1.98      ( sK5(sK6,sK8) = k2_struct_0(sK8)
% 11.60/1.98      | v1_tex_2(sK8,sK6) = iProver_top
% 11.60/1.98      | l1_pre_topc(sK6) != iProver_top ),
% 11.60/1.98      inference(light_normalisation,[status(thm)],[c_4832,c_2631]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_36,negated_conjecture,
% 11.60/1.98      ( ~ v1_tex_2(sK8,sK6) ),
% 11.60/1.98      inference(cnf_transformation,[],[f99]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_46,plain,
% 11.60/1.98      ( v1_tex_2(sK8,sK6) != iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_5022,plain,
% 11.60/1.98      ( sK5(sK6,sK8) = k2_struct_0(sK8) ),
% 11.60/1.98      inference(global_propositional_subsumption,
% 11.60/1.98                [status(thm)],
% 11.60/1.98                [c_4846,c_42,c_46]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_32,plain,
% 11.60/1.98      ( v1_tex_2(X0,X1)
% 11.60/1.98      | ~ m1_pre_topc(X0,X1)
% 11.60/1.98      | m1_subset_1(sK5(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.60/1.98      | ~ l1_pre_topc(X1) ),
% 11.60/1.98      inference(cnf_transformation,[],[f89]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1211,plain,
% 11.60/1.98      ( v1_tex_2(X0,X1) = iProver_top
% 11.60/1.98      | m1_pre_topc(X0,X1) != iProver_top
% 11.60/1.98      | m1_subset_1(sK5(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 11.60/1.98      | l1_pre_topc(X1) != iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_5025,plain,
% 11.60/1.98      ( v1_tex_2(sK8,sK6) = iProver_top
% 11.60/1.98      | m1_pre_topc(sK8,sK6) != iProver_top
% 11.60/1.98      | m1_subset_1(k2_struct_0(sK8),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
% 11.60/1.98      | l1_pre_topc(sK6) != iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_5022,c_1211]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_5026,plain,
% 11.60/1.98      ( v1_tex_2(sK8,sK6) = iProver_top
% 11.60/1.98      | m1_pre_topc(sK8,sK6) != iProver_top
% 11.60/1.98      | m1_subset_1(k2_struct_0(sK8),k1_zfmisc_1(k2_struct_0(sK6))) = iProver_top
% 11.60/1.98      | l1_pre_topc(sK6) != iProver_top ),
% 11.60/1.98      inference(light_normalisation,[status(thm)],[c_5025,c_1917]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_44,plain,
% 11.60/1.98      ( m1_pre_topc(sK8,sK6) = iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_8731,plain,
% 11.60/1.98      ( m1_subset_1(k2_struct_0(sK8),k1_zfmisc_1(k2_struct_0(sK6))) = iProver_top ),
% 11.60/1.98      inference(global_propositional_subsumption,
% 11.60/1.98                [status(thm)],
% 11.60/1.98                [c_5026,c_42,c_44,c_46]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_34,plain,
% 11.60/1.98      ( v1_subset_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | X0 = X1 ),
% 11.60/1.98      inference(cnf_transformation,[],[f93]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1210,plain,
% 11.60/1.98      ( X0 = X1
% 11.60/1.98      | v1_subset_1(X0,X1) = iProver_top
% 11.60/1.98      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_8736,plain,
% 11.60/1.98      ( k2_struct_0(sK8) = k2_struct_0(sK6)
% 11.60/1.98      | v1_subset_1(k2_struct_0(sK8),k2_struct_0(sK6)) = iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_8731,c_1210]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_30,plain,
% 11.60/1.98      ( v1_tex_2(X0,X1)
% 11.60/1.98      | ~ m1_pre_topc(X0,X1)
% 11.60/1.98      | ~ v1_subset_1(sK5(X1,X0),u1_struct_0(X1))
% 11.60/1.98      | ~ l1_pre_topc(X1) ),
% 11.60/1.98      inference(cnf_transformation,[],[f91]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1213,plain,
% 11.60/1.98      ( v1_tex_2(X0,X1) = iProver_top
% 11.60/1.98      | m1_pre_topc(X0,X1) != iProver_top
% 11.60/1.98      | v1_subset_1(sK5(X1,X0),u1_struct_0(X1)) != iProver_top
% 11.60/1.98      | l1_pre_topc(X1) != iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_5345,plain,
% 11.60/1.98      ( v1_tex_2(sK8,sK6) = iProver_top
% 11.60/1.98      | m1_pre_topc(sK8,sK6) != iProver_top
% 11.60/1.98      | v1_subset_1(k2_struct_0(sK8),u1_struct_0(sK6)) != iProver_top
% 11.60/1.98      | l1_pre_topc(sK6) != iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_5022,c_1213]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_5377,plain,
% 11.60/1.98      ( v1_tex_2(sK8,sK6) = iProver_top
% 11.60/1.98      | m1_pre_topc(sK8,sK6) != iProver_top
% 11.60/1.98      | v1_subset_1(k2_struct_0(sK8),k2_struct_0(sK6)) != iProver_top
% 11.60/1.98      | l1_pre_topc(sK6) != iProver_top ),
% 11.60/1.98      inference(light_normalisation,[status(thm)],[c_5345,c_1917]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_9422,plain,
% 11.60/1.98      ( k2_struct_0(sK8) = k2_struct_0(sK6) ),
% 11.60/1.98      inference(global_propositional_subsumption,
% 11.60/1.98                [status(thm)],
% 11.60/1.98                [c_8736,c_42,c_44,c_46,c_5377]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_9645,plain,
% 11.60/1.98      ( sP0(X0,sK6) != iProver_top
% 11.60/1.98      | r1_tarski(k2_struct_0(X0),k2_struct_0(sK8)) = iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_9422,c_1221]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_11980,plain,
% 11.60/1.98      ( k2_struct_0(X0) = k2_struct_0(sK8)
% 11.60/1.98      | sP0(X0,sK6) != iProver_top
% 11.60/1.98      | r1_tarski(k2_struct_0(sK8),k2_struct_0(X0)) != iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_9645,c_1238]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_32157,plain,
% 11.60/1.98      ( k2_struct_0(k1_pre_topc(sK6,k2_struct_0(sK7))) = k2_struct_0(sK8)
% 11.60/1.98      | sP0(k1_pre_topc(sK6,k2_struct_0(sK7)),sK6) != iProver_top
% 11.60/1.98      | r1_tarski(k2_struct_0(sK8),k2_struct_0(sK7)) != iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_13872,c_11980]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_32171,plain,
% 11.60/1.98      ( k2_struct_0(sK7) = k2_struct_0(sK8)
% 11.60/1.98      | sP0(k1_pre_topc(sK6,k2_struct_0(sK7)),sK6) != iProver_top
% 11.60/1.98      | r1_tarski(k2_struct_0(sK8),k2_struct_0(sK7)) != iProver_top ),
% 11.60/1.98      inference(demodulation,[status(thm)],[c_32157,c_13872]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_4215,plain,
% 11.60/1.98      ( sP0(k1_pre_topc(sK8,k2_struct_0(sK8)),X0) != iProver_top
% 11.60/1.98      | r1_tarski(k2_struct_0(sK8),k2_struct_0(X0)) = iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_2949,c_1221]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_42039,plain,
% 11.60/1.98      ( r1_tarski(k2_struct_0(sK8),k2_struct_0(sK7)) = iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_42032,c_4215]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_43516,plain,
% 11.60/1.98      ( k2_struct_0(sK7) = k2_struct_0(sK8) ),
% 11.60/1.98      inference(global_propositional_subsumption,
% 11.60/1.98                [status(thm)],
% 11.60/1.98                [c_42044,c_42,c_43,c_24698,c_30613,c_32171,c_42039]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_10912,plain,
% 11.60/1.98      ( l1_struct_0(k1_pre_topc(X0,u1_struct_0(X0))) = iProver_top
% 11.60/1.98      | l1_pre_topc(X0) != iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_9907,c_1217]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_11799,plain,
% 11.60/1.98      ( u1_struct_0(k1_pre_topc(X0,u1_struct_0(X0))) = k2_struct_0(k1_pre_topc(X0,u1_struct_0(X0)))
% 11.60/1.98      | l1_pre_topc(X0) != iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_10912,c_1233]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_14805,plain,
% 11.60/1.98      ( u1_struct_0(k1_pre_topc(sK6,u1_struct_0(sK6))) = k2_struct_0(k1_pre_topc(sK6,u1_struct_0(sK6))) ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_1204,c_11799]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_8739,plain,
% 11.60/1.98      ( k2_struct_0(k1_pre_topc(sK6,k2_struct_0(sK8))) = k2_struct_0(sK8) ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_8731,c_2008]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_9452,plain,
% 11.60/1.98      ( u1_struct_0(sK6) = k2_struct_0(sK8) ),
% 11.60/1.98      inference(demodulation,[status(thm)],[c_9422,c_1917]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_14826,plain,
% 11.60/1.98      ( u1_struct_0(k1_pre_topc(sK6,k2_struct_0(sK8))) = k2_struct_0(sK8) ),
% 11.60/1.98      inference(light_normalisation,[status(thm)],[c_14805,c_8739,c_9452]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_33,plain,
% 11.60/1.98      ( ~ v1_tex_2(X0,X1)
% 11.60/1.98      | ~ m1_pre_topc(X0,X1)
% 11.60/1.98      | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 11.60/1.98      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.60/1.98      | ~ l1_pre_topc(X1) ),
% 11.60/1.98      inference(cnf_transformation,[],[f105]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_343,plain,
% 11.60/1.98      ( v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 11.60/1.98      | ~ m1_pre_topc(X0,X1)
% 11.60/1.98      | ~ v1_tex_2(X0,X1)
% 11.60/1.98      | ~ l1_pre_topc(X1) ),
% 11.60/1.98      inference(global_propositional_subsumption,[status(thm)],[c_33,c_29]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_344,plain,
% 11.60/1.98      ( ~ v1_tex_2(X0,X1)
% 11.60/1.98      | ~ m1_pre_topc(X0,X1)
% 11.60/1.98      | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 11.60/1.98      | ~ l1_pre_topc(X1) ),
% 11.60/1.98      inference(renaming,[status(thm)],[c_343]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1202,plain,
% 11.60/1.98      ( v1_tex_2(X0,X1) != iProver_top
% 11.60/1.98      | m1_pre_topc(X0,X1) != iProver_top
% 11.60/1.98      | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 11.60/1.98      | l1_pre_topc(X1) != iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_344]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_4032,plain,
% 11.60/1.98      ( v1_tex_2(sK7,X0) != iProver_top
% 11.60/1.98      | m1_pre_topc(sK7,X0) != iProver_top
% 11.60/1.98      | v1_subset_1(k2_struct_0(sK7),u1_struct_0(X0)) = iProver_top
% 11.60/1.98      | l1_pre_topc(X0) != iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_2634,c_1202]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_24157,plain,
% 11.60/1.98      ( v1_tex_2(sK7,k1_pre_topc(sK6,k2_struct_0(sK8))) != iProver_top
% 11.60/1.98      | m1_pre_topc(sK7,k1_pre_topc(sK6,k2_struct_0(sK8))) != iProver_top
% 11.60/1.98      | v1_subset_1(k2_struct_0(sK7),k2_struct_0(sK8)) = iProver_top
% 11.60/1.98      | l1_pre_topc(k1_pre_topc(sK6,k2_struct_0(sK8))) != iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_14826,c_4032]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_37,negated_conjecture,
% 11.60/1.98      ( v1_tex_2(sK7,sK6) ),
% 11.60/1.98      inference(cnf_transformation,[],[f98]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_45,plain,
% 11.60/1.98      ( v1_tex_2(sK7,sK6) = iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_24154,plain,
% 11.60/1.98      ( v1_tex_2(sK7,sK6) != iProver_top
% 11.60/1.98      | m1_pre_topc(sK7,sK6) != iProver_top
% 11.60/1.98      | v1_subset_1(k2_struct_0(sK7),k2_struct_0(sK8)) = iProver_top
% 11.60/1.98      | l1_pre_topc(sK6) != iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_9452,c_4032]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_25488,plain,
% 11.60/1.98      ( v1_subset_1(k2_struct_0(sK7),k2_struct_0(sK8)) = iProver_top ),
% 11.60/1.98      inference(global_propositional_subsumption,
% 11.60/1.98                [status(thm)],
% 11.60/1.98                [c_24157,c_42,c_43,c_45,c_24154]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_43555,plain,
% 11.60/1.98      ( v1_subset_1(k2_struct_0(sK8),k2_struct_0(sK8)) = iProver_top ),
% 11.60/1.98      inference(demodulation,[status(thm)],[c_43516,c_25488]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_5,plain,
% 11.60/1.98      ( ~ v1_subset_1(k2_subset_1(X0),X0) ),
% 11.60/1.98      inference(cnf_transformation,[],[f63]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1235,plain,
% 11.60/1.98      ( v1_subset_1(k2_subset_1(X0),X0) != iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1253,plain,
% 11.60/1.98      ( v1_subset_1(X0,X0) != iProver_top ),
% 11.60/1.98      inference(light_normalisation,[status(thm)],[c_1235,c_3]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_44850,plain,
% 11.60/1.98      ( $false ),
% 11.60/1.98      inference(forward_subsumption_resolution,[status(thm)],[c_43555,c_1253]) ).
% 11.60/1.98  
% 11.60/1.98  
% 11.60/1.98  % SZS output end CNFRefutation for theBenchmark.p
% 11.60/1.98  
% 11.60/1.98  ------                               Statistics
% 11.60/1.98  
% 11.60/1.98  ------ Selected
% 11.60/1.98  
% 11.60/1.98  total_time:                             1.456
% 11.60/1.98  
%------------------------------------------------------------------------------
