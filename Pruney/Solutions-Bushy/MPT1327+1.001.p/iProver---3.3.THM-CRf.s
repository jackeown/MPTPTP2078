%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1327+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:29 EST 2020

% Result     : Theorem 4.05s
% Output     : CNFRefutation 4.05s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_3336)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
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

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X3,X2,X0,X1] :
      ( ( k1_tops_2(X0,X1,X2) = X3
      <=> sP0(X1,X0,X2,X3) )
      | ~ sP1(X3,X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f34,plain,(
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

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( sP1(X3,X2,X0,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f20,f35,f34])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X3,X2,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f42,plain,(
    ! [X3,X2,X0,X1] :
      ( ( ( k1_tops_2(X0,X1,X2) = X3
          | ~ sP0(X1,X0,X2,X3) )
        & ( sP0(X1,X0,X2,X3)
          | k1_tops_2(X0,X1,X2) != X3 ) )
      | ~ sP1(X3,X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_tops_2(X2,X3,X1) = X0
          | ~ sP0(X3,X2,X1,X0) )
        & ( sP0(X3,X2,X1,X0)
          | k1_tops_2(X2,X3,X1) != X0 ) )
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f42])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X3,X2,X1,X0)
      | k1_tops_2(X2,X3,X1) != X0
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f97,plain,(
    ! [X2,X3,X1] :
      ( sP0(X3,X2,X1,k1_tops_2(X2,X3,X1))
      | ~ sP1(k1_tops_2(X2,X3,X1),X1,X2,X3) ) ),
    inference(equality_resolution,[],[f66])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v4_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v4_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v4_pre_topc(X2,X0)
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v4_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v4_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v4_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK2(X0,X1),X0)
        & r2_hidden(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ( ~ v4_pre_topc(sK2(X0,X1),X0)
                & r2_hidden(sK2(X0,X1),X1)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v4_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v2_tops_2(X1,X0)
      | r2_hidden(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f13,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( v2_tops_2(X2,X0)
               => v2_tops_2(k1_tops_2(X0,X1,X2),k1_pre_topc(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( v2_tops_2(X2,X0)
                 => v2_tops_2(k1_tops_2(X0,X1,X2),k1_pre_topc(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k1_tops_2(X0,X1,X2),k1_pre_topc(X0,X1))
              & v2_tops_2(X2,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k1_tops_2(X0,X1,X2),k1_pre_topc(X0,X1))
              & v2_tops_2(X2,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v2_tops_2(k1_tops_2(X0,X1,X2),k1_pre_topc(X0,X1))
          & v2_tops_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ v2_tops_2(k1_tops_2(X0,X1,sK9),k1_pre_topc(X0,X1))
        & v2_tops_2(sK9,X0)
        & m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k1_tops_2(X0,X1,X2),k1_pre_topc(X0,X1))
              & v2_tops_2(X2,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ v2_tops_2(k1_tops_2(X0,sK8,X2),k1_pre_topc(X0,sK8))
            & v2_tops_2(X2,X0)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_tops_2(k1_tops_2(X0,X1,X2),k1_pre_topc(X0,X1))
                & v2_tops_2(X2,X0)
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k1_tops_2(sK7,X1,X2),k1_pre_topc(sK7,X1))
              & v2_tops_2(X2,sK7)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) )
      & l1_pre_topc(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( ~ v2_tops_2(k1_tops_2(sK7,sK8,sK9),k1_pre_topc(sK7,sK8))
    & v2_tops_2(sK9,sK7)
    & m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
    & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7)))
    & l1_pre_topc(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f33,f57,f56,f55])).

fof(f94,plain,(
    ~ v2_tops_2(k1_tops_2(sK7,sK8,sK9),k1_pre_topc(sK7,sK8)) ),
    inference(cnf_transformation,[],[f58])).

fof(f90,plain,(
    l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f58])).

fof(f91,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(cnf_transformation,[],[f58])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f83,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v2_tops_2(X1,X0)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f46,plain,(
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
    inference(rectify,[],[f45])).

fof(f49,plain,(
    ! [X7,X2,X1,X0] :
      ( ? [X9] :
          ( k9_subset_1(u1_struct_0(X1),X9,X0) = X7
          & r2_hidden(X9,X2)
          & m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X1),sK5(X0,X1,X2,X7),X0) = X7
        & r2_hidden(sK5(X0,X1,X2,X7),X2)
        & m1_subset_1(sK5(X0,X1,X2,X7),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( k9_subset_1(u1_struct_0(X1),X6,X0) = X4
          & r2_hidden(X6,X2)
          & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2,X3),X0) = X4
        & r2_hidden(sK4(X0,X1,X2,X3),X2)
        & m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
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
              ( k9_subset_1(u1_struct_0(X1),X5,X0) != sK3(X0,X1,X2,X3)
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
        & ( ? [X6] :
              ( k9_subset_1(u1_struct_0(X1),X6,X0) = sK3(X0,X1,X2,X3)
              & r2_hidden(X6,X2)
              & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) )
          | r2_hidden(sK3(X0,X1,X2,X3),X3) )
        & m1_subset_1(sK3(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ! [X5] :
                ( k9_subset_1(u1_struct_0(X1),X5,X0) != sK3(X0,X1,X2,X3)
                | ~ r2_hidden(X5,X2)
                | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
          & ( ( k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2,X3),X0) = sK3(X0,X1,X2,X3)
              & r2_hidden(sK4(X0,X1,X2,X3),X2)
              & m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1))) )
            | r2_hidden(sK3(X0,X1,X2,X3),X3) )
          & m1_subset_1(sK3(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0)))) ) )
      & ( ! [X7] :
            ( ( ( r2_hidden(X7,X3)
                | ! [X8] :
                    ( k9_subset_1(u1_struct_0(X1),X8,X0) != X7
                    | ~ r2_hidden(X8,X2)
                    | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X1))) ) )
              & ( ( k9_subset_1(u1_struct_0(X1),sK5(X0,X1,X2,X7),X0) = X7
                  & r2_hidden(sK5(X0,X1,X2,X7),X2)
                  & m1_subset_1(sK5(X0,X1,X2,X7),k1_zfmisc_1(u1_struct_0(X1))) )
                | ~ r2_hidden(X7,X3) ) )
            | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0)))) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f46,f49,f48,f47])).

fof(f70,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( k9_subset_1(u1_struct_0(X1),sK5(X0,X1,X2,X7),X0) = X7
      | ~ r2_hidden(X7,X3)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0))))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f92,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) ),
    inference(cnf_transformation,[],[f58])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2) )
             => ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X2) = X1
      | k1_pre_topc(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f96,plain,(
    ! [X0,X1] :
      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( v4_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v4_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v4_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                      & v4_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v4_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v4_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X4] :
                      ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                      & v4_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v4_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f51])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
          & v4_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X1),sK6(X0,X1,X2),k2_struct_0(X1)) = X2
        & v4_pre_topc(sK6(X0,X1,X2),X0)
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v4_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ( k9_subset_1(u1_struct_0(X1),sK6(X0,X1,X2),k2_struct_0(X1)) = X2
                    & v4_pre_topc(sK6(X0,X1,X2),X0)
                    & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v4_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f52,f53])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( v4_pre_topc(X2,X1)
      | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f99,plain,(
    ! [X0,X3,X1] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1)
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f88])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f82,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f81,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f69,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( r2_hidden(sK5(X0,X1,X2,X7),X2)
      | ~ r2_hidden(X7,X3)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0))))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( v4_pre_topc(X3,X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f93,plain,(
    v2_tops_2(sK9,sK7) ),
    inference(cnf_transformation,[],[f58])).

fof(f68,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( m1_subset_1(sK5(X0,X1,X2,X7),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(X7,X3)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0))))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v2_tops_2(X1,X0)
      | ~ v4_pre_topc(sK2(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_18,plain,
    ( sP1(X0,X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X3)))))
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_8,plain,
    ( ~ sP1(k1_tops_2(X0,X1,X2),X2,X0,X1)
    | sP0(X1,X0,X2,k1_tops_2(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_487,plain,
    ( sP0(X0,X1,X2,k1_tops_2(X1,X0,X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X4))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X4,X3)))))
    | ~ l1_pre_topc(X4)
    | X0 != X3
    | X1 != X4
    | X2 != X5
    | k1_tops_2(X1,X0,X2) != X6 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_8])).

cnf(c_488,plain,
    ( sP0(X0,X1,X2,k1_tops_2(X1,X0,X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(k1_tops_2(X1,X0,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0)))))
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_487])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | m1_subset_1(k1_tops_2(X1,X0,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0)))))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_492,plain,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sP0(X0,X1,X2,k1_tops_2(X1,X0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_488,c_21])).

cnf(c_493,plain,
    ( sP0(X0,X1,X2,k1_tops_2(X1,X0,X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_492])).

cnf(c_2316,plain,
    ( sP0(X0,X1,X2,k1_tops_2(X1,X0,X2)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_493])).

cnf(c_4,plain,
    ( r2_hidden(sK2(X0,X1),X1)
    | v2_tops_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_31,negated_conjecture,
    ( ~ v2_tops_2(k1_tops_2(sK7,sK8,sK9),k1_pre_topc(sK7,sK8)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_729,plain,
    ( r2_hidden(sK2(X0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0)
    | k1_tops_2(sK7,sK8,sK9) != X1
    | k1_pre_topc(sK7,sK8) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_31])).

cnf(c_730,plain,
    ( r2_hidden(sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9)),k1_tops_2(sK7,sK8,sK9))
    | ~ m1_subset_1(k1_tops_2(sK7,sK8,sK9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK7,sK8)))))
    | ~ l1_pre_topc(k1_pre_topc(sK7,sK8)) ),
    inference(unflattening,[status(thm)],[c_729])).

cnf(c_2313,plain,
    ( r2_hidden(sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9)),k1_tops_2(sK7,sK8,sK9)) = iProver_top
    | m1_subset_1(k1_tops_2(sK7,sK8,sK9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK7,sK8))))) != iProver_top
    | l1_pre_topc(k1_pre_topc(sK7,sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_730])).

cnf(c_35,negated_conjecture,
    ( l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_36,plain,
    ( l1_pre_topc(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_37,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_731,plain,
    ( r2_hidden(sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9)),k1_tops_2(sK7,sK8,sK9)) = iProver_top
    | m1_subset_1(k1_tops_2(sK7,sK8,sK9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK7,sK8))))) != iProver_top
    | l1_pre_topc(k1_pre_topc(sK7,sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_730])).

cnf(c_24,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2673,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK7,sK8),X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(k1_pre_topc(sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_2674,plain,
    ( m1_pre_topc(k1_pre_topc(sK7,sK8),X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(k1_pre_topc(sK7,sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2673])).

cnf(c_2676,plain,
    ( m1_pre_topc(k1_pre_topc(sK7,sK8),sK7) != iProver_top
    | l1_pre_topc(k1_pre_topc(sK7,sK8)) = iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2674])).

cnf(c_19,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2700,plain,
    ( m1_pre_topc(k1_pre_topc(sK7,sK8),sK7)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ l1_pre_topc(sK7) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2701,plain,
    ( m1_pre_topc(k1_pre_topc(sK7,sK8),sK7) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2700])).

cnf(c_2792,plain,
    ( m1_subset_1(k1_tops_2(sK7,sK8,sK9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK7,sK8))))) != iProver_top
    | r2_hidden(sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9)),k1_tops_2(sK7,sK8,sK9)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2313,c_36,c_37,c_731,c_2676,c_2701])).

cnf(c_2793,plain,
    ( r2_hidden(sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9)),k1_tops_2(sK7,sK8,sK9)) = iProver_top
    | m1_subset_1(k1_tops_2(sK7,sK8,sK9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK7,sK8))))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2792])).

cnf(c_5,plain,
    ( v2_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_781,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_2(sK7,sK8,sK9) != X0
    | k1_pre_topc(sK7,sK8) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_31])).

cnf(c_782,plain,
    ( ~ m1_subset_1(k1_tops_2(sK7,sK8,sK9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK7,sK8)))))
    | m1_subset_1(sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9)),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK7,sK8))))
    | ~ l1_pre_topc(k1_pre_topc(sK7,sK8)) ),
    inference(unflattening,[status(thm)],[c_781])).

cnf(c_2310,plain,
    ( m1_subset_1(k1_tops_2(sK7,sK8,sK9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK7,sK8))))) != iProver_top
    | m1_subset_1(sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9)),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK7,sK8)))) = iProver_top
    | l1_pre_topc(k1_pre_topc(sK7,sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_782])).

cnf(c_783,plain,
    ( m1_subset_1(k1_tops_2(sK7,sK8,sK9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK7,sK8))))) != iProver_top
    | m1_subset_1(sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9)),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK7,sK8)))) = iProver_top
    | l1_pre_topc(k1_pre_topc(sK7,sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_782])).

cnf(c_2800,plain,
    ( m1_subset_1(sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9)),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK7,sK8)))) = iProver_top
    | m1_subset_1(k1_tops_2(sK7,sK8,sK9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK7,sK8))))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2310,c_36,c_37,c_783,c_2676,c_2701])).

cnf(c_2801,plain,
    ( m1_subset_1(k1_tops_2(sK7,sK8,sK9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK7,sK8))))) != iProver_top
    | m1_subset_1(sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9)),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK7,sK8)))) = iProver_top ),
    inference(renaming,[status(thm)],[c_2800])).

cnf(c_15,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0))))
    | k9_subset_1(u1_struct_0(X1),sK5(X0,X1,X2,X4),X0) = X4 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2335,plain,
    ( k9_subset_1(u1_struct_0(X0),sK5(X1,X0,X2,X3),X1) = X3
    | sP0(X1,X0,X2,X4) != iProver_top
    | r2_hidden(X3,X4) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5149,plain,
    ( k9_subset_1(u1_struct_0(sK7),sK5(sK8,sK7,X0,sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9))),sK8) = sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9))
    | sP0(sK8,sK7,X0,X1) != iProver_top
    | r2_hidden(sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9)),X1) != iProver_top
    | m1_subset_1(k1_tops_2(sK7,sK8,sK9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK7,sK8))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2801,c_2335])).

cnf(c_2321,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2328,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2810,plain,
    ( k9_subset_1(u1_struct_0(sK7),X0,sK8) = k3_xboole_0(X0,sK8) ),
    inference(superposition,[status(thm)],[c_2321,c_2328])).

cnf(c_5154,plain,
    ( k3_xboole_0(sK5(sK8,sK7,X0,sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9))),sK8) = sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9))
    | sP0(sK8,sK7,X0,X1) != iProver_top
    | r2_hidden(sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9)),X1) != iProver_top
    | m1_subset_1(k1_tops_2(sK7,sK8,sK9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK7,sK8))))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5149,c_2810])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_38,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_2750,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
    | m1_subset_1(k1_tops_2(sK7,sK8,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK7,sK8)))))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ l1_pre_topc(sK7) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_2899,plain,
    ( m1_subset_1(k1_tops_2(sK7,sK8,sK9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK7,sK8)))))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ l1_pre_topc(sK7) ),
    inference(instantiation,[status(thm)],[c_2750])).

cnf(c_2900,plain,
    ( m1_subset_1(k1_tops_2(sK7,sK8,sK9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK7,sK8))))) = iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2899])).

cnf(c_5463,plain,
    ( r2_hidden(sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9)),X1) != iProver_top
    | sP0(sK8,sK7,X0,X1) != iProver_top
    | k3_xboole_0(sK5(sK8,sK7,X0,sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9))),sK8) = sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5154,c_36,c_37,c_38,c_2900])).

cnf(c_5464,plain,
    ( k3_xboole_0(sK5(sK8,sK7,X0,sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9))),sK8) = sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9))
    | sP0(sK8,sK7,X0,X1) != iProver_top
    | r2_hidden(sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9)),X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5463])).

cnf(c_5472,plain,
    ( k3_xboole_0(sK5(sK8,sK7,X0,sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9))),sK8) = sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9))
    | sP0(sK8,sK7,X0,k1_tops_2(sK7,sK8,sK9)) != iProver_top
    | m1_subset_1(k1_tops_2(sK7,sK8,sK9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK7,sK8))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2793,c_5464])).

cnf(c_5477,plain,
    ( sP0(sK8,sK7,X0,k1_tops_2(sK7,sK8,sK9)) != iProver_top
    | k3_xboole_0(sK5(sK8,sK7,X0,sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9))),sK8) = sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5472,c_36,c_37,c_38,c_2900])).

cnf(c_5478,plain,
    ( k3_xboole_0(sK5(sK8,sK7,X0,sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9))),sK8) = sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9))
    | sP0(sK8,sK7,X0,k1_tops_2(sK7,sK8,sK9)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5477])).

cnf(c_6141,plain,
    ( k3_xboole_0(sK5(sK8,sK7,sK9,sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9))),sK8) = sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9))
    | m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2316,c_5478])).

cnf(c_7269,plain,
    ( k3_xboole_0(sK5(sK8,sK7,sK9,sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9))),sK8) = sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6141,c_36,c_37,c_38])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(k1_pre_topc(X0,X1))
    | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_238,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(k1_pre_topc(X0,X1))
    | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2,c_19])).

cnf(c_239,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(k1_pre_topc(X1,X0))
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(renaming,[status(thm)],[c_238])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(k1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_244,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_239,c_20])).

cnf(c_245,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(renaming,[status(thm)],[c_244])).

cnf(c_2319,plain,
    ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_245])).

cnf(c_7750,plain,
    ( k2_struct_0(k1_pre_topc(sK7,sK8)) = sK8
    | l1_pre_topc(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2321,c_2319])).

cnf(c_2708,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ l1_pre_topc(sK7)
    | k2_struct_0(k1_pre_topc(sK7,sK8)) = sK8 ),
    inference(instantiation,[status(thm)],[c_245])).

cnf(c_7827,plain,
    ( k2_struct_0(k1_pre_topc(sK7,sK8)) = sK8 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7750,c_35,c_34,c_2708])).

cnf(c_26,plain,
    ( ~ v4_pre_topc(X0,X1)
    | v4_pre_topc(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_2327,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | v4_pre_topc(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),X2) = iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_7830,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | v4_pre_topc(k9_subset_1(u1_struct_0(k1_pre_topc(sK7,sK8)),X0,k2_struct_0(k1_pre_topc(sK7,sK8))),k1_pre_topc(sK7,sK8)) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK7,sK8),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k9_subset_1(u1_struct_0(k1_pre_topc(sK7,sK8)),X0,sK8),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK7,sK8)))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7827,c_2327])).

cnf(c_7870,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | v4_pre_topc(k9_subset_1(u1_struct_0(k1_pre_topc(sK7,sK8)),X0,sK8),k1_pre_topc(sK7,sK8)) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK7,sK8),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k9_subset_1(u1_struct_0(k1_pre_topc(sK7,sK8)),X0,sK8),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK7,sK8)))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7830,c_7827])).

cnf(c_2332,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3499,plain,
    ( m1_pre_topc(k1_pre_topc(sK7,sK8),sK7) = iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2321,c_2332])).

cnf(c_3768,plain,
    ( m1_pre_topc(k1_pre_topc(sK7,sK8),sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3499,c_36,c_37,c_2701])).

cnf(c_2329,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3773,plain,
    ( l1_pre_topc(k1_pre_topc(sK7,sK8)) = iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3768,c_2329])).

cnf(c_3945,plain,
    ( l1_pre_topc(k1_pre_topc(sK7,sK8)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3773,c_36,c_37,c_2676,c_2701])).

cnf(c_23,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_22,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_420,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_23,c_22])).

cnf(c_2318,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_420])).

cnf(c_7106,plain,
    ( k9_subset_1(u1_struct_0(X0),X1,k2_struct_0(X0)) = k3_xboole_0(X1,k2_struct_0(X0))
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2318,c_2328])).

cnf(c_7920,plain,
    ( k9_subset_1(u1_struct_0(k1_pre_topc(sK7,sK8)),X0,k2_struct_0(k1_pre_topc(sK7,sK8))) = k3_xboole_0(X0,k2_struct_0(k1_pre_topc(sK7,sK8))) ),
    inference(superposition,[status(thm)],[c_3945,c_7106])).

cnf(c_7935,plain,
    ( k9_subset_1(u1_struct_0(k1_pre_topc(sK7,sK8)),X0,sK8) = k3_xboole_0(X0,sK8) ),
    inference(light_normalisation,[status(thm)],[c_7920,c_7827])).

cnf(c_10587,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | v4_pre_topc(k3_xboole_0(X0,sK8),k1_pre_topc(sK7,sK8)) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK7,sK8),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k3_xboole_0(X0,sK8),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK7,sK8)))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7870,c_7935])).

cnf(c_10597,plain,
    ( v4_pre_topc(sK5(sK8,sK7,sK9,sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9))),X0) != iProver_top
    | v4_pre_topc(k3_xboole_0(sK5(sK8,sK7,sK9,sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9))),sK8),k1_pre_topc(sK7,sK8)) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK7,sK8),X0) != iProver_top
    | m1_subset_1(sK5(sK8,sK7,sK9,sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9))),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9)),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK7,sK8)))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7269,c_10587])).

cnf(c_10618,plain,
    ( v4_pre_topc(sK5(sK8,sK7,sK9,sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9))),X0) != iProver_top
    | v4_pre_topc(sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9)),k1_pre_topc(sK7,sK8)) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK7,sK8),X0) != iProver_top
    | m1_subset_1(sK5(sK8,sK7,sK9,sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9))),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9)),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK7,sK8)))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10597,c_7269])).

cnf(c_10629,plain,
    ( v4_pre_topc(sK5(sK8,sK7,sK9,sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9))),sK7) != iProver_top
    | v4_pre_topc(sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9)),k1_pre_topc(sK7,sK8)) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK7,sK8),sK7) != iProver_top
    | m1_subset_1(sK5(sK8,sK7,sK9,sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9))),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | m1_subset_1(sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9)),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK7,sK8)))) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_10618])).

cnf(c_16,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ r2_hidden(X4,X3)
    | r2_hidden(sK5(X0,X1,X2,X4),X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0)))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2334,plain,
    ( sP0(X0,X1,X2,X3) != iProver_top
    | r2_hidden(X4,X3) != iProver_top
    | r2_hidden(sK5(X0,X1,X2,X4),X2) = iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4564,plain,
    ( sP0(sK8,sK7,X0,X1) != iProver_top
    | r2_hidden(sK5(sK8,sK7,X0,sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9))),X0) = iProver_top
    | r2_hidden(sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9)),X1) != iProver_top
    | m1_subset_1(k1_tops_2(sK7,sK8,sK9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK7,sK8))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2801,c_2334])).

cnf(c_4766,plain,
    ( r2_hidden(sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9)),X1) != iProver_top
    | r2_hidden(sK5(sK8,sK7,X0,sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9))),X0) = iProver_top
    | sP0(sK8,sK7,X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4564,c_36,c_37,c_38,c_2900])).

cnf(c_4767,plain,
    ( sP0(sK8,sK7,X0,X1) != iProver_top
    | r2_hidden(sK5(sK8,sK7,X0,sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9))),X0) = iProver_top
    | r2_hidden(sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9)),X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_4766])).

cnf(c_4775,plain,
    ( sP0(sK8,sK7,X0,k1_tops_2(sK7,sK8,sK9)) != iProver_top
    | r2_hidden(sK5(sK8,sK7,X0,sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9))),X0) = iProver_top
    | m1_subset_1(k1_tops_2(sK7,sK8,sK9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK7,sK8))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2793,c_4767])).

cnf(c_4825,plain,
    ( r2_hidden(sK5(sK8,sK7,X0,sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9))),X0) = iProver_top
    | sP0(sK8,sK7,X0,k1_tops_2(sK7,sK8,sK9)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4775,c_36,c_37,c_38,c_731,c_783,c_2676,c_2701,c_2900,c_3336])).

cnf(c_4826,plain,
    ( sP0(sK8,sK7,X0,k1_tops_2(sK7,sK8,sK9)) != iProver_top
    | r2_hidden(sK5(sK8,sK7,X0,sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9))),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_4825])).

cnf(c_2322,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_30,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2323,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_2913,plain,
    ( r2_hidden(X0,sK9) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2322,c_2323])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | v4_pre_topc(X0,X2)
    | ~ v2_tops_2(X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_32,negated_conjecture,
    ( v2_tops_2(sK9,sK7) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_794,plain,
    ( ~ r2_hidden(X0,X1)
    | v4_pre_topc(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | sK9 != X1
    | sK7 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_32])).

cnf(c_795,plain,
    ( ~ r2_hidden(X0,sK9)
    | v4_pre_topc(X0,sK7)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_794])).

cnf(c_799,plain,
    ( ~ r2_hidden(X0,sK9)
    | v4_pre_topc(X0,sK7)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_795,c_35,c_33])).

cnf(c_2309,plain,
    ( r2_hidden(X0,sK9) != iProver_top
    | v4_pre_topc(X0,sK7) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_799])).

cnf(c_3235,plain,
    ( r2_hidden(X0,sK9) != iProver_top
    | v4_pre_topc(X0,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_2913,c_2309])).

cnf(c_4836,plain,
    ( sP0(sK8,sK7,sK9,k1_tops_2(sK7,sK8,sK9)) != iProver_top
    | v4_pre_topc(sK5(sK8,sK7,sK9,sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9))),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_4826,c_3235])).

cnf(c_17,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0))))
    | m1_subset_1(sK5(X0,X1,X2,X4),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_3027,plain,
    ( ~ sP0(X0,X1,X2,k1_tops_2(sK7,sK8,sK9))
    | ~ r2_hidden(sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9)),k1_tops_2(sK7,sK8,sK9))
    | m1_subset_1(sK5(X0,X1,X2,sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9))),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9)),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0)))) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_3330,plain,
    ( ~ sP0(sK8,sK7,X0,k1_tops_2(sK7,sK8,sK9))
    | ~ r2_hidden(sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9)),k1_tops_2(sK7,sK8,sK9))
    | m1_subset_1(sK5(sK8,sK7,X0,sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9))),k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ m1_subset_1(sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9)),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK7,sK8)))) ),
    inference(instantiation,[status(thm)],[c_3027])).

cnf(c_4619,plain,
    ( ~ sP0(sK8,sK7,sK9,k1_tops_2(sK7,sK8,sK9))
    | ~ r2_hidden(sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9)),k1_tops_2(sK7,sK8,sK9))
    | m1_subset_1(sK5(sK8,sK7,sK9,sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9))),k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ m1_subset_1(sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9)),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK7,sK8)))) ),
    inference(instantiation,[status(thm)],[c_3330])).

cnf(c_4625,plain,
    ( sP0(sK8,sK7,sK9,k1_tops_2(sK7,sK8,sK9)) != iProver_top
    | r2_hidden(sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9)),k1_tops_2(sK7,sK8,sK9)) != iProver_top
    | m1_subset_1(sK5(sK8,sK7,sK9,sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9))),k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top
    | m1_subset_1(sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9)),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK7,sK8)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4619])).

cnf(c_2769,plain,
    ( sP0(sK8,sK7,X0,k1_tops_2(sK7,sK8,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ l1_pre_topc(sK7) ),
    inference(instantiation,[status(thm)],[c_493])).

cnf(c_3138,plain,
    ( sP0(sK8,sK7,sK9,k1_tops_2(sK7,sK8,sK9))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ l1_pre_topc(sK7) ),
    inference(instantiation,[status(thm)],[c_2769])).

cnf(c_3139,plain,
    ( sP0(sK8,sK7,sK9,k1_tops_2(sK7,sK8,sK9)) = iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3138])).

cnf(c_3,plain,
    ( ~ v4_pre_topc(sK2(X0,X1),X0)
    | v2_tops_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_742,plain,
    ( ~ v4_pre_topc(sK2(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0)
    | k1_tops_2(sK7,sK8,sK9) != X1
    | k1_pre_topc(sK7,sK8) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_31])).

cnf(c_743,plain,
    ( ~ v4_pre_topc(sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9)),k1_pre_topc(sK7,sK8))
    | ~ m1_subset_1(k1_tops_2(sK7,sK8,sK9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK7,sK8)))))
    | ~ l1_pre_topc(k1_pre_topc(sK7,sK8)) ),
    inference(unflattening,[status(thm)],[c_742])).

cnf(c_744,plain,
    ( v4_pre_topc(sK2(k1_pre_topc(sK7,sK8),k1_tops_2(sK7,sK8,sK9)),k1_pre_topc(sK7,sK8)) != iProver_top
    | m1_subset_1(k1_tops_2(sK7,sK8,sK9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK7,sK8))))) != iProver_top
    | l1_pre_topc(k1_pre_topc(sK7,sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_743])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10629,c_4836,c_4625,c_3139,c_2900,c_2701,c_2676,c_783,c_744,c_731,c_38,c_37,c_36])).


%------------------------------------------------------------------------------
