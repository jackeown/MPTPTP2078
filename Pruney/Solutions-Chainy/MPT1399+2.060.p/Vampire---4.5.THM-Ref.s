%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:20 EST 2020

% Result     : Theorem 0.16s
% Output     : Refutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 251 expanded)
%              Number of leaves         :   25 (  81 expanded)
%              Depth                    :   16
%              Number of atoms          :  447 (2343 expanded)
%              Number of equality atoms :   49 ( 195 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f378,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f135,f151,f212,f227,f234,f377])).

fof(f377,plain,(
    ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f376])).

fof(f376,plain,
    ( $false
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f375,f44])).

fof(f44,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( k1_xboole_0 = sK2
    & ! [X3] :
        ( ( ( r2_hidden(X3,sK2)
            | ~ r2_hidden(sK1,X3)
            | ~ v4_pre_topc(X3,sK0)
            | ~ v3_pre_topc(X3,sK0) )
          & ( ( r2_hidden(sK1,X3)
              & v4_pre_topc(X3,sK0)
              & v3_pre_topc(X3,sK0) )
            | ~ r2_hidden(X3,sK2) ) )
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f38,f37,f36])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_xboole_0 = X2
                & ! [X3] :
                    ( ( ( r2_hidden(X3,X2)
                        | ~ r2_hidden(X1,X3)
                        | ~ v4_pre_topc(X3,X0)
                        | ~ v3_pre_topc(X3,X0) )
                      & ( ( r2_hidden(X1,X3)
                          & v4_pre_topc(X3,X0)
                          & v3_pre_topc(X3,X0) )
                        | ~ r2_hidden(X3,X2) ) )
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,sK0)
                      | ~ v3_pre_topc(X3,sK0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,sK0)
                        & v3_pre_topc(X3,sK0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k1_xboole_0 = X2
            & ! [X3] :
                ( ( ( r2_hidden(X3,X2)
                    | ~ r2_hidden(X1,X3)
                    | ~ v4_pre_topc(X3,sK0)
                    | ~ v3_pre_topc(X3,sK0) )
                  & ( ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,sK0)
                      & v3_pre_topc(X3,sK0) )
                    | ~ r2_hidden(X3,X2) ) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( k1_xboole_0 = X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(sK1,X3)
                  | ~ v4_pre_topc(X3,sK0)
                  | ~ v3_pre_topc(X3,sK0) )
                & ( ( r2_hidden(sK1,X3)
                    & v4_pre_topc(X3,sK0)
                    & v3_pre_topc(X3,sK0) )
                  | ~ r2_hidden(X3,X2) ) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X2] :
        ( k1_xboole_0 = X2
        & ! [X3] :
            ( ( ( r2_hidden(X3,X2)
                | ~ r2_hidden(sK1,X3)
                | ~ v4_pre_topc(X3,sK0)
                | ~ v3_pre_topc(X3,sK0) )
              & ( ( r2_hidden(sK1,X3)
                  & v4_pre_topc(X3,sK0)
                  & v3_pre_topc(X3,sK0) )
                | ~ r2_hidden(X3,X2) ) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( k1_xboole_0 = sK2
      & ! [X3] :
          ( ( ( r2_hidden(X3,sK2)
              | ~ r2_hidden(sK1,X3)
              | ~ v4_pre_topc(X3,sK0)
              | ~ v3_pre_topc(X3,sK0) )
            & ( ( r2_hidden(sK1,X3)
                & v4_pre_topc(X3,sK0)
                & v3_pre_topc(X3,sK0) )
              | ~ r2_hidden(X3,sK2) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ v3_pre_topc(X3,X0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,X0)
                        & v3_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ v3_pre_topc(X3,X0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,X0)
                        & v3_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ~ ( k1_xboole_0 = X2
                    & ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( r2_hidden(X3,X2)
                        <=> ( r2_hidden(X1,X3)
                            & v4_pre_topc(X3,X0)
                            & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ~ ( k1_xboole_0 = X2
                  & ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( r2_hidden(X3,X2)
                      <=> ( r2_hidden(X1,X3)
                          & v4_pre_topc(X3,X0)
                          & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).

fof(f375,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f374,f45])).

fof(f45,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f374,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f372,f46])).

fof(f46,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f372,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_5 ),
    inference(resolution,[],[f345,f134])).

fof(f134,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl5_5
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f345,plain,(
    ! [X1] :
      ( ~ v1_xboole_0(u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f327])).

fof(f327,plain,(
    ! [X1] :
      ( ~ v1_xboole_0(u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ v1_xboole_0(u1_struct_0(X1))
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(superposition,[],[f67,f322])).

fof(f322,plain,(
    ! [X4] :
      ( u1_struct_0(X4) = sK4(X4)
      | ~ v1_xboole_0(u1_struct_0(X4))
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X4) ) ),
    inference(resolution,[],[f289,f180])).

fof(f180,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f156,f55])).

fof(f55,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f156,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(resolution,[],[f66,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f66,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( v4_pre_topc(sK4(X0),X0)
        & v3_pre_topc(sK4(X0),X0)
        & ~ v1_xboole_0(sK4(X0))
        & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v4_pre_topc(sK4(X0),X0)
        & v3_pre_topc(sK4(X0),X0)
        & ~ v1_xboole_0(sK4(X0))
        & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_tops_1)).

fof(f289,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f208,f65])).

fof(f65,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f208,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f147])).

fof(f147,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | ~ r2_hidden(X1,k1_zfmisc_1(X0))
      | k1_xboole_0 = X1 ) ),
    inference(superposition,[],[f60,f58])).

fof(f58,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f60,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 != k3_tarski(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( ( r2_hidden(sK3(X0),X0)
          & k1_xboole_0 != sK3(X0) )
        | k1_xboole_0 = k3_tarski(X0) )
      & ( k1_xboole_0 != k3_tarski(X0)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | k1_xboole_0 = X2 ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,X0)
          & k1_xboole_0 != X1 )
     => ( r2_hidden(sK3(X0),X0)
        & k1_xboole_0 != sK3(X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ( ? [X1] :
            ( r2_hidden(X1,X0)
            & k1_xboole_0 != X1 )
        | k1_xboole_0 = k3_tarski(X0) )
      & ( k1_xboole_0 != k3_tarski(X0)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | k1_xboole_0 = X2 ) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k1_xboole_0 != k3_tarski(X0) )
      & ~ ( k1_xboole_0 = k3_tarski(X0)
          & ? [X2] :
              ( r2_hidden(X2,X0)
              & k1_xboole_0 != X2 ) ) ) ),
    inference(rectify,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k1_xboole_0 != k3_tarski(X0) )
      & ~ ( k1_xboole_0 = k3_tarski(X0)
          & ? [X1] :
              ( r2_hidden(X1,X0)
              & k1_xboole_0 != X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_orders_1)).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK4(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f234,plain,(
    ~ spl5_1 ),
    inference(avatar_contradiction_clause,[],[f233])).

fof(f233,plain,
    ( $false
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f230,f56])).

fof(f56,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f230,plain,
    ( ~ r1_tarski(k1_xboole_0,u1_struct_0(sK0))
    | ~ spl5_1 ),
    inference(resolution,[],[f226,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f226,plain,
    ( r2_hidden(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl5_1
  <=> r2_hidden(u1_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f227,plain,
    ( spl5_1
    | ~ spl5_4
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f225,f92,f88,f96,f85])).

fof(f96,plain,
    ( spl5_4
  <=> r2_hidden(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f88,plain,
    ( spl5_2
  <=> v3_pre_topc(u1_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f92,plain,
    ( spl5_3
  <=> v4_pre_topc(u1_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f225,plain,
    ( ~ r2_hidden(sK1,u1_struct_0(sK0))
    | r2_hidden(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f224,f89])).

fof(f89,plain,
    ( v3_pre_topc(u1_struct_0(sK0),sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f224,plain,
    ( ~ r2_hidden(sK1,u1_struct_0(sK0))
    | ~ v3_pre_topc(u1_struct_0(sK0),sK0)
    | r2_hidden(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f103,f93])).

fof(f93,plain,
    ( v4_pre_topc(u1_struct_0(sK0),sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f92])).

fof(f103,plain,
    ( ~ r2_hidden(sK1,u1_struct_0(sK0))
    | ~ v4_pre_topc(u1_struct_0(sK0),sK0)
    | ~ v3_pre_topc(u1_struct_0(sK0),sK0)
    | r2_hidden(u1_struct_0(sK0),k1_xboole_0) ),
    inference(resolution,[],[f74,f79])).

fof(f79,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f59,f57])).

fof(f57,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f59,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f74,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK1,X3)
      | ~ v4_pre_topc(X3,sK0)
      | ~ v3_pre_topc(X3,sK0)
      | r2_hidden(X3,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f52,f53])).

fof(f53,plain,(
    k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f39])).

fof(f52,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK2)
      | ~ r2_hidden(sK1,X3)
      | ~ v4_pre_topc(X3,sK0)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f212,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f211])).

fof(f211,plain,
    ( $false
    | spl5_3 ),
    inference(subsumption_resolution,[],[f210,f45])).

fof(f210,plain,
    ( ~ v2_pre_topc(sK0)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f209,f46])).

fof(f209,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl5_3 ),
    inference(resolution,[],[f185,f70])).

fof(f70,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).

fof(f185,plain,
    ( ~ v4_pre_topc(k2_struct_0(sK0),sK0)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f184,f80])).

fof(f80,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f64,f46])).

fof(f64,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f184,plain,
    ( ~ v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ l1_struct_0(sK0)
    | spl5_3 ),
    inference(superposition,[],[f106,f63])).

fof(f63,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f106,plain,
    ( ~ v4_pre_topc(u1_struct_0(sK0),sK0)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f92])).

fof(f151,plain,(
    spl5_2 ),
    inference(avatar_contradiction_clause,[],[f150])).

fof(f150,plain,
    ( $false
    | spl5_2 ),
    inference(subsumption_resolution,[],[f149,f45])).

fof(f149,plain,
    ( ~ v2_pre_topc(sK0)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f148,f46])).

fof(f148,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl5_2 ),
    inference(resolution,[],[f125,f71])).

fof(f71,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f125,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK0),sK0)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f124,f80])).

fof(f124,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK0),sK0)
    | ~ l1_struct_0(sK0)
    | spl5_2 ),
    inference(superposition,[],[f105,f63])).

fof(f105,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK0),sK0)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f135,plain,
    ( spl5_4
    | spl5_5 ),
    inference(avatar_split_clause,[],[f128,f133,f96])).

fof(f128,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f72,f47])).

fof(f47,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.10  % Command    : run_vampire %s %d
% 0.10/0.30  % Computer   : n012.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % WCLimit    : 600
% 0.10/0.30  % DateTime   : Tue Dec  1 09:14:52 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.16/0.39  % (16254)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.16/0.39  % (16252)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.16/0.40  % (16251)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.16/0.40  % (16252)Refutation not found, incomplete strategy% (16252)------------------------------
% 0.16/0.40  % (16252)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.16/0.40  % (16252)Termination reason: Refutation not found, incomplete strategy
% 0.16/0.40  
% 0.16/0.40  % (16252)Memory used [KB]: 10746
% 0.16/0.40  % (16252)Time elapsed: 0.037 s
% 0.16/0.40  % (16252)------------------------------
% 0.16/0.40  % (16252)------------------------------
% 0.16/0.40  % (16260)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.16/0.40  % (16261)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.16/0.41  % (16269)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.16/0.41  % (16261)Refutation not found, incomplete strategy% (16261)------------------------------
% 0.16/0.41  % (16261)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.16/0.41  % (16261)Termination reason: Refutation not found, incomplete strategy
% 0.16/0.41  
% 0.16/0.41  % (16261)Memory used [KB]: 10618
% 0.16/0.41  % (16261)Time elapsed: 0.044 s
% 0.16/0.41  % (16261)------------------------------
% 0.16/0.41  % (16261)------------------------------
% 0.16/0.41  % (16251)Refutation found. Thanks to Tanya!
% 0.16/0.41  % SZS status Theorem for theBenchmark
% 0.16/0.41  % SZS output start Proof for theBenchmark
% 0.16/0.41  fof(f378,plain,(
% 0.16/0.41    $false),
% 0.16/0.41    inference(avatar_sat_refutation,[],[f135,f151,f212,f227,f234,f377])).
% 0.16/0.41  fof(f377,plain,(
% 0.16/0.41    ~spl5_5),
% 0.16/0.41    inference(avatar_contradiction_clause,[],[f376])).
% 0.16/0.41  fof(f376,plain,(
% 0.16/0.41    $false | ~spl5_5),
% 0.16/0.41    inference(subsumption_resolution,[],[f375,f44])).
% 0.16/0.41  fof(f44,plain,(
% 0.16/0.41    ~v2_struct_0(sK0)),
% 0.16/0.41    inference(cnf_transformation,[],[f39])).
% 0.16/0.41  fof(f39,plain,(
% 0.16/0.41    ((k1_xboole_0 = sK2 & ! [X3] : (((r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,sK2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.16/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f38,f37,f36])).
% 0.16/0.41  fof(f36,plain,(
% 0.16/0.41    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.16/0.41    introduced(choice_axiom,[])).
% 0.16/0.41  fof(f37,plain,(
% 0.16/0.41    ? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.16/0.41    introduced(choice_axiom,[])).
% 0.16/0.41  fof(f38,plain,(
% 0.16/0.41    ? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (k1_xboole_0 = sK2 & ! [X3] : (((r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,sK2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.16/0.41    introduced(choice_axiom,[])).
% 0.16/0.41  fof(f35,plain,(
% 0.16/0.41    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.16/0.41    inference(flattening,[],[f34])).
% 0.16/0.41  fof(f34,plain,(
% 0.16/0.41    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | (~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0))) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.16/0.41    inference(nnf_transformation,[],[f20])).
% 0.16/0.41  fof(f20,plain,(
% 0.16/0.41    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.16/0.41    inference(flattening,[],[f19])).
% 0.16/0.41  fof(f19,plain,(
% 0.16/0.41    ? [X0] : (? [X1] : (? [X2] : ((k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.16/0.41    inference(ennf_transformation,[],[f17])).
% 0.16/0.41  fof(f17,negated_conjecture,(
% 0.16/0.41    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.16/0.41    inference(negated_conjecture,[],[f16])).
% 0.16/0.41  fof(f16,conjecture,(
% 0.16/0.41    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.16/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).
% 0.16/0.41  fof(f375,plain,(
% 0.16/0.41    v2_struct_0(sK0) | ~spl5_5),
% 0.16/0.41    inference(subsumption_resolution,[],[f374,f45])).
% 0.16/0.41  fof(f45,plain,(
% 0.16/0.41    v2_pre_topc(sK0)),
% 0.16/0.41    inference(cnf_transformation,[],[f39])).
% 0.16/0.41  fof(f374,plain,(
% 0.16/0.41    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_5),
% 0.16/0.41    inference(subsumption_resolution,[],[f372,f46])).
% 0.16/0.41  fof(f46,plain,(
% 0.16/0.41    l1_pre_topc(sK0)),
% 0.16/0.41    inference(cnf_transformation,[],[f39])).
% 0.16/0.41  fof(f372,plain,(
% 0.16/0.41    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_5),
% 0.16/0.41    inference(resolution,[],[f345,f134])).
% 0.16/0.41  fof(f134,plain,(
% 0.16/0.41    v1_xboole_0(u1_struct_0(sK0)) | ~spl5_5),
% 0.16/0.41    inference(avatar_component_clause,[],[f133])).
% 0.16/0.41  fof(f133,plain,(
% 0.16/0.41    spl5_5 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.16/0.41    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.16/0.41  fof(f345,plain,(
% 0.16/0.41    ( ! [X1] : (~v1_xboole_0(u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.16/0.41    inference(duplicate_literal_removal,[],[f327])).
% 0.16/0.41  fof(f327,plain,(
% 0.16/0.41    ( ! [X1] : (~v1_xboole_0(u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~v1_xboole_0(u1_struct_0(X1)) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X1)) )),
% 0.16/0.41    inference(superposition,[],[f67,f322])).
% 0.16/0.41  fof(f322,plain,(
% 0.16/0.41    ( ! [X4] : (u1_struct_0(X4) = sK4(X4) | ~v1_xboole_0(u1_struct_0(X4)) | ~v2_pre_topc(X4) | v2_struct_0(X4) | ~l1_pre_topc(X4)) )),
% 0.16/0.41    inference(resolution,[],[f289,f180])).
% 0.16/0.41  fof(f180,plain,(
% 0.16/0.41    ( ! [X0] : (r2_hidden(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.16/0.41    inference(subsumption_resolution,[],[f156,f55])).
% 0.16/0.41  fof(f55,plain,(
% 0.16/0.41    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.16/0.41    inference(cnf_transformation,[],[f7])).
% 0.16/0.41  fof(f7,axiom,(
% 0.16/0.41    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.16/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.16/0.41  fof(f156,plain,(
% 0.16/0.41    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v1_xboole_0(k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.16/0.41    inference(resolution,[],[f66,f72])).
% 0.16/0.41  fof(f72,plain,(
% 0.16/0.41    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.16/0.41    inference(cnf_transformation,[],[f32])).
% 0.16/0.41  fof(f32,plain,(
% 0.16/0.41    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.16/0.41    inference(flattening,[],[f31])).
% 0.16/0.41  fof(f31,plain,(
% 0.16/0.41    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.16/0.41    inference(ennf_transformation,[],[f8])).
% 0.16/0.41  fof(f8,axiom,(
% 0.16/0.41    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.16/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.16/0.41  fof(f66,plain,(
% 0.16/0.41    ( ! [X0] : (m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.16/0.41    inference(cnf_transformation,[],[f43])).
% 0.16/0.41  fof(f43,plain,(
% 0.16/0.41    ! [X0] : ((v4_pre_topc(sK4(X0),X0) & v3_pre_topc(sK4(X0),X0) & ~v1_xboole_0(sK4(X0)) & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.16/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f42])).
% 0.16/0.41  fof(f42,plain,(
% 0.16/0.41    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (v4_pre_topc(sK4(X0),X0) & v3_pre_topc(sK4(X0),X0) & ~v1_xboole_0(sK4(X0)) & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.16/0.41    introduced(choice_axiom,[])).
% 0.16/0.41  fof(f26,plain,(
% 0.16/0.41    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.16/0.41    inference(flattening,[],[f25])).
% 0.16/0.41  fof(f25,plain,(
% 0.16/0.41    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.16/0.41    inference(ennf_transformation,[],[f15])).
% 0.16/0.41  fof(f15,axiom,(
% 0.16/0.41    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.16/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_tops_1)).
% 0.16/0.41  fof(f289,plain,(
% 0.16/0.41    ( ! [X0,X1] : (~r2_hidden(X1,k1_zfmisc_1(X0)) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.16/0.41    inference(superposition,[],[f208,f65])).
% 0.16/0.41  fof(f65,plain,(
% 0.16/0.41    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.16/0.41    inference(cnf_transformation,[],[f24])).
% 0.16/0.41  fof(f24,plain,(
% 0.16/0.41    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.16/0.41    inference(ennf_transformation,[],[f2])).
% 0.16/0.41  fof(f2,axiom,(
% 0.16/0.41    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.16/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.16/0.41  fof(f208,plain,(
% 0.16/0.41    ( ! [X0] : (~r2_hidden(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) )),
% 0.16/0.41    inference(equality_resolution,[],[f147])).
% 0.16/0.41  fof(f147,plain,(
% 0.16/0.41    ( ! [X0,X1] : (k1_xboole_0 != X0 | ~r2_hidden(X1,k1_zfmisc_1(X0)) | k1_xboole_0 = X1) )),
% 0.16/0.41    inference(superposition,[],[f60,f58])).
% 0.16/0.41  fof(f58,plain,(
% 0.16/0.41    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 0.16/0.41    inference(cnf_transformation,[],[f4])).
% 0.16/0.41  fof(f4,axiom,(
% 0.16/0.41    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.16/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 0.16/0.41  fof(f60,plain,(
% 0.16/0.41    ( ! [X2,X0] : (k1_xboole_0 != k3_tarski(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X2) )),
% 0.16/0.41    inference(cnf_transformation,[],[f41])).
% 0.16/0.41  fof(f41,plain,(
% 0.16/0.41    ! [X0] : (((r2_hidden(sK3(X0),X0) & k1_xboole_0 != sK3(X0)) | k1_xboole_0 = k3_tarski(X0)) & (k1_xboole_0 != k3_tarski(X0) | ! [X2] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2)))),
% 0.16/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f40])).
% 0.16/0.41  fof(f40,plain,(
% 0.16/0.41    ! [X0] : (? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1) => (r2_hidden(sK3(X0),X0) & k1_xboole_0 != sK3(X0)))),
% 0.16/0.41    introduced(choice_axiom,[])).
% 0.16/0.41  fof(f21,plain,(
% 0.16/0.41    ! [X0] : ((? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1) | k1_xboole_0 = k3_tarski(X0)) & (k1_xboole_0 != k3_tarski(X0) | ! [X2] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2)))),
% 0.16/0.41    inference(ennf_transformation,[],[f18])).
% 0.16/0.41  fof(f18,plain,(
% 0.16/0.41    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X2] : (r2_hidden(X2,X0) & k1_xboole_0 != X2)))),
% 0.16/0.41    inference(rectify,[],[f13])).
% 0.16/0.41  fof(f13,axiom,(
% 0.16/0.41    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1)))),
% 0.16/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_orders_1)).
% 0.16/0.41  fof(f67,plain,(
% 0.16/0.41    ( ! [X0] : (~v1_xboole_0(sK4(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.16/0.41    inference(cnf_transformation,[],[f43])).
% 0.16/0.41  fof(f234,plain,(
% 0.16/0.41    ~spl5_1),
% 0.16/0.41    inference(avatar_contradiction_clause,[],[f233])).
% 0.16/0.41  fof(f233,plain,(
% 0.16/0.41    $false | ~spl5_1),
% 0.16/0.41    inference(subsumption_resolution,[],[f230,f56])).
% 0.16/0.41  fof(f56,plain,(
% 0.16/0.41    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.16/0.41    inference(cnf_transformation,[],[f3])).
% 0.16/0.41  fof(f3,axiom,(
% 0.16/0.41    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.16/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.16/0.41  fof(f230,plain,(
% 0.16/0.41    ~r1_tarski(k1_xboole_0,u1_struct_0(sK0)) | ~spl5_1),
% 0.16/0.41    inference(resolution,[],[f226,f73])).
% 0.16/0.41  fof(f73,plain,(
% 0.16/0.41    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.16/0.41    inference(cnf_transformation,[],[f33])).
% 0.16/0.41  fof(f33,plain,(
% 0.16/0.41    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.16/0.41    inference(ennf_transformation,[],[f9])).
% 0.16/0.41  fof(f9,axiom,(
% 0.16/0.41    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.16/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.16/0.41  fof(f226,plain,(
% 0.16/0.41    r2_hidden(u1_struct_0(sK0),k1_xboole_0) | ~spl5_1),
% 0.16/0.41    inference(avatar_component_clause,[],[f85])).
% 0.16/0.41  fof(f85,plain,(
% 0.16/0.41    spl5_1 <=> r2_hidden(u1_struct_0(sK0),k1_xboole_0)),
% 0.16/0.41    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.16/0.41  fof(f227,plain,(
% 0.16/0.41    spl5_1 | ~spl5_4 | ~spl5_2 | ~spl5_3),
% 0.16/0.41    inference(avatar_split_clause,[],[f225,f92,f88,f96,f85])).
% 0.16/0.41  fof(f96,plain,(
% 0.16/0.41    spl5_4 <=> r2_hidden(sK1,u1_struct_0(sK0))),
% 0.16/0.41    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.16/0.41  fof(f88,plain,(
% 0.16/0.41    spl5_2 <=> v3_pre_topc(u1_struct_0(sK0),sK0)),
% 0.16/0.41    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.16/0.41  fof(f92,plain,(
% 0.16/0.41    spl5_3 <=> v4_pre_topc(u1_struct_0(sK0),sK0)),
% 0.16/0.41    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.16/0.41  fof(f225,plain,(
% 0.16/0.41    ~r2_hidden(sK1,u1_struct_0(sK0)) | r2_hidden(u1_struct_0(sK0),k1_xboole_0) | (~spl5_2 | ~spl5_3)),
% 0.16/0.41    inference(subsumption_resolution,[],[f224,f89])).
% 0.16/0.41  fof(f89,plain,(
% 0.16/0.41    v3_pre_topc(u1_struct_0(sK0),sK0) | ~spl5_2),
% 0.16/0.41    inference(avatar_component_clause,[],[f88])).
% 0.16/0.41  fof(f224,plain,(
% 0.16/0.41    ~r2_hidden(sK1,u1_struct_0(sK0)) | ~v3_pre_topc(u1_struct_0(sK0),sK0) | r2_hidden(u1_struct_0(sK0),k1_xboole_0) | ~spl5_3),
% 0.16/0.41    inference(subsumption_resolution,[],[f103,f93])).
% 0.16/0.41  fof(f93,plain,(
% 0.16/0.41    v4_pre_topc(u1_struct_0(sK0),sK0) | ~spl5_3),
% 0.16/0.41    inference(avatar_component_clause,[],[f92])).
% 0.16/0.41  fof(f103,plain,(
% 0.16/0.41    ~r2_hidden(sK1,u1_struct_0(sK0)) | ~v4_pre_topc(u1_struct_0(sK0),sK0) | ~v3_pre_topc(u1_struct_0(sK0),sK0) | r2_hidden(u1_struct_0(sK0),k1_xboole_0)),
% 0.16/0.41    inference(resolution,[],[f74,f79])).
% 0.16/0.41  fof(f79,plain,(
% 0.16/0.41    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.16/0.41    inference(forward_demodulation,[],[f59,f57])).
% 0.16/0.41  fof(f57,plain,(
% 0.16/0.41    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.16/0.41    inference(cnf_transformation,[],[f5])).
% 0.16/0.41  fof(f5,axiom,(
% 0.16/0.41    ! [X0] : k2_subset_1(X0) = X0),
% 0.16/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.16/0.41  fof(f59,plain,(
% 0.16/0.41    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.16/0.41    inference(cnf_transformation,[],[f6])).
% 0.16/0.41  fof(f6,axiom,(
% 0.16/0.41    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.16/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.16/0.41  fof(f74,plain,(
% 0.16/0.41    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0) | r2_hidden(X3,k1_xboole_0)) )),
% 0.16/0.41    inference(forward_demodulation,[],[f52,f53])).
% 0.16/0.41  fof(f53,plain,(
% 0.16/0.41    k1_xboole_0 = sK2),
% 0.16/0.41    inference(cnf_transformation,[],[f39])).
% 0.16/0.41  fof(f52,plain,(
% 0.16/0.41    ( ! [X3] : (r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.16/0.41    inference(cnf_transformation,[],[f39])).
% 0.16/0.41  fof(f212,plain,(
% 0.16/0.41    spl5_3),
% 0.16/0.41    inference(avatar_contradiction_clause,[],[f211])).
% 0.16/0.41  fof(f211,plain,(
% 0.16/0.41    $false | spl5_3),
% 0.16/0.41    inference(subsumption_resolution,[],[f210,f45])).
% 0.16/0.41  fof(f210,plain,(
% 0.16/0.41    ~v2_pre_topc(sK0) | spl5_3),
% 0.16/0.41    inference(subsumption_resolution,[],[f209,f46])).
% 0.16/0.41  fof(f209,plain,(
% 0.16/0.41    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | spl5_3),
% 0.16/0.41    inference(resolution,[],[f185,f70])).
% 0.16/0.41  fof(f70,plain,(
% 0.16/0.41    ( ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.16/0.41    inference(cnf_transformation,[],[f28])).
% 0.16/0.41  fof(f28,plain,(
% 0.16/0.41    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.16/0.41    inference(flattening,[],[f27])).
% 0.16/0.41  fof(f27,plain,(
% 0.16/0.41    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.16/0.41    inference(ennf_transformation,[],[f12])).
% 0.16/0.41  fof(f12,axiom,(
% 0.16/0.41    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_struct_0(X0),X0))),
% 0.16/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).
% 0.16/0.41  fof(f185,plain,(
% 0.16/0.41    ~v4_pre_topc(k2_struct_0(sK0),sK0) | spl5_3),
% 0.16/0.41    inference(subsumption_resolution,[],[f184,f80])).
% 0.16/0.41  fof(f80,plain,(
% 0.16/0.41    l1_struct_0(sK0)),
% 0.16/0.41    inference(resolution,[],[f64,f46])).
% 0.16/0.41  fof(f64,plain,(
% 0.16/0.41    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.16/0.41    inference(cnf_transformation,[],[f23])).
% 0.16/0.41  fof(f23,plain,(
% 0.16/0.41    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.16/0.41    inference(ennf_transformation,[],[f11])).
% 0.16/0.41  fof(f11,axiom,(
% 0.16/0.41    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.16/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.16/0.41  fof(f184,plain,(
% 0.16/0.41    ~v4_pre_topc(k2_struct_0(sK0),sK0) | ~l1_struct_0(sK0) | spl5_3),
% 0.16/0.41    inference(superposition,[],[f106,f63])).
% 0.16/0.41  fof(f63,plain,(
% 0.16/0.41    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.16/0.41    inference(cnf_transformation,[],[f22])).
% 0.16/0.41  fof(f22,plain,(
% 0.16/0.41    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.16/0.41    inference(ennf_transformation,[],[f10])).
% 0.16/0.41  fof(f10,axiom,(
% 0.16/0.41    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.16/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.16/0.41  fof(f106,plain,(
% 0.16/0.41    ~v4_pre_topc(u1_struct_0(sK0),sK0) | spl5_3),
% 0.16/0.41    inference(avatar_component_clause,[],[f92])).
% 0.16/0.41  fof(f151,plain,(
% 0.16/0.41    spl5_2),
% 0.16/0.41    inference(avatar_contradiction_clause,[],[f150])).
% 0.16/0.41  fof(f150,plain,(
% 0.16/0.41    $false | spl5_2),
% 0.16/0.41    inference(subsumption_resolution,[],[f149,f45])).
% 0.16/0.41  fof(f149,plain,(
% 0.16/0.41    ~v2_pre_topc(sK0) | spl5_2),
% 0.16/0.41    inference(subsumption_resolution,[],[f148,f46])).
% 0.16/0.41  fof(f148,plain,(
% 0.16/0.41    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | spl5_2),
% 0.16/0.41    inference(resolution,[],[f125,f71])).
% 0.16/0.41  fof(f71,plain,(
% 0.16/0.41    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.16/0.41    inference(cnf_transformation,[],[f30])).
% 0.16/0.41  fof(f30,plain,(
% 0.16/0.41    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.16/0.41    inference(flattening,[],[f29])).
% 0.16/0.41  fof(f29,plain,(
% 0.16/0.41    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.16/0.41    inference(ennf_transformation,[],[f14])).
% 0.16/0.41  fof(f14,axiom,(
% 0.16/0.41    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 0.16/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).
% 0.16/0.41  fof(f125,plain,(
% 0.16/0.41    ~v3_pre_topc(k2_struct_0(sK0),sK0) | spl5_2),
% 0.16/0.41    inference(subsumption_resolution,[],[f124,f80])).
% 0.16/0.41  fof(f124,plain,(
% 0.16/0.41    ~v3_pre_topc(k2_struct_0(sK0),sK0) | ~l1_struct_0(sK0) | spl5_2),
% 0.16/0.41    inference(superposition,[],[f105,f63])).
% 0.16/0.41  fof(f105,plain,(
% 0.16/0.41    ~v3_pre_topc(u1_struct_0(sK0),sK0) | spl5_2),
% 0.16/0.41    inference(avatar_component_clause,[],[f88])).
% 0.16/0.41  fof(f135,plain,(
% 0.16/0.41    spl5_4 | spl5_5),
% 0.16/0.41    inference(avatar_split_clause,[],[f128,f133,f96])).
% 0.16/0.41  fof(f128,plain,(
% 0.16/0.41    v1_xboole_0(u1_struct_0(sK0)) | r2_hidden(sK1,u1_struct_0(sK0))),
% 0.16/0.41    inference(resolution,[],[f72,f47])).
% 0.16/0.41  fof(f47,plain,(
% 0.16/0.41    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.16/0.41    inference(cnf_transformation,[],[f39])).
% 0.16/0.41  % SZS output end Proof for theBenchmark
% 0.16/0.41  % (16251)------------------------------
% 0.16/0.41  % (16251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.16/0.41  % (16251)Termination reason: Refutation
% 0.16/0.41  
% 0.16/0.41  % (16251)Memory used [KB]: 10746
% 0.16/0.41  % (16251)Time elapsed: 0.047 s
% 0.16/0.41  % (16251)------------------------------
% 0.16/0.41  % (16251)------------------------------
% 0.16/0.41  % (16244)Success in time 0.098 s
%------------------------------------------------------------------------------
