%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:34 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 384 expanded)
%              Number of leaves         :   22 ( 134 expanded)
%              Depth                    :   24
%              Number of atoms          :  391 (2051 expanded)
%              Number of equality atoms :   55 ( 340 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f522,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f178,f185,f325,f496,f516])).

fof(f516,plain,(
    ~ spl5_18 ),
    inference(avatar_contradiction_clause,[],[f515])).

fof(f515,plain,
    ( $false
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f499,f80])).

fof(f80,plain,(
    ! [X0] : ~ v1_subset_1(X0,X0) ),
    inference(superposition,[],[f51,f52])).

fof(f52,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f51,plain,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

fof(f499,plain,
    ( v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl5_18 ),
    inference(superposition,[],[f98,f324])).

fof(f324,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK0)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f322])).

fof(f322,plain,
    ( spl5_18
  <=> u1_struct_0(sK1) = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f98,plain,(
    v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f97,f44])).

fof(f44,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ~ v1_tex_2(sK2,sK0)
    & v1_tex_2(sK1,sK0)
    & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    & m1_pre_topc(sK2,sK0)
    & m1_pre_topc(sK1,sK0)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f30,f29,f28])).

fof(f28,plain,
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
              ( ~ v1_tex_2(X2,sK0)
              & v1_tex_2(X1,sK0)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,sK0) )
          & m1_pre_topc(X1,sK0) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v1_tex_2(X2,sK0)
            & v1_tex_2(X1,sK0)
            & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
            & m1_pre_topc(X2,sK0) )
        & m1_pre_topc(X1,sK0) )
   => ( ? [X2] :
          ( ~ v1_tex_2(X2,sK0)
          & v1_tex_2(sK1,sK0)
          & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
          & m1_pre_topc(X2,sK0) )
      & m1_pre_topc(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X2] :
        ( ~ v1_tex_2(X2,sK0)
        & v1_tex_2(sK1,sK0)
        & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
        & m1_pre_topc(X2,sK0) )
   => ( ~ v1_tex_2(sK2,sK0)
      & v1_tex_2(sK1,sK0)
      & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
      & m1_pre_topc(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,X0)
              & v1_tex_2(X1,X0)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,X0)
              & v1_tex_2(X1,X0)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( ( v1_tex_2(X1,X0)
                    & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
                 => v1_tex_2(X2,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( ( v1_tex_2(X1,X0)
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
               => v1_tex_2(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_tex_2)).

% (5650)Termination reason: Refutation not found, incomplete strategy

% (5650)Memory used [KB]: 6268
% (5650)Time elapsed: 0.131 s
% (5650)------------------------------
% (5650)------------------------------
fof(f97,plain,
    ( v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f96,f45])).

fof(f45,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f96,plain,
    ( v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f79,f48])).

fof(f48,plain,(
    v1_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v1_tex_2(X1,X0)
      | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f73,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f73,plain,(
    ! [X0,X1] :
      ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( v1_subset_1(X3,u1_struct_0(X0))
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ( ~ v1_subset_1(sK3(X0,X1),u1_struct_0(X0))
                & u1_struct_0(X1) = sK3(X0,X1)
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK3(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK3(X0,X1)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).

fof(f496,plain,
    ( ~ spl5_7
    | spl5_17 ),
    inference(avatar_contradiction_clause,[],[f495])).

fof(f495,plain,
    ( $false
    | ~ spl5_7
    | spl5_17 ),
    inference(subsumption_resolution,[],[f494,f320])).

fof(f320,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1))
    | spl5_17 ),
    inference(avatar_component_clause,[],[f318])).

fof(f318,plain,
    ( spl5_17
  <=> r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f494,plain,
    ( r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl5_7 ),
    inference(resolution,[],[f493,f78])).

fof(f78,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK4(X0,X1),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r1_tarski(sK4(X0,X1),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f41,f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK4(X0,X1),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( r1_tarski(sK4(X0,X1),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f493,plain,
    ( r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f492,f50])).

fof(f50,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f492,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl5_7 ),
    inference(resolution,[],[f464,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f464,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f463,f177])).

fof(f177,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl5_7
  <=> u1_struct_0(sK2) = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f463,plain,(
    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f444,f84])).

fof(f84,plain,(
    l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f82,f44])).

fof(f82,plain,
    ( l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f56,f45])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f444,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f392,f57])).

fof(f392,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(subsumption_resolution,[],[f391,f85])).

fof(f85,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f83,f44])).

fof(f83,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f56,f46])).

fof(f46,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f391,plain,
    ( m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f384,f84])).

fof(f384,plain,
    ( m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f250,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f250,plain,(
    m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(forward_demodulation,[],[f249,f47])).

fof(f47,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f31])).

fof(f249,plain,(
    m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(subsumption_resolution,[],[f230,f85])).

fof(f230,plain,
    ( m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(duplicate_literal_removal,[],[f227])).

fof(f227,plain,
    ( m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f89,f54])).

% (5651)Termination reason: Refutation not found, incomplete strategy
fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

% (5651)Memory used [KB]: 10746
% (5651)Time elapsed: 0.129 s
% (5651)------------------------------
% (5651)------------------------------
fof(f89,plain,(
    m1_pre_topc(sK2,sK2) ),
    inference(resolution,[],[f85,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f325,plain,
    ( ~ spl5_17
    | spl5_18 ),
    inference(avatar_split_clause,[],[f315,f322,f318])).

fof(f315,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK0)
    | ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(resolution,[],[f292,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f292,plain,(
    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f167,f78])).

fof(f167,plain,(
    r2_hidden(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f166,f50])).

fof(f166,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f92,f63])).

fof(f92,plain,(
    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f90,f44])).

fof(f90,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f57,f45])).

fof(f185,plain,(
    ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f184])).

fof(f184,plain,
    ( $false
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f183,f44])).

fof(f183,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f182,f46])).

fof(f182,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f181,f49])).

fof(f49,plain,(
    ~ v1_tex_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f181,plain,
    ( v1_tex_2(sK2,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f180,f173])).

fof(f173,plain,
    ( v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl5_6
  <=> v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f180,plain,
    ( ~ v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0))
    | v1_tex_2(sK2,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f61,f116])).

fof(f116,plain,(
    u1_struct_0(sK2) = sK3(sK0,sK2) ),
    inference(subsumption_resolution,[],[f115,f44])).

fof(f115,plain,
    ( u1_struct_0(sK2) = sK3(sK0,sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f113,f49])).

fof(f113,plain,
    ( u1_struct_0(sK2) = sK3(sK0,sK2)
    | v1_tex_2(sK2,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f60,f46])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | u1_struct_0(X1) = sK3(X0,X1)
      | v1_tex_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

% (5658)Refutation not found, incomplete strategy% (5658)------------------------------
% (5658)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f178,plain,
    ( spl5_6
    | spl5_7 ),
    inference(avatar_split_clause,[],[f168,f175,f171])).

fof(f168,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK0)
    | v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0)) ),
    inference(resolution,[],[f93,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f93,plain,(
    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f91,f44])).

fof(f91,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f57,f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:39:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.52  % (5647)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.53  % (5663)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.54  % (5655)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.54  % (5653)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.55  % (5648)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.55  % (5649)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.55  % (5661)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.55  % (5650)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.55  % (5651)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.55  % (5669)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.55  % (5650)Refutation not found, incomplete strategy% (5650)------------------------------
% 0.20/0.55  % (5650)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (5657)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.56  % (5666)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.56  % (5651)Refutation not found, incomplete strategy% (5651)------------------------------
% 0.20/0.56  % (5651)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (5665)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.56  % (5664)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.56  % (5656)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.56  % (5658)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.56  % (5668)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.56  % (5660)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.56  % (5655)Refutation found. Thanks to Tanya!
% 0.20/0.56  % SZS status Theorem for theBenchmark
% 0.20/0.57  % SZS output start Proof for theBenchmark
% 0.20/0.57  fof(f522,plain,(
% 0.20/0.57    $false),
% 0.20/0.57    inference(avatar_sat_refutation,[],[f178,f185,f325,f496,f516])).
% 0.20/0.57  fof(f516,plain,(
% 0.20/0.57    ~spl5_18),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f515])).
% 0.20/0.57  fof(f515,plain,(
% 0.20/0.57    $false | ~spl5_18),
% 0.20/0.57    inference(subsumption_resolution,[],[f499,f80])).
% 0.20/0.57  fof(f80,plain,(
% 0.20/0.57    ( ! [X0] : (~v1_subset_1(X0,X0)) )),
% 0.20/0.57    inference(superposition,[],[f51,f52])).
% 0.20/0.57  fof(f52,plain,(
% 0.20/0.57    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.57    inference(cnf_transformation,[],[f3])).
% 0.20/0.57  fof(f3,axiom,(
% 0.20/0.57    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.57  fof(f51,plain,(
% 0.20/0.57    ( ! [X0] : (~v1_subset_1(k2_subset_1(X0),X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f5])).
% 0.20/0.57  fof(f5,axiom,(
% 0.20/0.57    ! [X0] : ~v1_subset_1(k2_subset_1(X0),X0)),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).
% 0.20/0.57  fof(f499,plain,(
% 0.20/0.57    v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) | ~spl5_18),
% 0.20/0.57    inference(superposition,[],[f98,f324])).
% 0.20/0.57  fof(f324,plain,(
% 0.20/0.57    u1_struct_0(sK1) = u1_struct_0(sK0) | ~spl5_18),
% 0.20/0.57    inference(avatar_component_clause,[],[f322])).
% 0.20/0.57  fof(f322,plain,(
% 0.20/0.57    spl5_18 <=> u1_struct_0(sK1) = u1_struct_0(sK0)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.20/0.57  fof(f98,plain,(
% 0.20/0.57    v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.20/0.57    inference(subsumption_resolution,[],[f97,f44])).
% 0.20/0.57  fof(f44,plain,(
% 0.20/0.57    l1_pre_topc(sK0)),
% 0.20/0.57    inference(cnf_transformation,[],[f31])).
% 0.20/0.57  fof(f31,plain,(
% 0.20/0.57    ((~v1_tex_2(sK2,sK0) & v1_tex_2(sK1,sK0) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_pre_topc(sK2,sK0)) & m1_pre_topc(sK1,sK0)) & l1_pre_topc(sK0)),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f30,f29,f28])).
% 0.20/0.57  fof(f28,plain,(
% 0.20/0.57    ? [X0] : (? [X1] : (? [X2] : (~v1_tex_2(X2,X0) & v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tex_2(X2,sK0) & v1_tex_2(X1,sK0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,sK0)) & m1_pre_topc(X1,sK0)) & l1_pre_topc(sK0))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f29,plain,(
% 0.20/0.57    ? [X1] : (? [X2] : (~v1_tex_2(X2,sK0) & v1_tex_2(X1,sK0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,sK0)) & m1_pre_topc(X1,sK0)) => (? [X2] : (~v1_tex_2(X2,sK0) & v1_tex_2(sK1,sK0) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_pre_topc(X2,sK0)) & m1_pre_topc(sK1,sK0))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.58  fof(f30,plain,(
% 0.20/0.58    ? [X2] : (~v1_tex_2(X2,sK0) & v1_tex_2(sK1,sK0) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_pre_topc(X2,sK0)) => (~v1_tex_2(sK2,sK0) & v1_tex_2(sK1,sK0) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_pre_topc(sK2,sK0))),
% 0.20/0.58    introduced(choice_axiom,[])).
% 0.20/0.58  fof(f17,plain,(
% 0.20/0.58    ? [X0] : (? [X1] : (? [X2] : (~v1_tex_2(X2,X0) & v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.20/0.58    inference(flattening,[],[f16])).
% 0.20/0.58  fof(f16,plain,(
% 0.20/0.58    ? [X0] : (? [X1] : (? [X2] : ((~v1_tex_2(X2,X0) & (v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.20/0.58    inference(ennf_transformation,[],[f15])).
% 0.20/0.58  fof(f15,negated_conjecture,(
% 0.20/0.58    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ((v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) => v1_tex_2(X2,X0)))))),
% 0.20/0.58    inference(negated_conjecture,[],[f14])).
% 0.20/0.58  fof(f14,conjecture,(
% 0.20/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ((v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) => v1_tex_2(X2,X0)))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_tex_2)).
% 0.20/0.58  % (5650)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.58  
% 0.20/0.58  % (5650)Memory used [KB]: 6268
% 0.20/0.58  % (5650)Time elapsed: 0.131 s
% 0.20/0.58  % (5650)------------------------------
% 0.20/0.58  % (5650)------------------------------
% 0.20/0.58  fof(f97,plain,(
% 0.20/0.58    v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0)),
% 0.20/0.58    inference(subsumption_resolution,[],[f96,f45])).
% 0.20/0.58  fof(f45,plain,(
% 0.20/0.58    m1_pre_topc(sK1,sK0)),
% 0.20/0.58    inference(cnf_transformation,[],[f31])).
% 0.20/0.58  fof(f96,plain,(
% 0.20/0.58    v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.20/0.58    inference(resolution,[],[f79,f48])).
% 0.20/0.58  fof(f48,plain,(
% 0.20/0.58    v1_tex_2(sK1,sK0)),
% 0.20/0.58    inference(cnf_transformation,[],[f31])).
% 0.20/0.58  fof(f79,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~v1_tex_2(X1,X0) | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f73,f57])).
% 0.20/0.58  fof(f57,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f21])).
% 0.20/0.58  fof(f21,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.58    inference(ennf_transformation,[],[f10])).
% 0.20/0.58  fof(f10,axiom,(
% 0.20/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.20/0.58  fof(f73,plain,(
% 0.20/0.58    ( ! [X0,X1] : (v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.58    inference(equality_resolution,[],[f58])).
% 0.20/0.58  fof(f58,plain,(
% 0.20/0.58    ( ! [X0,X3,X1] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f36])).
% 0.20/0.58  fof(f36,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK3(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK3(X0,X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f35])).
% 0.20/0.58  fof(f35,plain,(
% 0.20/0.58    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK3(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK3(X0,X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.58    introduced(choice_axiom,[])).
% 0.20/0.58  fof(f34,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.58    inference(rectify,[],[f33])).
% 0.20/0.58  fof(f33,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.58    inference(nnf_transformation,[],[f23])).
% 0.20/0.58  fof(f23,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.58    inference(flattening,[],[f22])).
% 0.20/0.58  fof(f22,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.58    inference(ennf_transformation,[],[f12])).
% 0.20/0.58  fof(f12,axiom,(
% 0.20/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).
% 0.20/0.58  fof(f496,plain,(
% 0.20/0.58    ~spl5_7 | spl5_17),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f495])).
% 0.20/0.58  fof(f495,plain,(
% 0.20/0.58    $false | (~spl5_7 | spl5_17)),
% 0.20/0.58    inference(subsumption_resolution,[],[f494,f320])).
% 0.20/0.58  fof(f320,plain,(
% 0.20/0.58    ~r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1)) | spl5_17),
% 0.20/0.58    inference(avatar_component_clause,[],[f318])).
% 0.20/0.58  fof(f318,plain,(
% 0.20/0.58    spl5_17 <=> r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.20/0.58  fof(f494,plain,(
% 0.20/0.58    r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl5_7),
% 0.20/0.58    inference(resolution,[],[f493,f78])).
% 0.20/0.58  fof(f78,plain,(
% 0.20/0.58    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 0.20/0.58    inference(equality_resolution,[],[f69])).
% 0.20/0.58  fof(f69,plain,(
% 0.20/0.58    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.20/0.58    inference(cnf_transformation,[],[f43])).
% 0.20/0.58  fof(f43,plain,(
% 0.20/0.58    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.20/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f41,f42])).
% 0.20/0.58  fof(f42,plain,(
% 0.20/0.58    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 0.20/0.58    introduced(choice_axiom,[])).
% 0.20/0.58  fof(f41,plain,(
% 0.20/0.58    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.20/0.58    inference(rectify,[],[f40])).
% 0.20/0.58  fof(f40,plain,(
% 0.20/0.58    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.20/0.58    inference(nnf_transformation,[],[f2])).
% 0.20/0.58  fof(f2,axiom,(
% 0.20/0.58    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.20/0.58  fof(f493,plain,(
% 0.20/0.58    r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK1))) | ~spl5_7),
% 0.20/0.58    inference(subsumption_resolution,[],[f492,f50])).
% 0.20/0.58  fof(f50,plain,(
% 0.20/0.58    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f4])).
% 0.20/0.58  fof(f4,axiom,(
% 0.20/0.58    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.20/0.58  fof(f492,plain,(
% 0.20/0.58    v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK1))) | r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK1))) | ~spl5_7),
% 0.20/0.58    inference(resolution,[],[f464,f63])).
% 0.20/0.58  fof(f63,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f26])).
% 0.20/0.58  fof(f26,plain,(
% 0.20/0.58    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.58    inference(flattening,[],[f25])).
% 0.20/0.58  fof(f25,plain,(
% 0.20/0.58    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.58    inference(ennf_transformation,[],[f6])).
% 0.20/0.58  fof(f6,axiom,(
% 0.20/0.58    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.58  fof(f464,plain,(
% 0.20/0.58    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK1))) | ~spl5_7),
% 0.20/0.58    inference(forward_demodulation,[],[f463,f177])).
% 0.20/0.58  fof(f177,plain,(
% 0.20/0.58    u1_struct_0(sK2) = u1_struct_0(sK0) | ~spl5_7),
% 0.20/0.58    inference(avatar_component_clause,[],[f175])).
% 0.20/0.58  fof(f175,plain,(
% 0.20/0.58    spl5_7 <=> u1_struct_0(sK2) = u1_struct_0(sK0)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.58  fof(f463,plain,(
% 0.20/0.58    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.20/0.58    inference(subsumption_resolution,[],[f444,f84])).
% 0.20/0.58  fof(f84,plain,(
% 0.20/0.58    l1_pre_topc(sK1)),
% 0.20/0.58    inference(subsumption_resolution,[],[f82,f44])).
% 0.20/0.58  fof(f82,plain,(
% 0.20/0.58    l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.20/0.58    inference(resolution,[],[f56,f45])).
% 0.20/0.58  fof(f56,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f20])).
% 0.20/0.58  fof(f20,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.58    inference(ennf_transformation,[],[f7])).
% 0.20/0.58  fof(f7,axiom,(
% 0.20/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.58  fof(f444,plain,(
% 0.20/0.58    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)),
% 0.20/0.58    inference(resolution,[],[f392,f57])).
% 0.20/0.58  fof(f392,plain,(
% 0.20/0.58    m1_pre_topc(sK2,sK1)),
% 0.20/0.58    inference(subsumption_resolution,[],[f391,f85])).
% 0.20/0.58  fof(f85,plain,(
% 0.20/0.58    l1_pre_topc(sK2)),
% 0.20/0.58    inference(subsumption_resolution,[],[f83,f44])).
% 0.20/0.58  fof(f83,plain,(
% 0.20/0.58    l1_pre_topc(sK2) | ~l1_pre_topc(sK0)),
% 0.20/0.58    inference(resolution,[],[f56,f46])).
% 0.20/0.58  fof(f46,plain,(
% 0.20/0.58    m1_pre_topc(sK2,sK0)),
% 0.20/0.58    inference(cnf_transformation,[],[f31])).
% 0.20/0.58  fof(f391,plain,(
% 0.20/0.58    m1_pre_topc(sK2,sK1) | ~l1_pre_topc(sK2)),
% 0.20/0.58    inference(subsumption_resolution,[],[f384,f84])).
% 0.20/0.58  fof(f384,plain,(
% 0.20/0.58    m1_pre_topc(sK2,sK1) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK2)),
% 0.20/0.58    inference(resolution,[],[f250,f55])).
% 0.20/0.58  fof(f55,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f32])).
% 0.20/0.58  fof(f32,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.20/0.58    inference(nnf_transformation,[],[f19])).
% 0.20/0.58  fof(f19,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.20/0.58    inference(ennf_transformation,[],[f9])).
% 0.20/0.58  fof(f9,axiom,(
% 0.20/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).
% 0.20/0.58  fof(f250,plain,(
% 0.20/0.58    m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.20/0.58    inference(forward_demodulation,[],[f249,f47])).
% 0.20/0.58  fof(f47,plain,(
% 0.20/0.58    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 0.20/0.58    inference(cnf_transformation,[],[f31])).
% 0.20/0.58  fof(f249,plain,(
% 0.20/0.58    m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),
% 0.20/0.58    inference(subsumption_resolution,[],[f230,f85])).
% 0.20/0.58  fof(f230,plain,(
% 0.20/0.58    m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~l1_pre_topc(sK2)),
% 0.20/0.58    inference(duplicate_literal_removal,[],[f227])).
% 0.20/0.58  fof(f227,plain,(
% 0.20/0.58    m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~l1_pre_topc(sK2) | ~l1_pre_topc(sK2)),
% 0.20/0.58    inference(resolution,[],[f89,f54])).
% 0.20/0.58  % (5651)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.58  fof(f54,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f32])).
% 0.20/0.58  
% 0.20/0.58  % (5651)Memory used [KB]: 10746
% 0.20/0.58  % (5651)Time elapsed: 0.129 s
% 0.20/0.58  % (5651)------------------------------
% 0.20/0.58  % (5651)------------------------------
% 0.20/0.58  fof(f89,plain,(
% 0.20/0.58    m1_pre_topc(sK2,sK2)),
% 0.20/0.58    inference(resolution,[],[f85,f53])).
% 0.20/0.58  fof(f53,plain,(
% 0.20/0.58    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f18])).
% 0.20/0.58  fof(f18,plain,(
% 0.20/0.58    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.20/0.58    inference(ennf_transformation,[],[f11])).
% 0.20/0.58  fof(f11,axiom,(
% 0.20/0.58    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.20/0.58  fof(f325,plain,(
% 0.20/0.58    ~spl5_17 | spl5_18),
% 0.20/0.58    inference(avatar_split_clause,[],[f315,f322,f318])).
% 0.20/0.58  fof(f315,plain,(
% 0.20/0.58    u1_struct_0(sK1) = u1_struct_0(sK0) | ~r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.58    inference(resolution,[],[f292,f68])).
% 0.20/0.58  fof(f68,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f39])).
% 0.20/0.58  fof(f39,plain,(
% 0.20/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.58    inference(flattening,[],[f38])).
% 0.20/0.58  fof(f38,plain,(
% 0.20/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.58    inference(nnf_transformation,[],[f1])).
% 0.20/0.58  fof(f1,axiom,(
% 0.20/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.58  fof(f292,plain,(
% 0.20/0.58    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.20/0.58    inference(resolution,[],[f167,f78])).
% 0.20/0.58  fof(f167,plain,(
% 0.20/0.58    r2_hidden(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.58    inference(subsumption_resolution,[],[f166,f50])).
% 0.20/0.58  fof(f166,plain,(
% 0.20/0.58    v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.58    inference(resolution,[],[f92,f63])).
% 0.20/0.58  fof(f92,plain,(
% 0.20/0.58    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.58    inference(subsumption_resolution,[],[f90,f44])).
% 0.20/0.58  fof(f90,plain,(
% 0.20/0.58    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.20/0.58    inference(resolution,[],[f57,f45])).
% 0.20/0.58  fof(f185,plain,(
% 0.20/0.58    ~spl5_6),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f184])).
% 0.20/0.58  fof(f184,plain,(
% 0.20/0.58    $false | ~spl5_6),
% 0.20/0.58    inference(subsumption_resolution,[],[f183,f44])).
% 0.20/0.58  fof(f183,plain,(
% 0.20/0.58    ~l1_pre_topc(sK0) | ~spl5_6),
% 0.20/0.58    inference(subsumption_resolution,[],[f182,f46])).
% 0.20/0.58  fof(f182,plain,(
% 0.20/0.58    ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0) | ~spl5_6),
% 0.20/0.58    inference(subsumption_resolution,[],[f181,f49])).
% 0.20/0.58  fof(f49,plain,(
% 0.20/0.58    ~v1_tex_2(sK2,sK0)),
% 0.20/0.58    inference(cnf_transformation,[],[f31])).
% 0.20/0.58  fof(f181,plain,(
% 0.20/0.58    v1_tex_2(sK2,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0) | ~spl5_6),
% 0.20/0.58    inference(subsumption_resolution,[],[f180,f173])).
% 0.20/0.58  fof(f173,plain,(
% 0.20/0.58    v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0)) | ~spl5_6),
% 0.20/0.58    inference(avatar_component_clause,[],[f171])).
% 0.20/0.58  fof(f171,plain,(
% 0.20/0.58    spl5_6 <=> v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.58  fof(f180,plain,(
% 0.20/0.58    ~v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0)) | v1_tex_2(sK2,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0)),
% 0.20/0.58    inference(superposition,[],[f61,f116])).
% 0.20/0.58  fof(f116,plain,(
% 0.20/0.58    u1_struct_0(sK2) = sK3(sK0,sK2)),
% 0.20/0.58    inference(subsumption_resolution,[],[f115,f44])).
% 0.20/0.58  fof(f115,plain,(
% 0.20/0.58    u1_struct_0(sK2) = sK3(sK0,sK2) | ~l1_pre_topc(sK0)),
% 0.20/0.58    inference(subsumption_resolution,[],[f113,f49])).
% 0.20/0.58  fof(f113,plain,(
% 0.20/0.58    u1_struct_0(sK2) = sK3(sK0,sK2) | v1_tex_2(sK2,sK0) | ~l1_pre_topc(sK0)),
% 0.20/0.58    inference(resolution,[],[f60,f46])).
% 0.20/0.58  fof(f60,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | u1_struct_0(X1) = sK3(X0,X1) | v1_tex_2(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f36])).
% 0.20/0.58  % (5658)Refutation not found, incomplete strategy% (5658)------------------------------
% 0.20/0.58  % (5658)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  fof(f61,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~v1_subset_1(sK3(X0,X1),u1_struct_0(X0)) | v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f36])).
% 0.20/0.58  fof(f178,plain,(
% 0.20/0.58    spl5_6 | spl5_7),
% 0.20/0.58    inference(avatar_split_clause,[],[f168,f175,f171])).
% 0.20/0.58  fof(f168,plain,(
% 0.20/0.58    u1_struct_0(sK2) = u1_struct_0(sK0) | v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0))),
% 0.20/0.58    inference(resolution,[],[f93,f65])).
% 0.20/0.58  fof(f65,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f37])).
% 0.20/0.58  fof(f37,plain,(
% 0.20/0.58    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.58    inference(nnf_transformation,[],[f27])).
% 0.20/0.58  fof(f27,plain,(
% 0.20/0.58    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.58    inference(ennf_transformation,[],[f13])).
% 0.20/0.58  fof(f13,axiom,(
% 0.20/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 0.20/0.58  fof(f93,plain,(
% 0.20/0.58    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.58    inference(subsumption_resolution,[],[f91,f44])).
% 0.20/0.58  fof(f91,plain,(
% 0.20/0.58    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.20/0.58    inference(resolution,[],[f57,f46])).
% 0.20/0.58  % SZS output end Proof for theBenchmark
% 0.20/0.58  % (5655)------------------------------
% 0.20/0.58  % (5655)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (5655)Termination reason: Refutation
% 0.20/0.58  
% 0.20/0.58  % (5655)Memory used [KB]: 10874
% 0.20/0.58  % (5655)Time elapsed: 0.154 s
% 0.20/0.58  % (5655)------------------------------
% 0.20/0.58  % (5655)------------------------------
% 0.20/0.58  % (5658)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.58  
% 0.20/0.58  % (5658)Memory used [KB]: 6396
% 0.20/0.58  % (5658)Time elapsed: 0.154 s
% 0.20/0.58  % (5658)------------------------------
% 0.20/0.58  % (5658)------------------------------
% 0.20/0.58  % (5644)Success in time 0.226 s
%------------------------------------------------------------------------------
