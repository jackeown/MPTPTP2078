%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1864+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:35 EST 2020

% Result     : Theorem 47.96s
% Output     : Refutation 47.96s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 275 expanded)
%              Number of leaves         :   19 ( 100 expanded)
%              Depth                    :   15
%              Number of atoms          :  331 (1837 expanded)
%              Number of equality atoms :   53 ( 271 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f97801,plain,(
    $false ),
    inference(subsumption_resolution,[],[f97773,f26486])).

fof(f26486,plain,(
    k1_tarski(sK33) != k3_xboole_0(sK32,sK56(sK32,sK31,k1_tarski(sK33))) ),
    inference(subsumption_resolution,[],[f26485,f6491])).

fof(f6491,plain,(
    sP7(sK32,sK31) ),
    inference(subsumption_resolution,[],[f6489,f4424])).

fof(f4424,plain,(
    v2_tex_2(sK32,sK31) ),
    inference(cnf_transformation,[],[f4109])).

fof(f4109,plain,
    ( ! [X3] :
        ( k9_subset_1(u1_struct_0(sK31),sK32,X3) != k1_tarski(sK33)
        | ~ v3_pre_topc(X3,sK31)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK31))) )
    & r2_hidden(sK33,sK32)
    & m1_subset_1(sK33,u1_struct_0(sK31))
    & v2_tex_2(sK32,sK31)
    & m1_subset_1(sK32,k1_zfmisc_1(u1_struct_0(sK31)))
    & l1_pre_topc(sK31) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK31,sK32,sK33])],[f3685,f4108,f4107,f4106])).

fof(f4106,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK31),X1,X3)
                  | ~ v3_pre_topc(X3,sK31)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK31))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(sK31)) )
          & v2_tex_2(X1,sK31)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK31))) )
      & l1_pre_topc(sK31) ) ),
    introduced(choice_axiom,[])).

fof(f4107,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ! [X3] :
                ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK31),X1,X3)
                | ~ v3_pre_topc(X3,sK31)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK31))) )
            & r2_hidden(X2,X1)
            & m1_subset_1(X2,u1_struct_0(sK31)) )
        & v2_tex_2(X1,sK31)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK31))) )
   => ( ? [X2] :
          ( ! [X3] :
              ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK31),sK32,X3)
              | ~ v3_pre_topc(X3,sK31)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK31))) )
          & r2_hidden(X2,sK32)
          & m1_subset_1(X2,u1_struct_0(sK31)) )
      & v2_tex_2(sK32,sK31)
      & m1_subset_1(sK32,k1_zfmisc_1(u1_struct_0(sK31))) ) ),
    introduced(choice_axiom,[])).

fof(f4108,plain,
    ( ? [X2] :
        ( ! [X3] :
            ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK31),sK32,X3)
            | ~ v3_pre_topc(X3,sK31)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK31))) )
        & r2_hidden(X2,sK32)
        & m1_subset_1(X2,u1_struct_0(sK31)) )
   => ( ! [X3] :
          ( k9_subset_1(u1_struct_0(sK31),sK32,X3) != k1_tarski(sK33)
          | ~ v3_pre_topc(X3,sK31)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK31))) )
      & r2_hidden(sK33,sK32)
      & m1_subset_1(sK33,u1_struct_0(sK31)) ) ),
    introduced(choice_axiom,[])).

fof(f3685,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f3684])).

fof(f3684,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3668])).

fof(f3668,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tex_2(X1,X0)
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ~ ( ! [X3] :
                          ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                         => ~ ( k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,X3)
                              & v3_pre_topc(X3,X0) ) )
                      & r2_hidden(X2,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3667])).

fof(f3667,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,X3)
                            & v3_pre_topc(X3,X0) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tex_2)).

fof(f6489,plain,
    ( sP7(sK32,sK31)
    | ~ v2_tex_2(sK32,sK31) ),
    inference(resolution,[],[f5724,f4539])).

fof(f4539,plain,(
    ! [X0,X1] :
      ( sP7(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ sP8(X0,X1) ) ),
    inference(cnf_transformation,[],[f4184])).

fof(f4184,plain,(
    ! [X0,X1] :
      ( ( ( v2_tex_2(X1,X0)
          | ~ sP7(X1,X0) )
        & ( sP7(X1,X0)
          | ~ v2_tex_2(X1,X0) ) )
      | ~ sP8(X0,X1) ) ),
    inference(nnf_transformation,[],[f4068])).

fof(f4068,plain,(
    ! [X0,X1] :
      ( ( v2_tex_2(X1,X0)
      <=> sP7(X1,X0) )
      | ~ sP8(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP8])])).

fof(f5724,plain,(
    sP8(sK31,sK32) ),
    inference(subsumption_resolution,[],[f5560,f4422])).

fof(f4422,plain,(
    l1_pre_topc(sK31) ),
    inference(cnf_transformation,[],[f4109])).

fof(f5560,plain,
    ( sP8(sK31,sK32)
    | ~ l1_pre_topc(sK31) ),
    inference(resolution,[],[f4423,f4547])).

fof(f4547,plain,(
    ! [X0,X1] :
      ( sP8(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f4069])).

fof(f4069,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP8(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f3750,f4068,f4067])).

fof(f4067,plain,(
    ! [X1,X0] :
      ( sP7(X1,X0)
    <=> ! [X2] :
          ( ? [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
              & v3_pre_topc(X3,X0)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ r1_tarski(X2,X1)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).

fof(f3750,plain,(
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
    inference(flattening,[],[f3749])).

fof(f3749,plain,(
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
    inference(ennf_transformation,[],[f3605])).

fof(f3605,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).

fof(f4423,plain,(
    m1_subset_1(sK32,k1_zfmisc_1(u1_struct_0(sK31))) ),
    inference(cnf_transformation,[],[f4109])).

fof(f26485,plain,
    ( k1_tarski(sK33) != k3_xboole_0(sK32,sK56(sK32,sK31,k1_tarski(sK33)))
    | ~ sP7(sK32,sK31) ),
    inference(subsumption_resolution,[],[f26440,f9748])).

fof(f9748,plain,(
    m1_subset_1(k1_tarski(sK33),k1_zfmisc_1(u1_struct_0(sK31))) ),
    inference(resolution,[],[f9715,f4483])).

fof(f4483,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f3706])).

fof(f3706,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f535])).

fof(f535,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(f9715,plain,(
    r2_hidden(sK33,u1_struct_0(sK31)) ),
    inference(resolution,[],[f5447,f5670])).

fof(f5670,plain,(
    r1_tarski(sK32,u1_struct_0(sK31)) ),
    inference(resolution,[],[f4423,f4730])).

fof(f4730,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f4270])).

fof(f4270,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f609])).

fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f5447,plain,(
    ! [X73] :
      ( ~ r1_tarski(sK32,X73)
      | r2_hidden(sK33,X73) ) ),
    inference(resolution,[],[f4426,f4736])).

fof(f4736,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4278])).

fof(f4278,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK86(X0,X1),X1)
          & r2_hidden(sK86(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK86])],[f4276,f4277])).

fof(f4277,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK86(X0,X1),X1)
        & r2_hidden(sK86(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f4276,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f4275])).

fof(f4275,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3863])).

fof(f3863,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f4426,plain,(
    r2_hidden(sK33,sK32) ),
    inference(cnf_transformation,[],[f4109])).

fof(f26440,plain,
    ( k1_tarski(sK33) != k3_xboole_0(sK32,sK56(sK32,sK31,k1_tarski(sK33)))
    | ~ m1_subset_1(k1_tarski(sK33),k1_zfmisc_1(u1_struct_0(sK31)))
    | ~ sP7(sK32,sK31) ),
    inference(resolution,[],[f6151,f5403])).

fof(f5403,plain,(
    r1_tarski(k1_tarski(sK33),sK32) ),
    inference(resolution,[],[f4426,f4467])).

fof(f4467,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f4142])).

fof(f4142,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f395])).

fof(f395,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).

fof(f6151,plain,(
    ! [X41,X40] :
      ( ~ r1_tarski(X41,X40)
      | k1_tarski(sK33) != k3_xboole_0(sK32,sK56(X40,sK31,X41))
      | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(sK31)))
      | ~ sP7(X40,sK31) ) ),
    inference(forward_demodulation,[],[f6150,f4690])).

fof(f4690,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f6150,plain,(
    ! [X41,X40] :
      ( k1_tarski(sK33) != k3_xboole_0(sK56(X40,sK31,X41),sK32)
      | ~ r1_tarski(X41,X40)
      | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(sK31)))
      | ~ sP7(X40,sK31) ) ),
    inference(subsumption_resolution,[],[f6108,f4541])).

fof(f4541,plain,(
    ! [X4,X0,X1] :
      ( m1_subset_1(sK56(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_tarski(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ sP7(X0,X1) ) ),
    inference(cnf_transformation,[],[f4189])).

fof(f4189,plain,(
    ! [X0,X1] :
      ( ( sP7(X0,X1)
        | ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X1),X0,X3) != sK55(X0,X1)
              | ~ v3_pre_topc(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & r1_tarski(sK55(X0,X1),X0)
          & m1_subset_1(sK55(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X4] :
            ( ( k9_subset_1(u1_struct_0(X1),X0,sK56(X0,X1,X4)) = X4
              & v3_pre_topc(sK56(X0,X1,X4),X1)
              & m1_subset_1(sK56(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r1_tarski(X4,X0)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP7(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK55,sK56])],[f4186,f4188,f4187])).

fof(f4187,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X1),X0,X3) != X2
              | ~ v3_pre_topc(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & r1_tarski(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X1),X0,X3) != sK55(X0,X1)
            | ~ v3_pre_topc(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        & r1_tarski(sK55(X0,X1),X0)
        & m1_subset_1(sK55(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f4188,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X1),X0,X5) = X4
          & v3_pre_topc(X5,X1)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X1),X0,sK56(X0,X1,X4)) = X4
        & v3_pre_topc(sK56(X0,X1,X4),X1)
        & m1_subset_1(sK56(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f4186,plain,(
    ! [X0,X1] :
      ( ( sP7(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X1),X0,X3) != X2
                | ~ v3_pre_topc(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & r1_tarski(X2,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X4] :
            ( ? [X5] :
                ( k9_subset_1(u1_struct_0(X1),X0,X5) = X4
                & v3_pre_topc(X5,X1)
                & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r1_tarski(X4,X0)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP7(X0,X1) ) ) ),
    inference(rectify,[],[f4185])).

fof(f4185,plain,(
    ! [X1,X0] :
      ( ( sP7(X1,X0)
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
        | ~ sP7(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f4067])).

fof(f6108,plain,(
    ! [X41,X40] :
      ( k1_tarski(sK33) != k3_xboole_0(sK56(X40,sK31,X41),sK32)
      | ~ m1_subset_1(sK56(X40,sK31,X41),k1_zfmisc_1(u1_struct_0(sK31)))
      | ~ r1_tarski(X41,X40)
      | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(sK31)))
      | ~ sP7(X40,sK31) ) ),
    inference(resolution,[],[f5793,f4542])).

fof(f4542,plain,(
    ! [X4,X0,X1] :
      ( v3_pre_topc(sK56(X0,X1,X4),X1)
      | ~ r1_tarski(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ sP7(X0,X1) ) ),
    inference(cnf_transformation,[],[f4189])).

fof(f5793,plain,(
    ! [X3] :
      ( ~ v3_pre_topc(X3,sK31)
      | k1_tarski(sK33) != k3_xboole_0(X3,sK32)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK31))) ) ),
    inference(backward_demodulation,[],[f4427,f5786])).

fof(f5786,plain,(
    ! [X174] : k9_subset_1(u1_struct_0(sK31),sK32,X174) = k3_xboole_0(X174,sK32) ),
    inference(backward_demodulation,[],[f5640,f5641])).

fof(f5641,plain,(
    ! [X175] : k3_xboole_0(X175,sK32) = k9_subset_1(u1_struct_0(sK31),X175,sK32) ),
    inference(resolution,[],[f4423,f4454])).

fof(f4454,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f3693])).

fof(f3693,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f496])).

fof(f496,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f5640,plain,(
    ! [X174] : k9_subset_1(u1_struct_0(sK31),X174,sK32) = k9_subset_1(u1_struct_0(sK31),sK32,X174) ),
    inference(resolution,[],[f4423,f4453])).

fof(f4453,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f3692])).

fof(f3692,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f454])).

fof(f454,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f4427,plain,(
    ! [X3] :
      ( k9_subset_1(u1_struct_0(sK31),sK32,X3) != k1_tarski(sK33)
      | ~ v3_pre_topc(X3,sK31)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK31))) ) ),
    inference(cnf_transformation,[],[f4109])).

fof(f97773,plain,(
    k1_tarski(sK33) = k3_xboole_0(sK32,sK56(sK32,sK31,k1_tarski(sK33))) ),
    inference(resolution,[],[f13748,f5403])).

fof(f13748,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,sK32)
      | k3_xboole_0(sK32,sK56(sK32,sK31,X1)) = X1 ) ),
    inference(forward_demodulation,[],[f13747,f4690])).

fof(f13747,plain,(
    ! [X1] :
      ( k3_xboole_0(sK56(sK32,sK31,X1),sK32) = X1
      | ~ r1_tarski(X1,sK32) ) ),
    inference(subsumption_resolution,[],[f13746,f11559])).

fof(f11559,plain,(
    ! [X11] :
      ( ~ r1_tarski(X11,sK32)
      | m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK31))) ) ),
    inference(superposition,[],[f5800,f4685])).

fof(f4685,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3833])).

fof(f3833,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f86])).

fof(f86,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f5800,plain,(
    ! [X176] : m1_subset_1(k3_xboole_0(X176,sK32),k1_zfmisc_1(u1_struct_0(sK31))) ),
    inference(forward_demodulation,[],[f5642,f5641])).

fof(f5642,plain,(
    ! [X176] : m1_subset_1(k9_subset_1(u1_struct_0(sK31),X176,sK32),k1_zfmisc_1(u1_struct_0(sK31))) ),
    inference(resolution,[],[f4423,f4455])).

fof(f4455,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f3694])).

fof(f3694,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f472])).

fof(f472,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f13746,plain,(
    ! [X1] :
      ( k3_xboole_0(sK56(sK32,sK31,X1),sK32) = X1
      | ~ r1_tarski(X1,sK32)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK31))) ) ),
    inference(subsumption_resolution,[],[f13707,f6491])).

fof(f13707,plain,(
    ! [X1] :
      ( k3_xboole_0(sK56(sK32,sK31,X1),sK32) = X1
      | ~ r1_tarski(X1,sK32)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK31)))
      | ~ sP7(sK32,sK31) ) ),
    inference(superposition,[],[f5786,f4543])).

fof(f4543,plain,(
    ! [X4,X0,X1] :
      ( k9_subset_1(u1_struct_0(X1),X0,sK56(X0,X1,X4)) = X4
      | ~ r1_tarski(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ sP7(X0,X1) ) ),
    inference(cnf_transformation,[],[f4189])).
%------------------------------------------------------------------------------
