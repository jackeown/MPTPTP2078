%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1865+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:35 EST 2020

% Result     : Theorem 46.72s
% Output     : Refutation 46.72s
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
fof(f97203,plain,(
    $false ),
    inference(subsumption_resolution,[],[f97163,f26947])).

fof(f26947,plain,(
    k1_tarski(sK33) != k3_xboole_0(sK32,sK61(sK32,sK31,k1_tarski(sK33))) ),
    inference(subsumption_resolution,[],[f26946,f6505])).

fof(f6505,plain,(
    sP9(sK32,sK31) ),
    inference(subsumption_resolution,[],[f6503,f4429])).

fof(f4429,plain,(
    v2_tex_2(sK32,sK31) ),
    inference(cnf_transformation,[],[f4112])).

fof(f4112,plain,
    ( ! [X3] :
        ( k9_subset_1(u1_struct_0(sK31),sK32,X3) != k1_tarski(sK33)
        | ~ v4_pre_topc(X3,sK31)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK31))) )
    & r2_hidden(sK33,sK32)
    & m1_subset_1(sK33,u1_struct_0(sK31))
    & v2_tex_2(sK32,sK31)
    & m1_subset_1(sK32,k1_zfmisc_1(u1_struct_0(sK31)))
    & l1_pre_topc(sK31) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK31,sK32,sK33])],[f3686,f4111,f4110,f4109])).

fof(f4109,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3)
                    | ~ v4_pre_topc(X3,X0)
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
                  | ~ v4_pre_topc(X3,sK31)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK31))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(sK31)) )
          & v2_tex_2(X1,sK31)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK31))) )
      & l1_pre_topc(sK31) ) ),
    introduced(choice_axiom,[])).

fof(f4110,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ! [X3] :
                ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK31),X1,X3)
                | ~ v4_pre_topc(X3,sK31)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK31))) )
            & r2_hidden(X2,X1)
            & m1_subset_1(X2,u1_struct_0(sK31)) )
        & v2_tex_2(X1,sK31)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK31))) )
   => ( ? [X2] :
          ( ! [X3] :
              ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK31),sK32,X3)
              | ~ v4_pre_topc(X3,sK31)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK31))) )
          & r2_hidden(X2,sK32)
          & m1_subset_1(X2,u1_struct_0(sK31)) )
      & v2_tex_2(sK32,sK31)
      & m1_subset_1(sK32,k1_zfmisc_1(u1_struct_0(sK31))) ) ),
    introduced(choice_axiom,[])).

fof(f4111,plain,
    ( ? [X2] :
        ( ! [X3] :
            ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK31),sK32,X3)
            | ~ v4_pre_topc(X3,sK31)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK31))) )
        & r2_hidden(X2,sK32)
        & m1_subset_1(X2,u1_struct_0(sK31)) )
   => ( ! [X3] :
          ( k9_subset_1(u1_struct_0(sK31),sK32,X3) != k1_tarski(sK33)
          | ~ v4_pre_topc(X3,sK31)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK31))) )
      & r2_hidden(sK33,sK32)
      & m1_subset_1(sK33,u1_struct_0(sK31)) ) ),
    introduced(choice_axiom,[])).

fof(f3686,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f3685])).

fof(f3685,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3669])).

fof(f3669,negated_conjecture,(
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
                              & v4_pre_topc(X3,X0) ) )
                      & r2_hidden(X2,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3668])).

fof(f3668,conjecture,(
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
                            & v4_pre_topc(X3,X0) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tex_2)).

fof(f6503,plain,
    ( sP9(sK32,sK31)
    | ~ v2_tex_2(sK32,sK31) ),
    inference(resolution,[],[f5764,f4563])).

fof(f4563,plain,(
    ! [X0,X1] :
      ( sP9(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ sP10(X0,X1) ) ),
    inference(cnf_transformation,[],[f4199])).

fof(f4199,plain,(
    ! [X0,X1] :
      ( ( ( v2_tex_2(X1,X0)
          | ~ sP9(X1,X0) )
        & ( sP9(X1,X0)
          | ~ v2_tex_2(X1,X0) ) )
      | ~ sP10(X0,X1) ) ),
    inference(nnf_transformation,[],[f4075])).

fof(f4075,plain,(
    ! [X0,X1] :
      ( ( v2_tex_2(X1,X0)
      <=> sP9(X1,X0) )
      | ~ sP10(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP10])])).

fof(f5764,plain,(
    sP10(sK31,sK32) ),
    inference(subsumption_resolution,[],[f5600,f4427])).

fof(f4427,plain,(
    l1_pre_topc(sK31) ),
    inference(cnf_transformation,[],[f4112])).

fof(f5600,plain,
    ( sP10(sK31,sK32)
    | ~ l1_pre_topc(sK31) ),
    inference(resolution,[],[f4428,f4571])).

fof(f4571,plain,(
    ! [X0,X1] :
      ( sP10(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f4076])).

fof(f4076,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP10(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f3759,f4075,f4074])).

fof(f4074,plain,(
    ! [X1,X0] :
      ( sP9(X1,X0)
    <=> ! [X2] :
          ( ? [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
              & v4_pre_topc(X3,X0)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ r1_tarski(X2,X1)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP9])])).

fof(f3759,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f3758])).

fof(f3758,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3606])).

fof(f3606,axiom,(
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
                            & v4_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tex_2)).

fof(f4428,plain,(
    m1_subset_1(sK32,k1_zfmisc_1(u1_struct_0(sK31))) ),
    inference(cnf_transformation,[],[f4112])).

fof(f26946,plain,
    ( k1_tarski(sK33) != k3_xboole_0(sK32,sK61(sK32,sK31,k1_tarski(sK33)))
    | ~ sP9(sK32,sK31) ),
    inference(subsumption_resolution,[],[f26901,f9785])).

fof(f9785,plain,(
    m1_subset_1(k1_tarski(sK33),k1_zfmisc_1(u1_struct_0(sK31))) ),
    inference(resolution,[],[f9752,f4488])).

fof(f4488,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f3707])).

fof(f3707,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f535])).

fof(f535,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(f9752,plain,(
    r2_hidden(sK33,u1_struct_0(sK31)) ),
    inference(resolution,[],[f5476,f5705])).

fof(f5705,plain,(
    r1_tarski(sK32,u1_struct_0(sK31)) ),
    inference(resolution,[],[f4428,f4770])).

fof(f4770,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f4296])).

fof(f4296,plain,(
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

fof(f5476,plain,(
    ! [X82] :
      ( ~ r1_tarski(sK32,X82)
      | r2_hidden(sK33,X82) ) ),
    inference(resolution,[],[f4431,f4776])).

fof(f4776,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4304])).

fof(f4304,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK94(X0,X1),X1)
          & r2_hidden(sK94(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK94])],[f4302,f4303])).

fof(f4303,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK94(X0,X1),X1)
        & r2_hidden(sK94(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f4302,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f4301])).

fof(f4301,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3888])).

fof(f3888,plain,(
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

fof(f4431,plain,(
    r2_hidden(sK33,sK32) ),
    inference(cnf_transformation,[],[f4112])).

fof(f26901,plain,
    ( k1_tarski(sK33) != k3_xboole_0(sK32,sK61(sK32,sK31,k1_tarski(sK33)))
    | ~ m1_subset_1(k1_tarski(sK33),k1_zfmisc_1(u1_struct_0(sK31)))
    | ~ sP9(sK32,sK31) ),
    inference(resolution,[],[f6168,f5426])).

fof(f5426,plain,(
    r1_tarski(k1_tarski(sK33),sK32) ),
    inference(resolution,[],[f4431,f4472])).

fof(f4472,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f4145])).

fof(f4145,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f302])).

fof(f302,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f6168,plain,(
    ! [X14,X13] :
      ( ~ r1_tarski(X14,X13)
      | k1_tarski(sK33) != k3_xboole_0(sK32,sK61(X13,sK31,X14))
      | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK31)))
      | ~ sP9(X13,sK31) ) ),
    inference(forward_demodulation,[],[f6167,f4730])).

fof(f4730,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f6167,plain,(
    ! [X14,X13] :
      ( k1_tarski(sK33) != k3_xboole_0(sK61(X13,sK31,X14),sK32)
      | ~ r1_tarski(X14,X13)
      | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK31)))
      | ~ sP9(X13,sK31) ) ),
    inference(subsumption_resolution,[],[f6137,f4565])).

fof(f4565,plain,(
    ! [X4,X0,X1] :
      ( m1_subset_1(sK61(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_tarski(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ sP9(X0,X1) ) ),
    inference(cnf_transformation,[],[f4204])).

fof(f4204,plain,(
    ! [X0,X1] :
      ( ( sP9(X0,X1)
        | ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X1),X0,X3) != sK60(X0,X1)
              | ~ v4_pre_topc(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & r1_tarski(sK60(X0,X1),X0)
          & m1_subset_1(sK60(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X4] :
            ( ( k9_subset_1(u1_struct_0(X1),X0,sK61(X0,X1,X4)) = X4
              & v4_pre_topc(sK61(X0,X1,X4),X1)
              & m1_subset_1(sK61(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r1_tarski(X4,X0)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP9(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK60,sK61])],[f4201,f4203,f4202])).

fof(f4202,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X1),X0,X3) != X2
              | ~ v4_pre_topc(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & r1_tarski(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X1),X0,X3) != sK60(X0,X1)
            | ~ v4_pre_topc(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        & r1_tarski(sK60(X0,X1),X0)
        & m1_subset_1(sK60(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f4203,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X1),X0,X5) = X4
          & v4_pre_topc(X5,X1)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X1),X0,sK61(X0,X1,X4)) = X4
        & v4_pre_topc(sK61(X0,X1,X4),X1)
        & m1_subset_1(sK61(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f4201,plain,(
    ! [X0,X1] :
      ( ( sP9(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X1),X0,X3) != X2
                | ~ v4_pre_topc(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & r1_tarski(X2,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X4] :
            ( ? [X5] :
                ( k9_subset_1(u1_struct_0(X1),X0,X5) = X4
                & v4_pre_topc(X5,X1)
                & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r1_tarski(X4,X0)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP9(X0,X1) ) ) ),
    inference(rectify,[],[f4200])).

fof(f4200,plain,(
    ! [X1,X0] :
      ( ( sP9(X1,X0)
        | ? [X2] :
            ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                | ~ v4_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & r1_tarski(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( ? [X3] :
                ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                & v4_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r1_tarski(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP9(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f4074])).

fof(f6137,plain,(
    ! [X14,X13] :
      ( k1_tarski(sK33) != k3_xboole_0(sK61(X13,sK31,X14),sK32)
      | ~ m1_subset_1(sK61(X13,sK31,X14),k1_zfmisc_1(u1_struct_0(sK31)))
      | ~ r1_tarski(X14,X13)
      | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK31)))
      | ~ sP9(X13,sK31) ) ),
    inference(resolution,[],[f5828,f4566])).

fof(f4566,plain,(
    ! [X4,X0,X1] :
      ( v4_pre_topc(sK61(X0,X1,X4),X1)
      | ~ r1_tarski(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ sP9(X0,X1) ) ),
    inference(cnf_transformation,[],[f4204])).

fof(f5828,plain,(
    ! [X3] :
      ( ~ v4_pre_topc(X3,sK31)
      | k1_tarski(sK33) != k3_xboole_0(X3,sK32)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK31))) ) ),
    inference(backward_demodulation,[],[f4432,f5821])).

fof(f5821,plain,(
    ! [X177] : k9_subset_1(u1_struct_0(sK31),sK32,X177) = k3_xboole_0(X177,sK32) ),
    inference(backward_demodulation,[],[f5675,f5676])).

fof(f5676,plain,(
    ! [X178] : k3_xboole_0(X178,sK32) = k9_subset_1(u1_struct_0(sK31),X178,sK32) ),
    inference(resolution,[],[f4428,f4459])).

fof(f4459,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f3694])).

fof(f3694,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f496])).

fof(f496,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f5675,plain,(
    ! [X177] : k9_subset_1(u1_struct_0(sK31),X177,sK32) = k9_subset_1(u1_struct_0(sK31),sK32,X177) ),
    inference(resolution,[],[f4428,f4458])).

fof(f4458,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f3693])).

fof(f3693,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f454])).

fof(f454,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f4432,plain,(
    ! [X3] :
      ( k9_subset_1(u1_struct_0(sK31),sK32,X3) != k1_tarski(sK33)
      | ~ v4_pre_topc(X3,sK31)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK31))) ) ),
    inference(cnf_transformation,[],[f4112])).

fof(f97163,plain,(
    k1_tarski(sK33) = k3_xboole_0(sK32,sK61(sK32,sK31,k1_tarski(sK33))) ),
    inference(resolution,[],[f13816,f5426])).

fof(f13816,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,sK32)
      | k3_xboole_0(sK32,sK61(sK32,sK31,X2)) = X2 ) ),
    inference(forward_demodulation,[],[f13815,f4730])).

fof(f13815,plain,(
    ! [X2] :
      ( k3_xboole_0(sK61(sK32,sK31,X2),sK32) = X2
      | ~ r1_tarski(X2,sK32) ) ),
    inference(subsumption_resolution,[],[f13814,f11610])).

fof(f11610,plain,(
    ! [X11] :
      ( ~ r1_tarski(X11,sK32)
      | m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK31))) ) ),
    inference(superposition,[],[f5837,f4725])).

fof(f4725,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3858])).

fof(f3858,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f86])).

fof(f86,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f5837,plain,(
    ! [X179] : m1_subset_1(k3_xboole_0(X179,sK32),k1_zfmisc_1(u1_struct_0(sK31))) ),
    inference(forward_demodulation,[],[f5677,f5676])).

fof(f5677,plain,(
    ! [X179] : m1_subset_1(k9_subset_1(u1_struct_0(sK31),X179,sK32),k1_zfmisc_1(u1_struct_0(sK31))) ),
    inference(resolution,[],[f4428,f4460])).

fof(f4460,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f3695])).

fof(f3695,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f472])).

fof(f472,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f13814,plain,(
    ! [X2] :
      ( k3_xboole_0(sK61(sK32,sK31,X2),sK32) = X2
      | ~ r1_tarski(X2,sK32)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK31))) ) ),
    inference(subsumption_resolution,[],[f13771,f6505])).

fof(f13771,plain,(
    ! [X2] :
      ( k3_xboole_0(sK61(sK32,sK31,X2),sK32) = X2
      | ~ r1_tarski(X2,sK32)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK31)))
      | ~ sP9(sK32,sK31) ) ),
    inference(superposition,[],[f5821,f4567])).

fof(f4567,plain,(
    ! [X4,X0,X1] :
      ( k9_subset_1(u1_struct_0(X1),X0,sK61(X0,X1,X4)) = X4
      | ~ r1_tarski(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ sP9(X0,X1) ) ),
    inference(cnf_transformation,[],[f4204])).
%------------------------------------------------------------------------------
