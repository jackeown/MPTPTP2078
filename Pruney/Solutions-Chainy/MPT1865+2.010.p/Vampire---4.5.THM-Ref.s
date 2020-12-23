%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:01 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 215 expanded)
%              Number of leaves         :   21 (  74 expanded)
%              Depth                    :   17
%              Number of atoms          :  382 (1201 expanded)
%              Number of equality atoms :   41 ( 160 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f277,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f90,f89,f273,f87])).

fof(f87,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | sP10(X1) ) ),
    inference(cnf_transformation,[],[f87_D])).

fof(f87_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
          | ~ v1_xboole_0(X2) )
    <=> ~ sP10(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP10])])).

fof(f273,plain,(
    v1_xboole_0(sK5) ),
    inference(resolution,[],[f272,f93])).

fof(f93,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f71,f89])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f272,plain,(
    v1_xboole_0(k1_zfmisc_1(sK5)) ),
    inference(subsumption_resolution,[],[f270,f52])).

fof(f52,plain,(
    r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ! [X3] :
        ( k9_subset_1(u1_struct_0(sK4),sK5,X3) != k1_tarski(sK6)
        | ~ v4_pre_topc(X3,sK4)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) )
    & r2_hidden(sK6,sK5)
    & m1_subset_1(sK6,u1_struct_0(sK4))
    & v2_tex_2(sK5,sK4)
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    & l1_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f14,f30,f29,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2)
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
                  ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK4),X1,X3)
                  | ~ v4_pre_topc(X3,sK4)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(sK4)) )
          & v2_tex_2(X1,sK4)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) )
      & l1_pre_topc(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ! [X3] :
                ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK4),X1,X3)
                | ~ v4_pre_topc(X3,sK4)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) )
            & r2_hidden(X2,X1)
            & m1_subset_1(X2,u1_struct_0(sK4)) )
        & v2_tex_2(X1,sK4)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) )
   => ( ? [X2] :
          ( ! [X3] :
              ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK4),sK5,X3)
              | ~ v4_pre_topc(X3,sK4)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) )
          & r2_hidden(X2,sK5)
          & m1_subset_1(X2,u1_struct_0(sK4)) )
      & v2_tex_2(sK5,sK4)
      & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X2] :
        ( ! [X3] :
            ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK4),sK5,X3)
            | ~ v4_pre_topc(X3,sK4)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) )
        & r2_hidden(X2,sK5)
        & m1_subset_1(X2,u1_struct_0(sK4)) )
   => ( ! [X3] :
          ( k9_subset_1(u1_struct_0(sK4),sK5,X3) != k1_tarski(sK6)
          | ~ v4_pre_topc(X3,sK4)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) )
      & r2_hidden(sK6,sK5)
      & m1_subset_1(sK6,u1_struct_0(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tex_2(X1,X0)
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ~ ( ! [X3] :
                          ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                         => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2)
                              & v4_pre_topc(X3,X0) ) )
                      & r2_hidden(X2,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2)
                            & v4_pre_topc(X3,X0) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tex_2)).

fof(f270,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK5))
    | ~ r2_hidden(sK6,sK5) ),
    inference(resolution,[],[f226,f259])).

fof(f259,plain,(
    ~ r1_tarski(k1_enumset1(sK6,sK6,sK6),sK5) ),
    inference(subsumption_resolution,[],[f258,f124])).

fof(f124,plain,(
    r2_hidden(sK6,u1_struct_0(sK4)) ),
    inference(subsumption_resolution,[],[f101,f114])).

fof(f114,plain,(
    ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(subsumption_resolution,[],[f110,f90])).

fof(f110,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | sP10(sK5) ),
    inference(resolution,[],[f87,f49])).

fof(f49,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f31])).

fof(f101,plain,
    ( r2_hidden(sK6,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(resolution,[],[f69,f51])).

fof(f51,plain,(
    m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f31])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f258,plain,
    ( ~ r1_tarski(k1_enumset1(sK6,sK6,sK6),sK5)
    | ~ r2_hidden(sK6,u1_struct_0(sK4)) ),
    inference(subsumption_resolution,[],[f257,f133])).

fof(f133,plain,(
    sP1(sK4,sK5) ),
    inference(subsumption_resolution,[],[f132,f50])).

fof(f50,plain,(
    v2_tex_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f31])).

fof(f132,plain,
    ( ~ v2_tex_2(sK5,sK4)
    | sP1(sK4,sK5) ),
    inference(resolution,[],[f130,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1)
      | ~ v2_tex_2(X0,X1)
      | sP1(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( v2_tex_2(X0,X1)
          | ~ sP1(X1,X0) )
        & ( sP1(X1,X0)
          | ~ v2_tex_2(X0,X1) ) )
      | ~ sP2(X0,X1) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ( ( v2_tex_2(X1,X0)
          | ~ sP1(X0,X1) )
        & ( sP1(X0,X1)
          | ~ v2_tex_2(X1,X0) ) )
      | ~ sP2(X1,X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ( v2_tex_2(X1,X0)
      <=> sP1(X0,X1) )
      | ~ sP2(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f130,plain,(
    sP2(sK5,sK4) ),
    inference(subsumption_resolution,[],[f127,f48])).

fof(f48,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f31])).

fof(f127,plain,
    ( sP2(sK5,sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(resolution,[],[f67,f49])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f16,f24,f23,f22])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( sP0(X2,X1,X0)
    <=> ? [X3] :
          ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
          & v4_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f23,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
    <=> ! [X2] :
          ( sP0(X2,X1,X0)
          | ~ r1_tarski(X2,X1)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f257,plain,
    ( ~ r1_tarski(k1_enumset1(sK6,sK6,sK6),sK5)
    | ~ sP1(sK4,sK5)
    | ~ r2_hidden(sK6,u1_struct_0(sK4)) ),
    inference(resolution,[],[f150,f183])).

fof(f183,plain,(
    ~ sP0(k1_enumset1(sK6,sK6,sK6),sK5,sK4) ),
    inference(equality_resolution,[],[f164])).

fof(f164,plain,(
    ! [X0] :
      ( k1_enumset1(sK6,sK6,sK6) != X0
      | ~ sP0(X0,sK5,sK4) ) ),
    inference(subsumption_resolution,[],[f163,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK8(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( k9_subset_1(u1_struct_0(X2),X1,X3) != X0
            | ~ v4_pre_topc(X3,X2)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) )
      & ( ( k9_subset_1(u1_struct_0(X2),X1,sK8(X0,X1,X2)) = X0
          & v4_pre_topc(sK8(X0,X1,X2),X2)
          & m1_subset_1(sK8(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f39,f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X2),X1,X4) = X0
          & v4_pre_topc(X4,X2)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( k9_subset_1(u1_struct_0(X2),X1,sK8(X0,X1,X2)) = X0
        & v4_pre_topc(sK8(X0,X1,X2),X2)
        & m1_subset_1(sK8(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( k9_subset_1(u1_struct_0(X2),X1,X3) != X0
            | ~ v4_pre_topc(X3,X2)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) )
      & ( ? [X4] :
            ( k9_subset_1(u1_struct_0(X2),X1,X4) = X0
            & v4_pre_topc(X4,X2)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ( sP0(X2,X1,X0)
        | ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
            | ~ v4_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ? [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
            & v4_pre_topc(X3,X0)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f163,plain,(
    ! [X0] :
      ( k1_enumset1(sK6,sK6,sK6) != X0
      | ~ m1_subset_1(sK8(X0,sK5,sK4),k1_zfmisc_1(u1_struct_0(sK4)))
      | ~ sP0(X0,sK5,sK4) ) ),
    inference(subsumption_resolution,[],[f162,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(sK8(X0,X1,X2),X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f162,plain,(
    ! [X0] :
      ( k1_enumset1(sK6,sK6,sK6) != X0
      | ~ v4_pre_topc(sK8(X0,sK5,sK4),sK4)
      | ~ m1_subset_1(sK8(X0,sK5,sK4),k1_zfmisc_1(u1_struct_0(sK4)))
      | ~ sP0(X0,sK5,sK4) ) ),
    inference(superposition,[],[f83,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(u1_struct_0(X2),X1,sK8(X0,X1,X2)) = X0
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f83,plain,(
    ! [X3] :
      ( k9_subset_1(u1_struct_0(sK4),sK5,X3) != k1_enumset1(sK6,sK6,sK6)
      | ~ v4_pre_topc(X3,sK4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) ) ),
    inference(definition_unfolding,[],[f53,f82])).

fof(f82,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f56,f68])).

fof(f68,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f56,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f53,plain,(
    ! [X3] :
      ( k9_subset_1(u1_struct_0(sK4),sK5,X3) != k1_tarski(sK6)
      | ~ v4_pre_topc(X3,sK4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f150,plain,(
    ! [X6,X7,X5] :
      ( sP0(k1_enumset1(X5,X5,X5),X6,X7)
      | ~ r1_tarski(k1_enumset1(X5,X5,X5),X6)
      | ~ sP1(X7,X6)
      | ~ r2_hidden(X5,u1_struct_0(X7)) ) ),
    inference(resolution,[],[f59,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f73,f82])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X3,X1)
      | sP0(X3,X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ( ~ sP0(sK7(X0,X1),X1,X0)
          & r1_tarski(sK7(X0,X1),X1)
          & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( sP0(X3,X1,X0)
            | ~ r1_tarski(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f35,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ sP0(X2,X1,X0)
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ sP0(sK7(X0,X1),X1,X0)
        & r1_tarski(sK7(X0,X1),X1)
        & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2] :
            ( ~ sP0(X2,X1,X0)
            & r1_tarski(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( sP0(X3,X1,X0)
            | ~ r1_tarski(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP1(X0,X1) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2] :
            ( ~ sP0(X2,X1,X0)
            & r1_tarski(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( sP0(X2,X1,X0)
            | ~ r1_tarski(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f226,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_enumset1(X0,X0,X0),X1)
      | v1_xboole_0(k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f136,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f75,f86])).

fof(f86,plain,(
    ! [X0] : sP3(X0,k1_zfmisc_1(X0)) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( sP3(X0,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ~ sP3(X0,X1) )
      & ( sP3(X0,X1)
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> sP3(X0,X1) ) ),
    inference(definition_folding,[],[f3,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( sP3(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( ~ sP3(X0,X1)
      | ~ r2_hidden(X3,X1)
      | r1_tarski(X3,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( sP3(X0,X1)
        | ( ( ~ r1_tarski(sK9(X0,X1),X0)
            | ~ r2_hidden(sK9(X0,X1),X1) )
          & ( r1_tarski(sK9(X0,X1),X0)
            | r2_hidden(sK9(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP3(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f44,f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK9(X0,X1),X0)
          | ~ r2_hidden(sK9(X0,X1),X1) )
        & ( r1_tarski(sK9(X0,X1),X0)
          | r2_hidden(sK9(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( sP3(X0,X1)
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
        | ~ sP3(X0,X1) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( sP3(X0,X1)
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
        | ~ sP3(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f136,plain,(
    ! [X4,X5] :
      ( r2_hidden(k1_enumset1(X4,X4,X4),k1_zfmisc_1(X5))
      | ~ r2_hidden(X4,X5)
      | v1_xboole_0(k1_zfmisc_1(X5)) ) ),
    inference(resolution,[],[f84,f69])).

fof(f89,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f55,f54])).

fof(f54,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f55,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f90,plain,(
    ~ sP10(sK5) ),
    inference(resolution,[],[f88,f52])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP10(X1) ) ),
    inference(general_splitting,[],[f81,f87_D])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n008.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 11:52:45 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.51  % (6148)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.23/0.52  % (6136)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.23/0.53  % (6146)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.53  % (6138)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.23/0.53  % (6135)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.23/0.53  % (6133)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.23/0.54  % (6153)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.23/0.54  % (6144)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.23/0.54  % (6155)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.23/0.54  % (6156)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.23/0.55  % (6142)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.23/0.55  % (6141)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.23/0.55  % (6150)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.23/0.55  % (6157)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.23/0.55  % (6156)Refutation not found, incomplete strategy% (6156)------------------------------
% 0.23/0.55  % (6156)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (6136)Refutation not found, incomplete strategy% (6136)------------------------------
% 0.23/0.55  % (6136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (6136)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.55  
% 0.23/0.55  % (6136)Memory used [KB]: 10746
% 0.23/0.55  % (6136)Time elapsed: 0.119 s
% 0.23/0.55  % (6136)------------------------------
% 0.23/0.55  % (6136)------------------------------
% 0.23/0.55  % (6156)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.55  
% 0.23/0.55  % (6156)Memory used [KB]: 1791
% 0.23/0.55  % (6156)Time elapsed: 0.117 s
% 0.23/0.55  % (6156)------------------------------
% 0.23/0.55  % (6156)------------------------------
% 0.23/0.55  % (6140)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.23/0.55  % (6158)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.23/0.55  % (6161)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.23/0.55  % (6147)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.23/0.55  % (6139)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.23/0.55  % (6145)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.23/0.55  % (6159)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.23/0.55  % (6137)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.23/0.55  % (6161)Refutation not found, incomplete strategy% (6161)------------------------------
% 0.23/0.55  % (6161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (6161)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.55  
% 0.23/0.55  % (6161)Memory used [KB]: 10746
% 0.23/0.55  % (6161)Time elapsed: 0.124 s
% 0.23/0.55  % (6161)------------------------------
% 0.23/0.55  % (6161)------------------------------
% 0.23/0.56  % (6164)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.23/0.56  % (6160)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.23/0.56  % (6163)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.23/0.56  % (6154)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.23/0.56  % (6164)Refutation found. Thanks to Tanya!
% 0.23/0.56  % SZS status Theorem for theBenchmark
% 0.23/0.56  % (6152)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.23/0.56  % (6143)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.23/0.56  % (6144)Refutation not found, incomplete strategy% (6144)------------------------------
% 0.23/0.56  % (6144)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (6151)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.23/0.56  % (6152)Refutation not found, incomplete strategy% (6152)------------------------------
% 0.23/0.56  % (6152)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (6162)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.23/0.56  % (6157)Refutation not found, incomplete strategy% (6157)------------------------------
% 0.23/0.56  % (6157)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (6157)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.56  
% 0.23/0.56  % (6157)Memory used [KB]: 10746
% 0.23/0.56  % (6157)Time elapsed: 0.068 s
% 0.23/0.56  % (6157)------------------------------
% 0.23/0.56  % (6157)------------------------------
% 0.23/0.56  % (6142)Refutation not found, incomplete strategy% (6142)------------------------------
% 0.23/0.56  % (6142)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (6142)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.56  
% 0.23/0.56  % (6142)Memory used [KB]: 10746
% 0.23/0.56  % (6142)Time elapsed: 0.133 s
% 0.23/0.56  % (6142)------------------------------
% 0.23/0.56  % (6142)------------------------------
% 0.23/0.56  % (6152)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.56  
% 0.23/0.56  % (6152)Memory used [KB]: 10746
% 0.23/0.56  % (6152)Time elapsed: 0.133 s
% 0.23/0.56  % (6152)------------------------------
% 0.23/0.56  % (6152)------------------------------
% 0.23/0.57  % (6144)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.57  
% 0.23/0.57  % (6144)Memory used [KB]: 10746
% 0.23/0.57  % (6144)Time elapsed: 0.135 s
% 0.23/0.57  % (6144)------------------------------
% 0.23/0.57  % (6144)------------------------------
% 0.23/0.58  % SZS output start Proof for theBenchmark
% 0.23/0.58  fof(f277,plain,(
% 0.23/0.58    $false),
% 0.23/0.58    inference(unit_resulting_resolution,[],[f90,f89,f273,f87])).
% 0.23/0.58  fof(f87,plain,(
% 0.23/0.58    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | sP10(X1)) )),
% 0.23/0.58    inference(cnf_transformation,[],[f87_D])).
% 0.23/0.58  fof(f87_D,plain,(
% 0.23/0.58    ( ! [X1] : (( ! [X2] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) ) <=> ~sP10(X1)) )),
% 0.23/0.58    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP10])])).
% 0.23/0.58  fof(f273,plain,(
% 0.23/0.58    v1_xboole_0(sK5)),
% 0.23/0.58    inference(resolution,[],[f272,f93])).
% 0.23/0.58  fof(f93,plain,(
% 0.23/0.58    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0)) | v1_xboole_0(X0)) )),
% 0.23/0.58    inference(resolution,[],[f71,f89])).
% 0.23/0.58  fof(f71,plain,(
% 0.23/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 0.23/0.58    inference(cnf_transformation,[],[f42])).
% 0.23/0.58  fof(f42,plain,(
% 0.23/0.58    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.23/0.58    inference(nnf_transformation,[],[f17])).
% 0.23/0.58  fof(f17,plain,(
% 0.23/0.58    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.23/0.58    inference(ennf_transformation,[],[f4])).
% 0.23/0.58  fof(f4,axiom,(
% 0.23/0.58    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.23/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.23/0.58  fof(f272,plain,(
% 0.23/0.58    v1_xboole_0(k1_zfmisc_1(sK5))),
% 0.23/0.58    inference(subsumption_resolution,[],[f270,f52])).
% 0.23/0.58  fof(f52,plain,(
% 0.23/0.58    r2_hidden(sK6,sK5)),
% 0.23/0.58    inference(cnf_transformation,[],[f31])).
% 0.23/0.58  fof(f31,plain,(
% 0.23/0.58    ((! [X3] : (k9_subset_1(u1_struct_0(sK4),sK5,X3) != k1_tarski(sK6) | ~v4_pre_topc(X3,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) & r2_hidden(sK6,sK5) & m1_subset_1(sK6,u1_struct_0(sK4))) & v2_tex_2(sK5,sK4) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))) & l1_pre_topc(sK4)),
% 0.23/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f14,f30,f29,f28])).
% 0.23/0.58  fof(f28,plain,(
% 0.23/0.58    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK4),X1,X3) | ~v4_pre_topc(X3,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK4))) & v2_tex_2(X1,sK4) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))) & l1_pre_topc(sK4))),
% 0.23/0.58    introduced(choice_axiom,[])).
% 0.23/0.58  fof(f29,plain,(
% 0.23/0.58    ? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK4),X1,X3) | ~v4_pre_topc(X3,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK4))) & v2_tex_2(X1,sK4) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))) => (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK4),sK5,X3) | ~v4_pre_topc(X3,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) & r2_hidden(X2,sK5) & m1_subset_1(X2,u1_struct_0(sK4))) & v2_tex_2(sK5,sK4) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))))),
% 0.23/0.58    introduced(choice_axiom,[])).
% 0.23/0.58  fof(f30,plain,(
% 0.23/0.58    ? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK4),sK5,X3) | ~v4_pre_topc(X3,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) & r2_hidden(X2,sK5) & m1_subset_1(X2,u1_struct_0(sK4))) => (! [X3] : (k9_subset_1(u1_struct_0(sK4),sK5,X3) != k1_tarski(sK6) | ~v4_pre_topc(X3,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) & r2_hidden(sK6,sK5) & m1_subset_1(sK6,u1_struct_0(sK4)))),
% 0.23/0.58    introduced(choice_axiom,[])).
% 0.23/0.58  fof(f14,plain,(
% 0.23/0.58    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.23/0.58    inference(flattening,[],[f13])).
% 0.23/0.58  fof(f13,plain,(
% 0.23/0.58    ? [X0] : (? [X1] : ((? [X2] : ((! [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v4_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.23/0.58    inference(ennf_transformation,[],[f12])).
% 0.23/0.58  fof(f12,negated_conjecture,(
% 0.23/0.58    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v4_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 0.23/0.58    inference(negated_conjecture,[],[f11])).
% 0.23/0.58  fof(f11,conjecture,(
% 0.23/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v4_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 0.23/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tex_2)).
% 0.23/0.58  fof(f270,plain,(
% 0.23/0.58    v1_xboole_0(k1_zfmisc_1(sK5)) | ~r2_hidden(sK6,sK5)),
% 0.23/0.58    inference(resolution,[],[f226,f259])).
% 0.23/0.58  fof(f259,plain,(
% 0.23/0.58    ~r1_tarski(k1_enumset1(sK6,sK6,sK6),sK5)),
% 0.23/0.58    inference(subsumption_resolution,[],[f258,f124])).
% 0.23/0.58  fof(f124,plain,(
% 0.23/0.58    r2_hidden(sK6,u1_struct_0(sK4))),
% 0.23/0.58    inference(subsumption_resolution,[],[f101,f114])).
% 0.23/0.58  fof(f114,plain,(
% 0.23/0.58    ~v1_xboole_0(u1_struct_0(sK4))),
% 0.23/0.58    inference(subsumption_resolution,[],[f110,f90])).
% 0.23/0.58  fof(f110,plain,(
% 0.23/0.58    ~v1_xboole_0(u1_struct_0(sK4)) | sP10(sK5)),
% 0.23/0.58    inference(resolution,[],[f87,f49])).
% 0.23/0.58  fof(f49,plain,(
% 0.23/0.58    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))),
% 0.23/0.58    inference(cnf_transformation,[],[f31])).
% 0.23/0.58  fof(f101,plain,(
% 0.23/0.58    r2_hidden(sK6,u1_struct_0(sK4)) | v1_xboole_0(u1_struct_0(sK4))),
% 0.23/0.58    inference(resolution,[],[f69,f51])).
% 0.23/0.58  fof(f51,plain,(
% 0.23/0.58    m1_subset_1(sK6,u1_struct_0(sK4))),
% 0.23/0.58    inference(cnf_transformation,[],[f31])).
% 0.23/0.58  fof(f69,plain,(
% 0.23/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.23/0.58    inference(cnf_transformation,[],[f42])).
% 0.23/0.58  fof(f258,plain,(
% 0.23/0.58    ~r1_tarski(k1_enumset1(sK6,sK6,sK6),sK5) | ~r2_hidden(sK6,u1_struct_0(sK4))),
% 0.23/0.58    inference(subsumption_resolution,[],[f257,f133])).
% 0.23/0.58  fof(f133,plain,(
% 0.23/0.58    sP1(sK4,sK5)),
% 0.23/0.58    inference(subsumption_resolution,[],[f132,f50])).
% 0.23/0.58  fof(f50,plain,(
% 0.23/0.58    v2_tex_2(sK5,sK4)),
% 0.23/0.58    inference(cnf_transformation,[],[f31])).
% 0.23/0.58  fof(f132,plain,(
% 0.23/0.58    ~v2_tex_2(sK5,sK4) | sP1(sK4,sK5)),
% 0.23/0.58    inference(resolution,[],[f130,f57])).
% 0.23/0.58  fof(f57,plain,(
% 0.23/0.58    ( ! [X0,X1] : (~sP2(X0,X1) | ~v2_tex_2(X0,X1) | sP1(X1,X0)) )),
% 0.23/0.58    inference(cnf_transformation,[],[f33])).
% 0.23/0.58  fof(f33,plain,(
% 0.23/0.58    ! [X0,X1] : (((v2_tex_2(X0,X1) | ~sP1(X1,X0)) & (sP1(X1,X0) | ~v2_tex_2(X0,X1))) | ~sP2(X0,X1))),
% 0.23/0.58    inference(rectify,[],[f32])).
% 0.23/0.58  fof(f32,plain,(
% 0.23/0.58    ! [X1,X0] : (((v2_tex_2(X1,X0) | ~sP1(X0,X1)) & (sP1(X0,X1) | ~v2_tex_2(X1,X0))) | ~sP2(X1,X0))),
% 0.23/0.58    inference(nnf_transformation,[],[f24])).
% 0.23/0.58  fof(f24,plain,(
% 0.23/0.58    ! [X1,X0] : ((v2_tex_2(X1,X0) <=> sP1(X0,X1)) | ~sP2(X1,X0))),
% 0.23/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.23/0.58  fof(f130,plain,(
% 0.23/0.58    sP2(sK5,sK4)),
% 0.23/0.58    inference(subsumption_resolution,[],[f127,f48])).
% 0.23/0.58  fof(f48,plain,(
% 0.23/0.58    l1_pre_topc(sK4)),
% 0.23/0.58    inference(cnf_transformation,[],[f31])).
% 0.23/0.58  fof(f127,plain,(
% 0.23/0.58    sP2(sK5,sK4) | ~l1_pre_topc(sK4)),
% 0.23/0.58    inference(resolution,[],[f67,f49])).
% 0.23/0.58  fof(f67,plain,(
% 0.23/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP2(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.23/0.58    inference(cnf_transformation,[],[f25])).
% 0.23/0.58  fof(f25,plain,(
% 0.23/0.58    ! [X0] : (! [X1] : (sP2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.58    inference(definition_folding,[],[f16,f24,f23,f22])).
% 0.23/0.58  fof(f22,plain,(
% 0.23/0.58    ! [X2,X1,X0] : (sP0(X2,X1,X0) <=> ? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.23/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.23/0.58  fof(f23,plain,(
% 0.23/0.58    ! [X0,X1] : (sP1(X0,X1) <=> ! [X2] : (sP0(X2,X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.23/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.23/0.58  fof(f16,plain,(
% 0.23/0.58    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.58    inference(flattening,[],[f15])).
% 0.23/0.58  fof(f15,plain,(
% 0.23/0.58    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.58    inference(ennf_transformation,[],[f10])).
% 0.23/0.58  fof(f10,axiom,(
% 0.23/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 0.23/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tex_2)).
% 0.23/0.58  fof(f257,plain,(
% 0.23/0.58    ~r1_tarski(k1_enumset1(sK6,sK6,sK6),sK5) | ~sP1(sK4,sK5) | ~r2_hidden(sK6,u1_struct_0(sK4))),
% 0.23/0.58    inference(resolution,[],[f150,f183])).
% 0.23/0.58  fof(f183,plain,(
% 0.23/0.58    ~sP0(k1_enumset1(sK6,sK6,sK6),sK5,sK4)),
% 0.23/0.58    inference(equality_resolution,[],[f164])).
% 0.23/0.58  fof(f164,plain,(
% 0.23/0.58    ( ! [X0] : (k1_enumset1(sK6,sK6,sK6) != X0 | ~sP0(X0,sK5,sK4)) )),
% 0.23/0.58    inference(subsumption_resolution,[],[f163,f63])).
% 0.23/0.58  fof(f63,plain,(
% 0.23/0.58    ( ! [X2,X0,X1] : (m1_subset_1(sK8(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) | ~sP0(X0,X1,X2)) )),
% 0.23/0.58    inference(cnf_transformation,[],[f41])).
% 0.23/0.58  fof(f41,plain,(
% 0.23/0.58    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (k9_subset_1(u1_struct_0(X2),X1,X3) != X0 | ~v4_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))) & ((k9_subset_1(u1_struct_0(X2),X1,sK8(X0,X1,X2)) = X0 & v4_pre_topc(sK8(X0,X1,X2),X2) & m1_subset_1(sK8(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))) | ~sP0(X0,X1,X2)))),
% 0.23/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f39,f40])).
% 0.23/0.58  fof(f40,plain,(
% 0.23/0.58    ! [X2,X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X2),X1,X4) = X0 & v4_pre_topc(X4,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))) => (k9_subset_1(u1_struct_0(X2),X1,sK8(X0,X1,X2)) = X0 & v4_pre_topc(sK8(X0,X1,X2),X2) & m1_subset_1(sK8(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))))),
% 0.23/0.58    introduced(choice_axiom,[])).
% 0.23/0.58  fof(f39,plain,(
% 0.23/0.58    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (k9_subset_1(u1_struct_0(X2),X1,X3) != X0 | ~v4_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))) & (? [X4] : (k9_subset_1(u1_struct_0(X2),X1,X4) = X0 & v4_pre_topc(X4,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))) | ~sP0(X0,X1,X2)))),
% 0.23/0.58    inference(rectify,[],[f38])).
% 0.23/0.58  fof(f38,plain,(
% 0.23/0.58    ! [X2,X1,X0] : ((sP0(X2,X1,X0) | ! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X2,X1,X0)))),
% 0.23/0.58    inference(nnf_transformation,[],[f22])).
% 0.23/0.58  fof(f163,plain,(
% 0.23/0.58    ( ! [X0] : (k1_enumset1(sK6,sK6,sK6) != X0 | ~m1_subset_1(sK8(X0,sK5,sK4),k1_zfmisc_1(u1_struct_0(sK4))) | ~sP0(X0,sK5,sK4)) )),
% 0.23/0.58    inference(subsumption_resolution,[],[f162,f64])).
% 0.23/0.58  fof(f64,plain,(
% 0.23/0.58    ( ! [X2,X0,X1] : (v4_pre_topc(sK8(X0,X1,X2),X2) | ~sP0(X0,X1,X2)) )),
% 0.23/0.58    inference(cnf_transformation,[],[f41])).
% 0.23/0.58  fof(f162,plain,(
% 0.23/0.58    ( ! [X0] : (k1_enumset1(sK6,sK6,sK6) != X0 | ~v4_pre_topc(sK8(X0,sK5,sK4),sK4) | ~m1_subset_1(sK8(X0,sK5,sK4),k1_zfmisc_1(u1_struct_0(sK4))) | ~sP0(X0,sK5,sK4)) )),
% 0.23/0.58    inference(superposition,[],[f83,f65])).
% 0.23/0.58  fof(f65,plain,(
% 0.23/0.58    ( ! [X2,X0,X1] : (k9_subset_1(u1_struct_0(X2),X1,sK8(X0,X1,X2)) = X0 | ~sP0(X0,X1,X2)) )),
% 0.23/0.58    inference(cnf_transformation,[],[f41])).
% 0.23/0.58  fof(f83,plain,(
% 0.23/0.58    ( ! [X3] : (k9_subset_1(u1_struct_0(sK4),sK5,X3) != k1_enumset1(sK6,sK6,sK6) | ~v4_pre_topc(X3,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) )),
% 0.23/0.58    inference(definition_unfolding,[],[f53,f82])).
% 0.23/0.58  fof(f82,plain,(
% 0.23/0.58    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.23/0.58    inference(definition_unfolding,[],[f56,f68])).
% 0.23/0.58  fof(f68,plain,(
% 0.23/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.23/0.58    inference(cnf_transformation,[],[f2])).
% 0.23/0.58  fof(f2,axiom,(
% 0.23/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.23/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.23/0.58  fof(f56,plain,(
% 0.23/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.23/0.58    inference(cnf_transformation,[],[f1])).
% 0.23/0.58  fof(f1,axiom,(
% 0.23/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.23/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.23/0.58  fof(f53,plain,(
% 0.23/0.58    ( ! [X3] : (k9_subset_1(u1_struct_0(sK4),sK5,X3) != k1_tarski(sK6) | ~v4_pre_topc(X3,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) )),
% 0.23/0.58    inference(cnf_transformation,[],[f31])).
% 0.23/0.58  fof(f150,plain,(
% 0.23/0.58    ( ! [X6,X7,X5] : (sP0(k1_enumset1(X5,X5,X5),X6,X7) | ~r1_tarski(k1_enumset1(X5,X5,X5),X6) | ~sP1(X7,X6) | ~r2_hidden(X5,u1_struct_0(X7))) )),
% 0.23/0.58    inference(resolution,[],[f59,f84])).
% 0.23/0.58  fof(f84,plain,(
% 0.23/0.58    ( ! [X0,X1] : (m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.23/0.58    inference(definition_unfolding,[],[f73,f82])).
% 0.23/0.58  fof(f73,plain,(
% 0.23/0.58    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.23/0.58    inference(cnf_transformation,[],[f18])).
% 0.23/0.58  fof(f18,plain,(
% 0.23/0.58    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.23/0.58    inference(ennf_transformation,[],[f7])).
% 0.23/0.58  fof(f7,axiom,(
% 0.23/0.58    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.23/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).
% 0.23/0.58  fof(f59,plain,(
% 0.23/0.58    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X3,X1) | sP0(X3,X1,X0) | ~sP1(X0,X1)) )),
% 0.23/0.58    inference(cnf_transformation,[],[f37])).
% 0.23/0.58  fof(f37,plain,(
% 0.23/0.58    ! [X0,X1] : ((sP1(X0,X1) | (~sP0(sK7(X0,X1),X1,X0) & r1_tarski(sK7(X0,X1),X1) & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (sP0(X3,X1,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP1(X0,X1)))),
% 0.23/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f35,f36])).
% 0.23/0.58  fof(f36,plain,(
% 0.23/0.58    ! [X1,X0] : (? [X2] : (~sP0(X2,X1,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~sP0(sK7(X0,X1),X1,X0) & r1_tarski(sK7(X0,X1),X1) & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.23/0.58    introduced(choice_axiom,[])).
% 0.23/0.58  fof(f35,plain,(
% 0.23/0.58    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : (~sP0(X2,X1,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (sP0(X3,X1,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP1(X0,X1)))),
% 0.23/0.58    inference(rectify,[],[f34])).
% 0.23/0.58  fof(f34,plain,(
% 0.23/0.58    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : (~sP0(X2,X1,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (sP0(X2,X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP1(X0,X1)))),
% 0.23/0.58    inference(nnf_transformation,[],[f23])).
% 0.23/0.58  fof(f226,plain,(
% 0.23/0.58    ( ! [X0,X1] : (r1_tarski(k1_enumset1(X0,X0,X0),X1) | v1_xboole_0(k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.23/0.58    inference(resolution,[],[f136,f117])).
% 0.23/0.58  fof(f117,plain,(
% 0.23/0.58    ( ! [X0,X1] : (~r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.23/0.58    inference(resolution,[],[f75,f86])).
% 0.23/0.58  fof(f86,plain,(
% 0.23/0.58    ( ! [X0] : (sP3(X0,k1_zfmisc_1(X0))) )),
% 0.23/0.58    inference(equality_resolution,[],[f79])).
% 0.23/0.58  fof(f79,plain,(
% 0.23/0.58    ( ! [X0,X1] : (sP3(X0,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.23/0.58    inference(cnf_transformation,[],[f47])).
% 0.23/0.58  fof(f47,plain,(
% 0.23/0.58    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ~sP3(X0,X1)) & (sP3(X0,X1) | k1_zfmisc_1(X0) != X1))),
% 0.23/0.58    inference(nnf_transformation,[],[f27])).
% 0.23/0.58  fof(f27,plain,(
% 0.23/0.58    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> sP3(X0,X1))),
% 0.23/0.58    inference(definition_folding,[],[f3,f26])).
% 0.23/0.58  fof(f26,plain,(
% 0.23/0.58    ! [X0,X1] : (sP3(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.23/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.23/0.58  fof(f3,axiom,(
% 0.23/0.58    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.23/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.23/0.58  fof(f75,plain,(
% 0.23/0.58    ( ! [X0,X3,X1] : (~sP3(X0,X1) | ~r2_hidden(X3,X1) | r1_tarski(X3,X0)) )),
% 0.23/0.58    inference(cnf_transformation,[],[f46])).
% 0.23/0.58  fof(f46,plain,(
% 0.23/0.58    ! [X0,X1] : ((sP3(X0,X1) | ((~r1_tarski(sK9(X0,X1),X0) | ~r2_hidden(sK9(X0,X1),X1)) & (r1_tarski(sK9(X0,X1),X0) | r2_hidden(sK9(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | ~sP3(X0,X1)))),
% 0.23/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f44,f45])).
% 0.23/0.58  fof(f45,plain,(
% 0.23/0.58    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK9(X0,X1),X0) | ~r2_hidden(sK9(X0,X1),X1)) & (r1_tarski(sK9(X0,X1),X0) | r2_hidden(sK9(X0,X1),X1))))),
% 0.23/0.58    introduced(choice_axiom,[])).
% 0.23/0.58  fof(f44,plain,(
% 0.23/0.58    ! [X0,X1] : ((sP3(X0,X1) | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | ~sP3(X0,X1)))),
% 0.23/0.58    inference(rectify,[],[f43])).
% 0.23/0.58  fof(f43,plain,(
% 0.23/0.58    ! [X0,X1] : ((sP3(X0,X1) | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | ~sP3(X0,X1)))),
% 0.23/0.58    inference(nnf_transformation,[],[f26])).
% 0.23/0.58  fof(f136,plain,(
% 0.23/0.58    ( ! [X4,X5] : (r2_hidden(k1_enumset1(X4,X4,X4),k1_zfmisc_1(X5)) | ~r2_hidden(X4,X5) | v1_xboole_0(k1_zfmisc_1(X5))) )),
% 0.23/0.58    inference(resolution,[],[f84,f69])).
% 0.23/0.58  fof(f89,plain,(
% 0.23/0.58    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.23/0.58    inference(forward_demodulation,[],[f55,f54])).
% 0.23/0.58  fof(f54,plain,(
% 0.23/0.58    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.23/0.58    inference(cnf_transformation,[],[f5])).
% 0.23/0.58  fof(f5,axiom,(
% 0.23/0.58    ! [X0] : k2_subset_1(X0) = X0),
% 0.23/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.23/0.58  fof(f55,plain,(
% 0.23/0.58    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.23/0.58    inference(cnf_transformation,[],[f6])).
% 0.23/0.58  fof(f6,axiom,(
% 0.23/0.58    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.23/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.23/0.58  fof(f90,plain,(
% 0.23/0.58    ~sP10(sK5)),
% 0.23/0.58    inference(resolution,[],[f88,f52])).
% 0.23/0.58  fof(f88,plain,(
% 0.23/0.58    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~sP10(X1)) )),
% 0.23/0.58    inference(general_splitting,[],[f81,f87_D])).
% 0.23/0.58  fof(f81,plain,(
% 0.23/0.58    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.23/0.58    inference(cnf_transformation,[],[f21])).
% 0.23/0.58  fof(f21,plain,(
% 0.23/0.58    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.23/0.58    inference(ennf_transformation,[],[f9])).
% 0.23/0.58  fof(f9,axiom,(
% 0.23/0.58    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.23/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.23/0.58  % SZS output end Proof for theBenchmark
% 0.23/0.58  % (6164)------------------------------
% 0.23/0.58  % (6164)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.58  % (6164)Termination reason: Refutation
% 0.23/0.58  
% 0.23/0.58  % (6164)Memory used [KB]: 1918
% 0.23/0.58  % (6164)Time elapsed: 0.139 s
% 0.23/0.58  % (6164)------------------------------
% 0.23/0.58  % (6164)------------------------------
% 0.23/0.58  % (6131)Success in time 0.196 s
%------------------------------------------------------------------------------
