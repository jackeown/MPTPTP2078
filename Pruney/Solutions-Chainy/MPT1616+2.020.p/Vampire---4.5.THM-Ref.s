%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:46 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 166 expanded)
%              Number of leaves         :   17 (  43 expanded)
%              Depth                    :   15
%              Number of atoms          :  301 ( 822 expanded)
%              Number of equality atoms :   26 (  83 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f177,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f144,f148,f176])).

fof(f176,plain,(
    ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f174,f85])).

fof(f85,plain,(
    ~ v1_xboole_0(u1_pre_topc(sK0)) ),
    inference(resolution,[],[f82,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f82,plain,(
    r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f81,f40])).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( u1_struct_0(sK0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( u1_struct_0(sK0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_yellow_1)).

fof(f81,plain,
    ( r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f46,f39])).

fof(f39,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK1(X0),sK2(X0)),u1_pre_topc(X0))
            & r2_hidden(sK2(X0),u1_pre_topc(X0))
            & r2_hidden(sK1(X0),u1_pre_topc(X0))
            & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
            & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) )
          | ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0))
            & r1_tarski(sK3(X0),u1_pre_topc(X0))
            & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(k9_subset_1(u1_struct_0(X0),X4,X5),u1_pre_topc(X0))
                    | ~ r2_hidden(X5,u1_pre_topc(X0))
                    | ~ r2_hidden(X4,u1_pre_topc(X0))
                    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            & ! [X6] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X6),u1_pre_topc(X0))
                | ~ r1_tarski(X6,u1_pre_topc(X0))
                | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f31,f34,f33,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
              & r2_hidden(X2,u1_pre_topc(X0))
              & r2_hidden(X1,u1_pre_topc(X0))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK1(X0),X2),u1_pre_topc(X0))
            & r2_hidden(X2,u1_pre_topc(X0))
            & r2_hidden(sK1(X0),u1_pre_topc(X0))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK1(X0),X2),u1_pre_topc(X0))
          & r2_hidden(X2,u1_pre_topc(X0))
          & r2_hidden(sK1(X0),u1_pre_topc(X0))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK1(X0),sK2(X0)),u1_pre_topc(X0))
        & r2_hidden(sK2(X0),u1_pre_topc(X0))
        & r2_hidden(sK1(X0),u1_pre_topc(X0))
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
          & r1_tarski(X3,u1_pre_topc(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0))
        & r1_tarski(sK3(X0),u1_pre_topc(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  & r2_hidden(X2,u1_pre_topc(X0))
                  & r2_hidden(X1,u1_pre_topc(X0))
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ? [X3] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              & r1_tarski(X3,u1_pre_topc(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(k9_subset_1(u1_struct_0(X0),X4,X5),u1_pre_topc(X0))
                    | ~ r2_hidden(X5,u1_pre_topc(X0))
                    | ~ r2_hidden(X4,u1_pre_topc(X0))
                    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            & ! [X6] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X6),u1_pre_topc(X0))
                | ~ r1_tarski(X6,u1_pre_topc(X0))
                | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  & r2_hidden(X2,u1_pre_topc(X0))
                  & r2_hidden(X1,u1_pre_topc(X0))
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ? [X3] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              & r1_tarski(X3,u1_pre_topc(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( ! [X1] :
                ( ! [X2] :
                    ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                    | ~ r2_hidden(X2,u1_pre_topc(X0))
                    | ~ r2_hidden(X1,u1_pre_topc(X0))
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
            & ! [X3] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
                | ~ r1_tarski(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  & r2_hidden(X2,u1_pre_topc(X0))
                  & r2_hidden(X1,u1_pre_topc(X0))
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ? [X3] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              & r1_tarski(X3,u1_pre_topc(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( ! [X1] :
                ( ! [X2] :
                    ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                    | ~ r2_hidden(X2,u1_pre_topc(X0))
                    | ~ r2_hidden(X1,u1_pre_topc(X0))
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
            & ! [X3] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
                | ~ r1_tarski(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X3,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    inference(rectify,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X1,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).

fof(f174,plain,
    ( v1_xboole_0(u1_pre_topc(sK0))
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f173,f41])).

fof(f41,plain,(
    u1_struct_0(sK0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f173,plain,
    ( u1_struct_0(sK0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))
    | v1_xboole_0(u1_pre_topc(sK0))
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f171,f82])).

fof(f171,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | u1_struct_0(sK0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))
    | v1_xboole_0(u1_pre_topc(sK0))
    | ~ spl4_4 ),
    inference(superposition,[],[f44,f143])).

fof(f143,plain,
    ( u1_struct_0(sK0) = k3_tarski(u1_pre_topc(sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl4_4
  <=> u1_struct_0(sK0) = k3_tarski(u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f44,plain,(
    ! [X0] :
      ( ~ r2_hidden(k3_tarski(X0),X0)
      | k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k3_tarski(X0),X0)
       => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_1)).

fof(f148,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f147])).

fof(f147,plain,
    ( $false
    | spl4_3 ),
    inference(subsumption_resolution,[],[f146,f139])).

fof(f139,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),k3_tarski(u1_pre_topc(sK0)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl4_3
  <=> r1_tarski(u1_struct_0(sK0),k3_tarski(u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f146,plain,(
    r1_tarski(u1_struct_0(sK0),k3_tarski(u1_pre_topc(sK0))) ),
    inference(resolution,[],[f129,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f129,plain,(
    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k3_tarski(u1_pre_topc(sK0)))) ),
    inference(resolution,[],[f120,f82])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(k3_tarski(X1))) ) ),
    inference(resolution,[],[f76,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f76,plain,(
    ! [X1] : m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(k3_tarski(X1)))) ),
    inference(resolution,[],[f70,f43])).

fof(f43,plain,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f144,plain,
    ( ~ spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f133,f141,f137])).

fof(f133,plain,
    ( u1_struct_0(sK0) = k3_tarski(u1_pre_topc(sK0))
    | ~ r1_tarski(u1_struct_0(sK0),k3_tarski(u1_pre_topc(sK0))) ),
    inference(resolution,[],[f114,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f114,plain,(
    r1_tarski(k3_tarski(u1_pre_topc(sK0)),u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f103,f42])).

fof(f42,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f103,plain,(
    r1_tarski(k3_tarski(u1_pre_topc(sK0)),k3_tarski(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f97,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(f97,plain,(
    r1_tarski(u1_pre_topc(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f80,f69])).

fof(f80,plain,(
    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f45,f40])).

fof(f45,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n006.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 09:49:07 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.44  % (22616)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.23/0.44  % (22616)Refutation found. Thanks to Tanya!
% 0.23/0.44  % SZS status Theorem for theBenchmark
% 0.23/0.45  % (22624)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.23/0.45  % SZS output start Proof for theBenchmark
% 0.23/0.45  fof(f177,plain,(
% 0.23/0.45    $false),
% 0.23/0.45    inference(avatar_sat_refutation,[],[f144,f148,f176])).
% 0.23/0.45  fof(f176,plain,(
% 0.23/0.45    ~spl4_4),
% 0.23/0.45    inference(avatar_contradiction_clause,[],[f175])).
% 0.23/0.45  fof(f175,plain,(
% 0.23/0.45    $false | ~spl4_4),
% 0.23/0.45    inference(subsumption_resolution,[],[f174,f85])).
% 0.23/0.45  fof(f85,plain,(
% 0.23/0.45    ~v1_xboole_0(u1_pre_topc(sK0))),
% 0.23/0.45    inference(resolution,[],[f82,f64])).
% 0.23/0.45  fof(f64,plain,(
% 0.23/0.45    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.23/0.45    inference(cnf_transformation,[],[f23])).
% 0.23/0.45  fof(f23,plain,(
% 0.23/0.45    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 0.23/0.45    inference(ennf_transformation,[],[f14])).
% 0.23/0.45  fof(f14,plain,(
% 0.23/0.45    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 0.23/0.45    inference(unused_predicate_definition_removal,[],[f1])).
% 0.23/0.45  fof(f1,axiom,(
% 0.23/0.45    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.23/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.23/0.45  fof(f82,plain,(
% 0.23/0.45    r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))),
% 0.23/0.45    inference(subsumption_resolution,[],[f81,f40])).
% 0.23/0.45  fof(f40,plain,(
% 0.23/0.45    l1_pre_topc(sK0)),
% 0.23/0.45    inference(cnf_transformation,[],[f28])).
% 0.23/0.45  fof(f28,plain,(
% 0.23/0.45    u1_struct_0(sK0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.23/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f27])).
% 0.23/0.45  fof(f27,plain,(
% 0.23/0.45    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (u1_struct_0(sK0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.23/0.45    introduced(choice_axiom,[])).
% 0.23/0.45  fof(f17,plain,(
% 0.23/0.45    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.23/0.45    inference(flattening,[],[f16])).
% 0.23/0.45  fof(f16,plain,(
% 0.23/0.45    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.23/0.45    inference(ennf_transformation,[],[f15])).
% 0.23/0.45  fof(f15,plain,(
% 0.23/0.45    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 0.23/0.45    inference(pure_predicate_removal,[],[f12])).
% 0.23/0.45  fof(f12,negated_conjecture,(
% 0.23/0.45    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 0.23/0.45    inference(negated_conjecture,[],[f11])).
% 0.23/0.45  fof(f11,conjecture,(
% 0.23/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 0.23/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_yellow_1)).
% 0.23/0.45  fof(f81,plain,(
% 0.23/0.45    r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~l1_pre_topc(sK0)),
% 0.23/0.45    inference(resolution,[],[f46,f39])).
% 0.23/0.45  fof(f39,plain,(
% 0.23/0.45    v2_pre_topc(sK0)),
% 0.23/0.45    inference(cnf_transformation,[],[f28])).
% 0.23/0.45  fof(f46,plain,(
% 0.23/0.45    ( ! [X0] : (~v2_pre_topc(X0) | r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~l1_pre_topc(X0)) )),
% 0.23/0.45    inference(cnf_transformation,[],[f35])).
% 0.23/0.45  fof(f35,plain,(
% 0.23/0.45    ! [X0] : (((v2_pre_topc(X0) | ((~r2_hidden(k9_subset_1(u1_struct_0(X0),sK1(X0),sK2(X0)),u1_pre_topc(X0)) & r2_hidden(sK2(X0),u1_pre_topc(X0)) & r2_hidden(sK1(X0),u1_pre_topc(X0)) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))) | (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0)) & r1_tarski(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((! [X4] : (! [X5] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X4,X5),u1_pre_topc(X0)) | ~r2_hidden(X5,u1_pre_topc(X0)) | ~r2_hidden(X4,u1_pre_topc(X0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X6] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X6),u1_pre_topc(X0)) | ~r1_tarski(X6,u1_pre_topc(X0)) | ~m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 0.23/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f31,f34,f33,f32])).
% 0.23/0.45  fof(f32,plain,(
% 0.23/0.45    ! [X0] : (? [X1] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),sK1(X0),X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(sK1(X0),u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.23/0.45    introduced(choice_axiom,[])).
% 0.23/0.45  fof(f33,plain,(
% 0.23/0.45    ! [X0] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),sK1(X0),X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(sK1(X0),u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~r2_hidden(k9_subset_1(u1_struct_0(X0),sK1(X0),sK2(X0)),u1_pre_topc(X0)) & r2_hidden(sK2(X0),u1_pre_topc(X0)) & r2_hidden(sK1(X0),u1_pre_topc(X0)) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.23/0.45    introduced(choice_axiom,[])).
% 0.23/0.45  fof(f34,plain,(
% 0.23/0.45    ! [X0] : (? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0)) & r1_tarski(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 0.23/0.45    introduced(choice_axiom,[])).
% 0.23/0.45  fof(f31,plain,(
% 0.23/0.45    ! [X0] : (((v2_pre_topc(X0) | ? [X1] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((! [X4] : (! [X5] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X4,X5),u1_pre_topc(X0)) | ~r2_hidden(X5,u1_pre_topc(X0)) | ~r2_hidden(X4,u1_pre_topc(X0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X6] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X6),u1_pre_topc(X0)) | ~r1_tarski(X6,u1_pre_topc(X0)) | ~m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 0.23/0.45    inference(rectify,[],[f30])).
% 0.23/0.45  fof(f30,plain,(
% 0.23/0.45    ! [X0] : (((v2_pre_topc(X0) | ? [X1] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 0.23/0.45    inference(flattening,[],[f29])).
% 0.23/0.45  fof(f29,plain,(
% 0.23/0.45    ! [X0] : (((v2_pre_topc(X0) | (? [X1] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 0.23/0.45    inference(nnf_transformation,[],[f22])).
% 0.23/0.45  fof(f22,plain,(
% 0.23/0.45    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.45    inference(flattening,[],[f21])).
% 0.23/0.45  fof(f21,plain,(
% 0.23/0.45    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.45    inference(ennf_transformation,[],[f13])).
% 0.23/0.45  fof(f13,plain,(
% 0.23/0.45    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.23/0.45    inference(rectify,[],[f8])).
% 0.23/0.45  fof(f8,axiom,(
% 0.23/0.45    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.23/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).
% 0.23/0.45  fof(f174,plain,(
% 0.23/0.45    v1_xboole_0(u1_pre_topc(sK0)) | ~spl4_4),
% 0.23/0.45    inference(subsumption_resolution,[],[f173,f41])).
% 0.23/0.45  fof(f41,plain,(
% 0.23/0.45    u1_struct_0(sK0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))),
% 0.23/0.45    inference(cnf_transformation,[],[f28])).
% 0.23/0.45  fof(f173,plain,(
% 0.23/0.45    u1_struct_0(sK0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) | v1_xboole_0(u1_pre_topc(sK0)) | ~spl4_4),
% 0.23/0.45    inference(subsumption_resolution,[],[f171,f82])).
% 0.23/0.45  fof(f171,plain,(
% 0.23/0.45    ~r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) | u1_struct_0(sK0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) | v1_xboole_0(u1_pre_topc(sK0)) | ~spl4_4),
% 0.23/0.45    inference(superposition,[],[f44,f143])).
% 0.23/0.45  fof(f143,plain,(
% 0.23/0.45    u1_struct_0(sK0) = k3_tarski(u1_pre_topc(sK0)) | ~spl4_4),
% 0.23/0.45    inference(avatar_component_clause,[],[f141])).
% 0.23/0.45  fof(f141,plain,(
% 0.23/0.45    spl4_4 <=> u1_struct_0(sK0) = k3_tarski(u1_pre_topc(sK0))),
% 0.23/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.23/0.45  fof(f44,plain,(
% 0.23/0.45    ( ! [X0] : (~r2_hidden(k3_tarski(X0),X0) | k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 0.23/0.45    inference(cnf_transformation,[],[f19])).
% 0.23/0.45  fof(f19,plain,(
% 0.23/0.45    ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0))),
% 0.23/0.45    inference(flattening,[],[f18])).
% 0.23/0.45  fof(f18,plain,(
% 0.23/0.45    ! [X0] : ((k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0)) | v1_xboole_0(X0))),
% 0.23/0.45    inference(ennf_transformation,[],[f10])).
% 0.23/0.45  fof(f10,axiom,(
% 0.23/0.45    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k3_tarski(X0),X0) => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))))),
% 0.23/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_1)).
% 0.23/0.45  fof(f148,plain,(
% 0.23/0.45    spl4_3),
% 0.23/0.45    inference(avatar_contradiction_clause,[],[f147])).
% 0.23/0.45  fof(f147,plain,(
% 0.23/0.45    $false | spl4_3),
% 0.23/0.45    inference(subsumption_resolution,[],[f146,f139])).
% 0.23/0.45  fof(f139,plain,(
% 0.23/0.45    ~r1_tarski(u1_struct_0(sK0),k3_tarski(u1_pre_topc(sK0))) | spl4_3),
% 0.23/0.45    inference(avatar_component_clause,[],[f137])).
% 0.23/0.45  fof(f137,plain,(
% 0.23/0.45    spl4_3 <=> r1_tarski(u1_struct_0(sK0),k3_tarski(u1_pre_topc(sK0)))),
% 0.23/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.23/0.45  fof(f146,plain,(
% 0.23/0.45    r1_tarski(u1_struct_0(sK0),k3_tarski(u1_pre_topc(sK0)))),
% 0.23/0.45    inference(resolution,[],[f129,f69])).
% 0.23/0.45  fof(f69,plain,(
% 0.23/0.45    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.23/0.45    inference(cnf_transformation,[],[f38])).
% 0.23/0.45  fof(f38,plain,(
% 0.23/0.45    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.23/0.45    inference(nnf_transformation,[],[f6])).
% 0.23/0.45  fof(f6,axiom,(
% 0.23/0.45    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.23/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.23/0.45  fof(f129,plain,(
% 0.23/0.45    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k3_tarski(u1_pre_topc(sK0))))),
% 0.23/0.45    inference(resolution,[],[f120,f82])).
% 0.23/0.45  fof(f120,plain,(
% 0.23/0.45    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(k3_tarski(X1)))) )),
% 0.23/0.45    inference(resolution,[],[f76,f71])).
% 0.23/0.45  fof(f71,plain,(
% 0.23/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.23/0.45    inference(cnf_transformation,[],[f26])).
% 0.23/0.45  fof(f26,plain,(
% 0.23/0.45    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.23/0.45    inference(flattening,[],[f25])).
% 0.23/0.45  fof(f25,plain,(
% 0.23/0.45    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.23/0.45    inference(ennf_transformation,[],[f7])).
% 0.23/0.45  fof(f7,axiom,(
% 0.23/0.45    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.23/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.23/0.45  fof(f76,plain,(
% 0.23/0.45    ( ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(k3_tarski(X1))))) )),
% 0.23/0.45    inference(resolution,[],[f70,f43])).
% 0.23/0.45  fof(f43,plain,(
% 0.23/0.45    ( ! [X0] : (r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))) )),
% 0.23/0.45    inference(cnf_transformation,[],[f3])).
% 0.23/0.45  fof(f3,axiom,(
% 0.23/0.45    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))),
% 0.23/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).
% 0.23/0.45  fof(f70,plain,(
% 0.23/0.45    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.23/0.45    inference(cnf_transformation,[],[f38])).
% 0.23/0.45  fof(f144,plain,(
% 0.23/0.45    ~spl4_3 | spl4_4),
% 0.23/0.45    inference(avatar_split_clause,[],[f133,f141,f137])).
% 0.23/0.45  fof(f133,plain,(
% 0.23/0.45    u1_struct_0(sK0) = k3_tarski(u1_pre_topc(sK0)) | ~r1_tarski(u1_struct_0(sK0),k3_tarski(u1_pre_topc(sK0)))),
% 0.23/0.45    inference(resolution,[],[f114,f68])).
% 0.23/0.45  fof(f68,plain,(
% 0.23/0.45    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.23/0.45    inference(cnf_transformation,[],[f37])).
% 0.23/0.45  fof(f37,plain,(
% 0.23/0.45    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.23/0.45    inference(flattening,[],[f36])).
% 0.23/0.45  fof(f36,plain,(
% 0.23/0.45    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.23/0.45    inference(nnf_transformation,[],[f2])).
% 0.23/0.45  fof(f2,axiom,(
% 0.23/0.45    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.23/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.23/0.45  fof(f114,plain,(
% 0.23/0.45    r1_tarski(k3_tarski(u1_pre_topc(sK0)),u1_struct_0(sK0))),
% 0.23/0.45    inference(forward_demodulation,[],[f103,f42])).
% 0.23/0.45  fof(f42,plain,(
% 0.23/0.45    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 0.23/0.45    inference(cnf_transformation,[],[f5])).
% 0.23/0.45  fof(f5,axiom,(
% 0.23/0.45    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.23/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 0.23/0.45  fof(f103,plain,(
% 0.23/0.45    r1_tarski(k3_tarski(u1_pre_topc(sK0)),k3_tarski(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.23/0.45    inference(resolution,[],[f97,f65])).
% 0.23/0.45  fof(f65,plain,(
% 0.23/0.45    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k3_tarski(X0),k3_tarski(X1))) )),
% 0.23/0.45    inference(cnf_transformation,[],[f24])).
% 0.23/0.45  fof(f24,plain,(
% 0.23/0.45    ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1))),
% 0.23/0.45    inference(ennf_transformation,[],[f4])).
% 0.23/0.45  fof(f4,axiom,(
% 0.23/0.45    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 0.23/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).
% 0.23/0.45  fof(f97,plain,(
% 0.23/0.45    r1_tarski(u1_pre_topc(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.23/0.45    inference(resolution,[],[f80,f69])).
% 0.23/0.45  fof(f80,plain,(
% 0.23/0.45    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.23/0.45    inference(resolution,[],[f45,f40])).
% 0.23/0.45  fof(f45,plain,(
% 0.23/0.45    ( ! [X0] : (~l1_pre_topc(X0) | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) )),
% 0.23/0.45    inference(cnf_transformation,[],[f20])).
% 0.23/0.45  fof(f20,plain,(
% 0.23/0.45    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.45    inference(ennf_transformation,[],[f9])).
% 0.23/0.45  fof(f9,axiom,(
% 0.23/0.45    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.23/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.23/0.45  % SZS output end Proof for theBenchmark
% 0.23/0.45  % (22616)------------------------------
% 0.23/0.45  % (22616)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.45  % (22616)Termination reason: Refutation
% 0.23/0.45  
% 0.23/0.45  % (22616)Memory used [KB]: 10618
% 0.23/0.45  % (22616)Time elapsed: 0.035 s
% 0.23/0.45  % (22616)------------------------------
% 0.23/0.45  % (22616)------------------------------
% 0.23/0.45  % (22605)Success in time 0.081 s
%------------------------------------------------------------------------------
