%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 542 expanded)
%              Number of leaves         :   26 ( 175 expanded)
%              Depth                    :   19
%              Number of atoms          :  502 (3062 expanded)
%              Number of equality atoms :   27 ( 132 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f194,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f100,f105,f123,f124,f154,f158,f179,f193])).

fof(f193,plain,
    ( spl3_2
    | spl3_6
    | ~ spl3_7 ),
    inference(avatar_contradiction_clause,[],[f192])).

fof(f192,plain,
    ( $false
    | spl3_2
    | spl3_6
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f191,f121])).

fof(f121,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl3_6
  <=> m1_connsp_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f191,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | spl3_2
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f190,f52])).

fof(f52,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ( ~ m1_connsp_2(sK2,sK0,sK1)
      | ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
    & ( m1_connsp_2(sK2,sK0,sK1)
      | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f38,f41,f40,f39])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_connsp_2(X2,X0,X1)
                  | ~ m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
                & ( m1_connsp_2(X2,X0,X1)
                  | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_connsp_2(X2,sK0,X1)
                | ~ m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1)) )
              & ( m1_connsp_2(X2,sK0,X1)
                | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ m1_connsp_2(X2,sK0,X1)
              | ~ m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1)) )
            & ( m1_connsp_2(X2,sK0,X1)
              | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1)) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ( ~ m1_connsp_2(X2,sK0,sK1)
            | ~ m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
          & ( m1_connsp_2(X2,sK0,sK1)
            | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X2] :
        ( ( ~ m1_connsp_2(X2,sK0,sK1)
          | ~ m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
        & ( m1_connsp_2(X2,sK0,sK1)
          | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ m1_connsp_2(sK2,sK0,sK1)
        | ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
      & ( m1_connsp_2(sK2,sK0,sK1)
        | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_connsp_2(X2,X0,X1)
                | ~ m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
              & ( m1_connsp_2(X2,X0,X1)
                | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_connsp_2(X2,X0,X1)
                | ~ m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
              & ( m1_connsp_2(X2,X0,X1)
                | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
              <~> m1_connsp_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
              <~> m1_connsp_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
                <=> m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
              <=> m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_connsp_2)).

fof(f190,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_connsp_2(sK2,sK0,sK1)
    | spl3_2
    | ~ spl3_7 ),
    inference(resolution,[],[f189,f182])).

fof(f182,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | spl3_2
    | ~ spl3_7 ),
    inference(resolution,[],[f149,f135])).

fof(f135,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k6_domain_1(u1_struct_0(sK0),sK1),X1)
        | r2_hidden(sK1,X1) )
    | spl3_2 ),
    inference(superposition,[],[f86,f133])).

fof(f133,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | spl3_2 ),
    inference(subsumption_resolution,[],[f130,f98])).

fof(f98,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl3_2
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f130,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f83,f51])).

fof(f51,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f42])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f64,f82])).

fof(f82,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f55,f81])).

fof(f81,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f62,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f69,f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f73,f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f74,f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f75,f76])).

fof(f76,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f73,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f69,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f62,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f55,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f64,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f70,f81])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f149,plain,
    ( r1_tarski(k6_domain_1(u1_struct_0(sK0),sK1),k1_tops_1(sK0,sK2))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl3_7
  <=> r1_tarski(k6_domain_1(u1_struct_0(sK0),sK1),k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f189,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1,k1_tops_1(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_connsp_2(X0,sK0,sK1) ) ),
    inference(resolution,[],[f188,f51])).

fof(f188,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,k1_tops_1(sK0,X1))
      | m1_connsp_2(X1,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f187,f48])).

fof(f48,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f187,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_tops_1(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | m1_connsp_2(X1,sK0,X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f186,f50])).

fof(f50,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f186,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_tops_1(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | m1_connsp_2(X1,sK0,X0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f59,f49])).

fof(f49,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | m1_connsp_2(X2,X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
                & ( r2_hidden(X1,k1_tops_1(X0,X2))
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

fof(f179,plain,
    ( spl3_2
    | spl3_5
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(avatar_contradiction_clause,[],[f178])).

fof(f178,plain,
    ( $false
    | spl3_2
    | spl3_5
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f177,f52])).

fof(f177,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_2
    | spl3_5
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f176,f117])).

fof(f117,plain,
    ( ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl3_5
  <=> m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f176,plain,
    ( m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_2
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(resolution,[],[f175,f169])).

fof(f169,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK1,k1_tops_1(sK0,X3))
        | m2_connsp_2(X3,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl3_2
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f168,f152])).

fof(f152,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl3_8
  <=> m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f168,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | m2_connsp_2(X3,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
        | ~ r2_hidden(sK1,k1_tops_1(sK0,X3)) )
    | spl3_2 ),
    inference(resolution,[],[f166,f137])).

fof(f137,plain,
    ( ! [X0] :
        ( r1_tarski(k6_domain_1(u1_struct_0(sK0),sK1),X0)
        | ~ r2_hidden(sK1,X0) )
    | spl3_2 ),
    inference(duplicate_literal_removal,[],[f134])).

fof(f134,plain,
    ( ! [X0] :
        ( r1_tarski(k6_domain_1(u1_struct_0(sK0),sK1),X0)
        | ~ r2_hidden(sK1,X0)
        | ~ r2_hidden(sK1,X0) )
    | spl3_2 ),
    inference(superposition,[],[f84,f133])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f72,f81])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f166,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tops_1(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m2_connsp_2(X1,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f165,f50])).

fof(f165,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tops_1(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | m2_connsp_2(X1,sK0,X0) ) ),
    inference(resolution,[],[f61,f49])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m2_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_connsp_2(X2,X0,X1)
                  | ~ r1_tarski(X1,k1_tops_1(X0,X2)) )
                & ( r1_tarski(X1,k1_tops_1(X0,X2))
                  | ~ m2_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_connsp_2)).

fof(f175,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f174,f52])).

fof(f174,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ spl3_6 ),
    inference(resolution,[],[f173,f122])).

fof(f122,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f120])).

fof(f173,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK1,k1_tops_1(sK0,X0)) ) ),
    inference(resolution,[],[f172,f51])).

fof(f172,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_connsp_2(X0,sK0,X1)
      | r2_hidden(X1,k1_tops_1(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f171,f48])).

fof(f171,plain,(
    ! [X0,X1] :
      ( ~ m1_connsp_2(X0,sK0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(X1,k1_tops_1(sK0,X0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f170,f50])).

fof(f170,plain,(
    ! [X0,X1] :
      ( ~ m1_connsp_2(X0,sK0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | r2_hidden(X1,k1_tops_1(sK0,X0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f58,f49])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f158,plain,
    ( ~ spl3_1
    | spl3_2
    | spl3_8 ),
    inference(avatar_contradiction_clause,[],[f157])).

fof(f157,plain,
    ( $false
    | ~ spl3_1
    | spl3_2
    | spl3_8 ),
    inference(subsumption_resolution,[],[f156,f95])).

fof(f95,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl3_1
  <=> r2_hidden(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f156,plain,
    ( ~ r2_hidden(sK1,u1_struct_0(sK0))
    | spl3_2
    | spl3_8 ),
    inference(resolution,[],[f155,f137])).

fof(f155,plain,
    ( ~ r1_tarski(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | spl3_8 ),
    inference(resolution,[],[f153,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f153,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f151])).

fof(f154,plain,
    ( spl3_7
    | ~ spl3_8
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f145,f116,f151,f147])).

fof(f145,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k6_domain_1(u1_struct_0(sK0),sK1),k1_tops_1(sK0,sK2))
    | ~ spl3_5 ),
    inference(resolution,[],[f144,f118])).

fof(f118,plain,
    ( m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f116])).

fof(f144,plain,(
    ! [X0,X1] :
      ( ~ m2_connsp_2(X0,sK0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(X1,k1_tops_1(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f143,f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ m2_connsp_2(X0,sK0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f127,f50])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ~ m2_connsp_2(X0,sK0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f66,f49])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m2_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X2] :
          ( m2_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_connsp_2)).

fof(f143,plain,(
    ! [X0,X1] :
      ( ~ m2_connsp_2(X0,sK0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(X1,k1_tops_1(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f142,f50])).

fof(f142,plain,(
    ! [X0,X1] :
      ( ~ m2_connsp_2(X0,sK0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | r1_tarski(X1,k1_tops_1(sK0,X0)) ) ),
    inference(resolution,[],[f60,f49])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m2_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(X1,k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f124,plain,
    ( ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f54,f120,f116])).

fof(f54,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f42])).

fof(f123,plain,
    ( spl3_5
    | spl3_6 ),
    inference(avatar_split_clause,[],[f53,f120,f116])).

fof(f53,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f42])).

fof(f105,plain,(
    ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f104])).

fof(f104,plain,
    ( $false
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f103,f50])).

fof(f103,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f102,f56])).

fof(f56,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f102,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f101,f48])).

fof(f101,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f99,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f99,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f100,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f89,f97,f93])).

fof(f89,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f63,f51])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:58:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.45  % (4098)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.45  % (4098)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f194,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f100,f105,f123,f124,f154,f158,f179,f193])).
% 0.21/0.45  fof(f193,plain,(
% 0.21/0.45    spl3_2 | spl3_6 | ~spl3_7),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f192])).
% 0.21/0.45  fof(f192,plain,(
% 0.21/0.45    $false | (spl3_2 | spl3_6 | ~spl3_7)),
% 0.21/0.45    inference(subsumption_resolution,[],[f191,f121])).
% 0.21/0.45  fof(f121,plain,(
% 0.21/0.45    ~m1_connsp_2(sK2,sK0,sK1) | spl3_6),
% 0.21/0.45    inference(avatar_component_clause,[],[f120])).
% 0.21/0.45  fof(f120,plain,(
% 0.21/0.45    spl3_6 <=> m1_connsp_2(sK2,sK0,sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.45  fof(f191,plain,(
% 0.21/0.45    m1_connsp_2(sK2,sK0,sK1) | (spl3_2 | ~spl3_7)),
% 0.21/0.45    inference(subsumption_resolution,[],[f190,f52])).
% 0.21/0.45  fof(f52,plain,(
% 0.21/0.45    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.45    inference(cnf_transformation,[],[f42])).
% 0.21/0.45  fof(f42,plain,(
% 0.21/0.45    (((~m1_connsp_2(sK2,sK0,sK1) | ~m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & (m1_connsp_2(sK2,sK0,sK1) | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f38,f41,f40,f39])).
% 0.21/0.45  fof(f39,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (? [X2] : ((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~m1_connsp_2(X2,sK0,X1) | ~m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1))) & (m1_connsp_2(X2,sK0,X1) | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f40,plain,(
% 0.21/0.45    ? [X1] : (? [X2] : ((~m1_connsp_2(X2,sK0,X1) | ~m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1))) & (m1_connsp_2(X2,sK0,X1) | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : ((~m1_connsp_2(X2,sK0,sK1) | ~m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & (m1_connsp_2(X2,sK0,sK1) | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f41,plain,(
% 0.21/0.45    ? [X2] : ((~m1_connsp_2(X2,sK0,sK1) | ~m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & (m1_connsp_2(X2,sK0,sK1) | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => ((~m1_connsp_2(sK2,sK0,sK1) | ~m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & (m1_connsp_2(sK2,sK0,sK1) | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f38,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (? [X2] : ((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.45    inference(flattening,[],[f37])).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (? [X2] : (((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.45    inference(nnf_transformation,[],[f21])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (? [X2] : ((m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <~> m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.45    inference(flattening,[],[f20])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (? [X2] : ((m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <~> m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f19])).
% 0.21/0.45  fof(f19,negated_conjecture,(
% 0.21/0.45    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <=> m1_connsp_2(X2,X0,X1)))))),
% 0.21/0.45    inference(negated_conjecture,[],[f18])).
% 0.21/0.45  fof(f18,conjecture,(
% 0.21/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <=> m1_connsp_2(X2,X0,X1)))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_connsp_2)).
% 0.21/0.45  fof(f190,plain,(
% 0.21/0.45    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(sK2,sK0,sK1) | (spl3_2 | ~spl3_7)),
% 0.21/0.45    inference(resolution,[],[f189,f182])).
% 0.21/0.45  fof(f182,plain,(
% 0.21/0.45    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | (spl3_2 | ~spl3_7)),
% 0.21/0.45    inference(resolution,[],[f149,f135])).
% 0.21/0.45  fof(f135,plain,(
% 0.21/0.45    ( ! [X1] : (~r1_tarski(k6_domain_1(u1_struct_0(sK0),sK1),X1) | r2_hidden(sK1,X1)) ) | spl3_2),
% 0.21/0.45    inference(superposition,[],[f86,f133])).
% 0.21/0.45  fof(f133,plain,(
% 0.21/0.45    k6_domain_1(u1_struct_0(sK0),sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | spl3_2),
% 0.21/0.45    inference(subsumption_resolution,[],[f130,f98])).
% 0.21/0.45  fof(f98,plain,(
% 0.21/0.45    ~v1_xboole_0(u1_struct_0(sK0)) | spl3_2),
% 0.21/0.45    inference(avatar_component_clause,[],[f97])).
% 0.21/0.45  fof(f97,plain,(
% 0.21/0.45    spl3_2 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.46  fof(f130,plain,(
% 0.21/0.46    k6_domain_1(u1_struct_0(sK0),sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.46    inference(resolution,[],[f83,f51])).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.46    inference(cnf_transformation,[],[f42])).
% 0.21/0.46  fof(f83,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) | v1_xboole_0(X0)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f64,f82])).
% 0.21/0.46  fof(f82,plain,(
% 0.21/0.46    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f55,f81])).
% 0.21/0.46  fof(f81,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f62,f80])).
% 0.21/0.46  fof(f80,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f69,f79])).
% 0.21/0.46  fof(f79,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f73,f78])).
% 0.21/0.46  fof(f78,plain,(
% 0.21/0.46    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f74,f77])).
% 0.21/0.46  fof(f77,plain,(
% 0.21/0.46    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f75,f76])).
% 0.21/0.46  fof(f76,plain,(
% 0.21/0.46    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.21/0.46  fof(f75,plain,(
% 0.21/0.46    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.21/0.46  fof(f74,plain,(
% 0.21/0.46    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.46  fof(f73,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.46  fof(f69,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.46  fof(f62,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.46  fof(f55,plain,(
% 0.21/0.46    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.46  fof(f64,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f32])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.46    inference(flattening,[],[f31])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,axiom,(
% 0.21/0.46    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.46  fof(f86,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) | r2_hidden(X0,X2)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f70,f81])).
% 0.21/0.46  fof(f70,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f47])).
% 0.21/0.46  fof(f47,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.46    inference(flattening,[],[f46])).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.46    inference(nnf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.21/0.46  fof(f149,plain,(
% 0.21/0.46    r1_tarski(k6_domain_1(u1_struct_0(sK0),sK1),k1_tops_1(sK0,sK2)) | ~spl3_7),
% 0.21/0.46    inference(avatar_component_clause,[],[f147])).
% 0.21/0.46  fof(f147,plain,(
% 0.21/0.46    spl3_7 <=> r1_tarski(k6_domain_1(u1_struct_0(sK0),sK1),k1_tops_1(sK0,sK2))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.46  fof(f189,plain,(
% 0.21/0.46    ( ! [X0] : (~r2_hidden(sK1,k1_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(X0,sK0,sK1)) )),
% 0.21/0.46    inference(resolution,[],[f188,f51])).
% 0.21/0.46  fof(f188,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,k1_tops_1(sK0,X1)) | m1_connsp_2(X1,sK0,X0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f187,f48])).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    ~v2_struct_0(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f42])).
% 0.21/0.46  fof(f187,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r2_hidden(X0,k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_connsp_2(X1,sK0,X0) | v2_struct_0(sK0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f186,f50])).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    l1_pre_topc(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f42])).
% 0.21/0.46  fof(f186,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r2_hidden(X0,k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | m1_connsp_2(X1,sK0,X0) | v2_struct_0(sK0)) )),
% 0.21/0.46    inference(resolution,[],[f59,f49])).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    v2_pre_topc(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f42])).
% 0.21/0.46  fof(f59,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | m1_connsp_2(X2,X0,X1) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f43])).
% 0.21/0.46  fof(f43,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(nnf_transformation,[],[f26])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f25])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f14])).
% 0.21/0.46  fof(f14,axiom,(
% 0.21/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).
% 0.21/0.46  fof(f179,plain,(
% 0.21/0.46    spl3_2 | spl3_5 | ~spl3_6 | ~spl3_8),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f178])).
% 0.21/0.46  fof(f178,plain,(
% 0.21/0.46    $false | (spl3_2 | spl3_5 | ~spl3_6 | ~spl3_8)),
% 0.21/0.46    inference(subsumption_resolution,[],[f177,f52])).
% 0.21/0.46  fof(f177,plain,(
% 0.21/0.46    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (spl3_2 | spl3_5 | ~spl3_6 | ~spl3_8)),
% 0.21/0.46    inference(subsumption_resolution,[],[f176,f117])).
% 0.21/0.46  fof(f117,plain,(
% 0.21/0.46    ~m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) | spl3_5),
% 0.21/0.46    inference(avatar_component_clause,[],[f116])).
% 0.21/0.46  fof(f116,plain,(
% 0.21/0.46    spl3_5 <=> m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.46  fof(f176,plain,(
% 0.21/0.46    m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (spl3_2 | ~spl3_6 | ~spl3_8)),
% 0.21/0.46    inference(resolution,[],[f175,f169])).
% 0.21/0.46  fof(f169,plain,(
% 0.21/0.46    ( ! [X3] : (~r2_hidden(sK1,k1_tops_1(sK0,X3)) | m2_connsp_2(X3,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl3_2 | ~spl3_8)),
% 0.21/0.46    inference(subsumption_resolution,[],[f168,f152])).
% 0.21/0.46  fof(f152,plain,(
% 0.21/0.46    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_8),
% 0.21/0.46    inference(avatar_component_clause,[],[f151])).
% 0.21/0.46  fof(f151,plain,(
% 0.21/0.46    spl3_8 <=> m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.46  fof(f168,plain,(
% 0.21/0.46    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | m2_connsp_2(X3,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) | ~r2_hidden(sK1,k1_tops_1(sK0,X3))) ) | spl3_2),
% 0.21/0.46    inference(resolution,[],[f166,f137])).
% 0.21/0.46  fof(f137,plain,(
% 0.21/0.46    ( ! [X0] : (r1_tarski(k6_domain_1(u1_struct_0(sK0),sK1),X0) | ~r2_hidden(sK1,X0)) ) | spl3_2),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f134])).
% 0.21/0.46  fof(f134,plain,(
% 0.21/0.46    ( ! [X0] : (r1_tarski(k6_domain_1(u1_struct_0(sK0),sK1),X0) | ~r2_hidden(sK1,X0) | ~r2_hidden(sK1,X0)) ) | spl3_2),
% 0.21/0.46    inference(superposition,[],[f84,f133])).
% 0.21/0.46  fof(f84,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f72,f81])).
% 0.21/0.46  fof(f72,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f47])).
% 0.21/0.46  fof(f166,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r1_tarski(X0,k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m2_connsp_2(X1,sK0,X0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f165,f50])).
% 0.21/0.46  fof(f165,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r1_tarski(X0,k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | m2_connsp_2(X1,sK0,X0)) )),
% 0.21/0.46    inference(resolution,[],[f61,f49])).
% 0.21/0.46  fof(f61,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | m2_connsp_2(X2,X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f44])).
% 0.21/0.46  fof(f44,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : (((m2_connsp_2(X2,X0,X1) | ~r1_tarski(X1,k1_tops_1(X0,X2))) & (r1_tarski(X1,k1_tops_1(X0,X2)) | ~m2_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.46    inference(nnf_transformation,[],[f28])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.46    inference(flattening,[],[f27])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f15])).
% 0.21/0.46  fof(f15,axiom,(
% 0.21/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_connsp_2)).
% 0.21/0.46  fof(f175,plain,(
% 0.21/0.46    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~spl3_6),
% 0.21/0.46    inference(subsumption_resolution,[],[f174,f52])).
% 0.21/0.46  fof(f174,plain,(
% 0.21/0.46    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~spl3_6),
% 0.21/0.46    inference(resolution,[],[f173,f122])).
% 0.21/0.46  fof(f122,plain,(
% 0.21/0.46    m1_connsp_2(sK2,sK0,sK1) | ~spl3_6),
% 0.21/0.46    inference(avatar_component_clause,[],[f120])).
% 0.21/0.46  fof(f173,plain,(
% 0.21/0.46    ( ! [X0] : (~m1_connsp_2(X0,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK1,k1_tops_1(sK0,X0))) )),
% 0.21/0.46    inference(resolution,[],[f172,f51])).
% 0.21/0.46  fof(f172,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_connsp_2(X0,sK0,X1) | r2_hidden(X1,k1_tops_1(sK0,X0))) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f171,f48])).
% 0.21/0.46  fof(f171,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_connsp_2(X0,sK0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(X1,k1_tops_1(sK0,X0)) | v2_struct_0(sK0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f170,f50])).
% 0.21/0.46  fof(f170,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_connsp_2(X0,sK0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | r2_hidden(X1,k1_tops_1(sK0,X0)) | v2_struct_0(sK0)) )),
% 0.21/0.46    inference(resolution,[],[f58,f49])).
% 0.21/0.46  fof(f58,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | r2_hidden(X1,k1_tops_1(X0,X2)) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f43])).
% 0.21/0.46  fof(f158,plain,(
% 0.21/0.46    ~spl3_1 | spl3_2 | spl3_8),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f157])).
% 0.21/0.46  fof(f157,plain,(
% 0.21/0.46    $false | (~spl3_1 | spl3_2 | spl3_8)),
% 0.21/0.46    inference(subsumption_resolution,[],[f156,f95])).
% 0.21/0.46  fof(f95,plain,(
% 0.21/0.46    r2_hidden(sK1,u1_struct_0(sK0)) | ~spl3_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f93])).
% 0.21/0.46  fof(f93,plain,(
% 0.21/0.46    spl3_1 <=> r2_hidden(sK1,u1_struct_0(sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.46  fof(f156,plain,(
% 0.21/0.46    ~r2_hidden(sK1,u1_struct_0(sK0)) | (spl3_2 | spl3_8)),
% 0.21/0.46    inference(resolution,[],[f155,f137])).
% 0.21/0.46  fof(f155,plain,(
% 0.21/0.46    ~r1_tarski(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | spl3_8),
% 0.21/0.46    inference(resolution,[],[f153,f68])).
% 0.21/0.46  fof(f68,plain,(
% 0.21/0.46    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f45])).
% 0.21/0.46  fof(f45,plain,(
% 0.21/0.46    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.46    inference(nnf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,axiom,(
% 0.21/0.46    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.46  fof(f153,plain,(
% 0.21/0.46    ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_8),
% 0.21/0.46    inference(avatar_component_clause,[],[f151])).
% 0.21/0.46  fof(f154,plain,(
% 0.21/0.46    spl3_7 | ~spl3_8 | ~spl3_5),
% 0.21/0.46    inference(avatar_split_clause,[],[f145,f116,f151,f147])).
% 0.21/0.46  fof(f145,plain,(
% 0.21/0.46    ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k6_domain_1(u1_struct_0(sK0),sK1),k1_tops_1(sK0,sK2)) | ~spl3_5),
% 0.21/0.46    inference(resolution,[],[f144,f118])).
% 0.21/0.46  fof(f118,plain,(
% 0.21/0.46    m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) | ~spl3_5),
% 0.21/0.46    inference(avatar_component_clause,[],[f116])).
% 0.21/0.46  fof(f144,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m2_connsp_2(X0,sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X1,k1_tops_1(sK0,X0))) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f143,f128])).
% 0.21/0.46  fof(f128,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m2_connsp_2(X0,sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f127,f50])).
% 0.21/0.46  fof(f127,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m2_connsp_2(X0,sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.46    inference(resolution,[],[f66,f49])).
% 0.21/0.46  fof(f66,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~m2_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f36])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.46    inference(flattening,[],[f35])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f17])).
% 0.21/0.46  fof(f17,axiom,(
% 0.21/0.46    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X2] : (m2_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_connsp_2)).
% 0.21/0.46  fof(f143,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m2_connsp_2(X0,sK0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X1,k1_tops_1(sK0,X0))) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f142,f50])).
% 0.21/0.46  fof(f142,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m2_connsp_2(X0,sK0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | r1_tarski(X1,k1_tops_1(sK0,X0))) )),
% 0.21/0.46    inference(resolution,[],[f60,f49])).
% 0.21/0.46  fof(f60,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~m2_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_tarski(X1,k1_tops_1(X0,X2))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f44])).
% 0.21/0.46  fof(f124,plain,(
% 0.21/0.46    ~spl3_5 | ~spl3_6),
% 0.21/0.46    inference(avatar_split_clause,[],[f54,f120,f116])).
% 0.21/0.46  fof(f54,plain,(
% 0.21/0.46    ~m1_connsp_2(sK2,sK0,sK1) | ~m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))),
% 0.21/0.46    inference(cnf_transformation,[],[f42])).
% 0.21/0.46  fof(f123,plain,(
% 0.21/0.46    spl3_5 | spl3_6),
% 0.21/0.46    inference(avatar_split_clause,[],[f53,f120,f116])).
% 0.21/0.46  fof(f53,plain,(
% 0.21/0.46    m1_connsp_2(sK2,sK0,sK1) | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))),
% 0.21/0.46    inference(cnf_transformation,[],[f42])).
% 0.21/0.46  fof(f105,plain,(
% 0.21/0.46    ~spl3_2),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f104])).
% 0.21/0.46  fof(f104,plain,(
% 0.21/0.46    $false | ~spl3_2),
% 0.21/0.46    inference(subsumption_resolution,[],[f103,f50])).
% 0.21/0.46  fof(f103,plain,(
% 0.21/0.46    ~l1_pre_topc(sK0) | ~spl3_2),
% 0.21/0.46    inference(resolution,[],[f102,f56])).
% 0.21/0.46  fof(f56,plain,(
% 0.21/0.46    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,axiom,(
% 0.21/0.46    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.46  fof(f102,plain,(
% 0.21/0.46    ~l1_struct_0(sK0) | ~spl3_2),
% 0.21/0.46    inference(subsumption_resolution,[],[f101,f48])).
% 0.21/0.46  fof(f101,plain,(
% 0.21/0.46    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl3_2),
% 0.21/0.46    inference(resolution,[],[f99,f57])).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f24])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f23])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,axiom,(
% 0.21/0.46    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.46  fof(f99,plain,(
% 0.21/0.46    v1_xboole_0(u1_struct_0(sK0)) | ~spl3_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f97])).
% 0.21/0.46  fof(f100,plain,(
% 0.21/0.46    spl3_1 | spl3_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f89,f97,f93])).
% 0.21/0.46  fof(f89,plain,(
% 0.21/0.46    v1_xboole_0(u1_struct_0(sK0)) | r2_hidden(sK1,u1_struct_0(sK0))),
% 0.21/0.46    inference(resolution,[],[f63,f51])).
% 0.21/0.46  fof(f63,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f30])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.46    inference(flattening,[],[f29])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,axiom,(
% 0.21/0.46    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (4098)------------------------------
% 0.21/0.46  % (4098)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (4098)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (4098)Memory used [KB]: 6268
% 0.21/0.46  % (4098)Time elapsed: 0.042 s
% 0.21/0.46  % (4098)------------------------------
% 0.21/0.46  % (4098)------------------------------
% 0.21/0.46  % (4083)Success in time 0.097 s
%------------------------------------------------------------------------------
