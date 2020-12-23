%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1873+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:48 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 709 expanded)
%              Number of leaves         :   26 ( 214 expanded)
%              Depth                    :   25
%              Number of atoms          :  678 (5609 expanded)
%              Number of equality atoms :   73 ( 942 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1239,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f87,f92,f96,f304,f562,f861,f930,f1238])).

fof(f1238,plain,
    ( ~ spl5_1
    | spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(avatar_contradiction_clause,[],[f1237])).

fof(f1237,plain,
    ( $false
    | ~ spl5_1
    | spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(subsumption_resolution,[],[f1236,f86])).

fof(f86,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl5_3
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f1236,plain,
    ( ~ r1_tarski(sK2,sK1)
    | ~ spl5_1
    | spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(subsumption_resolution,[],[f1235,f384])).

fof(f384,plain,
    ( r1_tarski(sK2,k2_pre_topc(sK0,sK2))
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f351,f47])).

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ( ( sK2 != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2))
        & r1_tarski(sK2,sK1)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )
      | ~ v2_tex_2(sK1,sK0) )
    & ( ! [X3] :
          ( k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X3)) = X3
          | ~ r1_tarski(X3,sK1)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | v2_tex_2(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f34,f37,f36,f35])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | v2_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X2)) != X2
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
            | ~ v2_tex_2(X1,sK0) )
          & ( ! [X3] :
                ( k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X3)) = X3
                | ~ r1_tarski(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            | v2_tex_2(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X1] :
        ( ( ? [X2] :
              ( k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X2)) != X2
              & r1_tarski(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          | ~ v2_tex_2(X1,sK0) )
        & ( ! [X3] :
              ( k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X3)) = X3
              | ~ r1_tarski(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          | v2_tex_2(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ? [X2] :
            ( k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X2)) != X2
            & r1_tarski(X2,sK1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        | ~ v2_tex_2(sK1,sK0) )
      & ( ! [X3] :
            ( k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X3)) = X3
            | ~ r1_tarski(X3,sK1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        | v2_tex_2(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X2] :
        ( k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X2)) != X2
        & r1_tarski(X2,sK1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( sK2 != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2))
      & r1_tarski(sK2,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_tex_2(X1,X0) )
          & ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
                | ~ r1_tarski(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_tex_2(X1,X0) )
          & ( ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_tex_2(X1,X0) )
          & ( ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tex_2(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( r1_tarski(X2,X1)
                   => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tex_2(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( r1_tarski(X2,X1)
                   => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r1_tarski(X2,X1)
                 => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).

fof(f351,plain,
    ( r1_tarski(sK2,k2_pre_topc(sK0,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_4 ),
    inference(resolution,[],[f91,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f91,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl5_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f1235,plain,
    ( ~ r1_tarski(sK2,k2_pre_topc(sK0,sK2))
    | ~ r1_tarski(sK2,sK1)
    | ~ spl5_1
    | spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(resolution,[],[f1226,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f1226,plain,
    ( ~ r1_tarski(sK2,k3_xboole_0(sK1,k2_pre_topc(sK0,sK2)))
    | ~ spl5_1
    | spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(subsumption_resolution,[],[f1225,f426])).

fof(f426,plain,
    ( sK2 != k3_xboole_0(sK1,k2_pre_topc(sK0,sK2))
    | spl5_2 ),
    inference(superposition,[],[f412,f62])).

fof(f62,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f412,plain,
    ( sK2 != k3_xboole_0(k2_pre_topc(sK0,sK2),sK1)
    | spl5_2 ),
    inference(superposition,[],[f81,f194])).

fof(f194,plain,(
    ! [X3] : k9_subset_1(u1_struct_0(sK0),sK1,X3) = k3_xboole_0(X3,sK1) ),
    inference(forward_demodulation,[],[f104,f105])).

fof(f105,plain,(
    ! [X4] : k9_subset_1(u1_struct_0(sK0),X4,sK1) = k3_xboole_0(X4,sK1) ),
    inference(resolution,[],[f48,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f48,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f104,plain,(
    ! [X3] : k9_subset_1(u1_struct_0(sK0),X3,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X3) ),
    inference(resolution,[],[f48,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f81,plain,
    ( sK2 != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl5_2
  <=> sK2 = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f1225,plain,
    ( sK2 = k3_xboole_0(sK1,k2_pre_topc(sK0,sK2))
    | ~ r1_tarski(sK2,k3_xboole_0(sK1,k2_pre_topc(sK0,sK2)))
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(resolution,[],[f1218,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1218,plain,
    ( r1_tarski(k3_xboole_0(sK1,k2_pre_topc(sK0,sK2)),sK2)
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f1213,f62])).

fof(f1213,plain,
    ( r1_tarski(k3_xboole_0(k2_pre_topc(sK0,sK2),sK1),sK2)
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(resolution,[],[f855,f557])).

fof(f557,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK2),sK4(sK0,sK1,sK2))
    | ~ spl5_50 ),
    inference(avatar_component_clause,[],[f555])).

fof(f555,plain,
    ( spl5_50
  <=> r1_tarski(k2_pre_topc(sK0,sK2),sK4(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

fof(f855,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,sK4(sK0,sK1,sK2))
        | r1_tarski(k3_xboole_0(X1,sK1),sK2) )
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(superposition,[],[f68,f804])).

fof(f804,plain,
    ( sK2 = k3_xboole_0(sK4(sK0,sK1,sK2),sK1)
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(superposition,[],[f607,f194])).

fof(f607,plain,
    ( sK2 = k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,sK2))
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f606,f86])).

fof(f606,plain,
    ( sK2 = k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,sK2))
    | ~ r1_tarski(sK2,sK1)
    | ~ spl5_1
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f601,f76])).

fof(f76,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl5_1
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f601,plain,
    ( sK2 = k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,sK2))
    | ~ v2_tex_2(sK1,sK0)
    | ~ r1_tarski(sK2,sK1)
    | ~ spl5_4 ),
    inference(resolution,[],[f386,f48])).

fof(f386,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | sK2 = k9_subset_1(u1_struct_0(sK0),X1,sK4(sK0,X1,sK2))
        | ~ v2_tex_2(X1,sK0)
        | ~ r1_tarski(sK2,X1) )
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f353,f47])).

fof(f353,plain,
    ( ! [X1] :
        ( ~ r1_tarski(sK2,X1)
        | sK2 = k9_subset_1(u1_struct_0(sK0),X1,sK4(sK0,X1,sK2))
        | ~ v2_tex_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl5_4 ),
    inference(resolution,[],[f91,f56])).

fof(f56,plain,(
    ! [X4,X0,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X4,X1)
      | k9_subset_1(u1_struct_0(X0),X1,sK4(X0,X1,X4)) = X4
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK3(X0,X1)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r1_tarski(sK3(X0,X1),X1)
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ( k9_subset_1(u1_struct_0(X0),X1,sK4(X0,X1,X4)) = X4
                    & v4_pre_topc(sK4(X0,X1,X4),X0)
                    & m1_subset_1(sK4(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f40,f42,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
              | ~ v4_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK3(X0,X1)
            | ~ v4_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r1_tarski(sK3(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
          & v4_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK4(X0,X1,X4)) = X4
        & v4_pre_topc(sK4(X0,X1,X4),X0)
        & m1_subset_1(sK4(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ? [X5] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
                      & v4_pre_topc(X5,X0)
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
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
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_xboole_1)).

fof(f930,plain,
    ( ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | spl5_51 ),
    inference(avatar_contradiction_clause,[],[f929])).

fof(f929,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | spl5_51 ),
    inference(subsumption_resolution,[],[f928,f47])).

fof(f928,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | spl5_51 ),
    inference(subsumption_resolution,[],[f927,f48])).

fof(f927,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | spl5_51 ),
    inference(subsumption_resolution,[],[f926,f76])).

fof(f926,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_3
    | ~ spl5_4
    | spl5_51 ),
    inference(subsumption_resolution,[],[f925,f91])).

fof(f925,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_3
    | spl5_51 ),
    inference(subsumption_resolution,[],[f924,f86])).

fof(f924,plain,
    ( ~ r1_tarski(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl5_51 ),
    inference(resolution,[],[f561,f55])).

fof(f55,plain,(
    ! [X4,X0,X1] :
      ( v4_pre_topc(sK4(X0,X1,X4),X0)
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f561,plain,
    ( ~ v4_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | spl5_51 ),
    inference(avatar_component_clause,[],[f559])).

fof(f559,plain,
    ( spl5_51
  <=> v4_pre_topc(sK4(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).

fof(f861,plain,
    ( ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | spl5_47 ),
    inference(avatar_contradiction_clause,[],[f860])).

fof(f860,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | spl5_47 ),
    inference(subsumption_resolution,[],[f859,f544])).

fof(f544,plain,
    ( ~ r1_tarski(sK2,sK4(sK0,sK1,sK2))
    | spl5_47 ),
    inference(avatar_component_clause,[],[f542])).

fof(f542,plain,
    ( spl5_47
  <=> r1_tarski(sK2,sK4(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).

fof(f859,plain,
    ( r1_tarski(sK2,sK4(sK0,sK1,sK2))
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(superposition,[],[f61,f804])).

fof(f61,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f562,plain,
    ( ~ spl5_47
    | spl5_50
    | ~ spl5_51
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f528,f89,f84,f75,f559,f555,f542])).

fof(f528,plain,
    ( ~ v4_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | r1_tarski(k2_pre_topc(sK0,sK2),sK4(sK0,sK1,sK2))
    | ~ r1_tarski(sK2,sK4(sK0,sK1,sK2))
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(resolution,[],[f524,f399])).

fof(f399,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X2,sK0)
        | r1_tarski(k2_pre_topc(sK0,sK2),X2)
        | ~ r1_tarski(sK2,X2) )
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f356,f47])).

fof(f356,plain,
    ( ! [X2] :
        ( ~ r1_tarski(sK2,X2)
        | ~ v4_pre_topc(X2,sK0)
        | r1_tarski(k2_pre_topc(sK0,sK2),X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl5_4 ),
    inference(resolution,[],[f91,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | ~ v4_pre_topc(X1,X0)
      | r1_tarski(k2_pre_topc(X0,X2),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X2),X1)
              | ~ r1_tarski(X2,X1)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X2),X1)
              | ~ r1_tarski(X2,X1)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X2,X1)
                  & v4_pre_topc(X1,X0) )
               => r1_tarski(k2_pre_topc(X0,X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_1)).

fof(f524,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f523,f86])).

fof(f523,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK2,sK1)
    | ~ spl5_1
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f519,f76])).

fof(f519,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | ~ r1_tarski(sK2,sK1)
    | ~ spl5_4 ),
    inference(resolution,[],[f385,f48])).

fof(f385,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(sK4(sK0,X0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK0)
        | ~ r1_tarski(sK2,X0) )
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f352,f47])).

fof(f352,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2,X0)
        | m1_subset_1(sK4(sK0,X0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl5_4 ),
    inference(resolution,[],[f91,f54])).

fof(f54,plain,(
    ! [X4,X0,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X4,X1)
      | m1_subset_1(sK4(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f304,plain,
    ( spl5_1
    | ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f303])).

fof(f303,plain,
    ( $false
    | spl5_1
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f302,f47])).

fof(f302,plain,
    ( ~ l1_pre_topc(sK0)
    | spl5_1
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f301,f110])).

fof(f110,plain,
    ( m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_1 ),
    inference(subsumption_resolution,[],[f109,f47])).

fof(f109,plain,
    ( m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f100,f77])).

fof(f77,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f100,plain,
    ( m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f48,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f301,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl5_1
    | ~ spl5_5 ),
    inference(resolution,[],[f300,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f300,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK3(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_1
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f299,f47])).

fof(f299,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK3(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl5_1
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f298,f48])).

fof(f298,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK3(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl5_1
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f297,f172])).

fof(f172,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK3(sK0,sK1)),sK0)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f171,f46])).

fof(f46,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f171,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK3(sK0,sK1)),sK0)
    | ~ v2_pre_topc(sK0)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f147,f47])).

fof(f147,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK3(sK0,sK1)),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl5_1 ),
    inference(resolution,[],[f110,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f297,plain,
    ( ~ v4_pre_topc(k2_pre_topc(sK0,sK3(sK0,sK1)),sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK3(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl5_1
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f296,f77])).

fof(f296,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ v4_pre_topc(k2_pre_topc(sK0,sK3(sK0,sK1)),sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK3(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl5_1
    | ~ spl5_5 ),
    inference(trivial_inequality_removal,[],[f295])).

fof(f295,plain,
    ( sK3(sK0,sK1) != sK3(sK0,sK1)
    | v2_tex_2(sK1,sK0)
    | ~ v4_pre_topc(k2_pre_topc(sK0,sK3(sK0,sK1)),sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK3(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl5_1
    | ~ spl5_5 ),
    inference(superposition,[],[f59,f150])).

fof(f150,plain,
    ( sK3(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK3(sK0,sK1)))
    | spl5_1
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f140,f112])).

fof(f112,plain,
    ( r1_tarski(sK3(sK0,sK1),sK1)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f111,f47])).

fof(f111,plain,
    ( r1_tarski(sK3(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f101,f77])).

fof(f101,plain,
    ( r1_tarski(sK3(sK0,sK1),sK1)
    | v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f48,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(sK3(X0,X1),X1)
      | v2_tex_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f140,plain,
    ( sK3(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK3(sK0,sK1)))
    | ~ r1_tarski(sK3(sK0,sK1),sK1)
    | spl5_1
    | ~ spl5_5 ),
    inference(resolution,[],[f110,f95])).

fof(f95,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X3)) = X3
        | ~ r1_tarski(X3,sK1) )
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl5_5
  <=> ! [X3] :
        ( k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X3)) = X3
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X3,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK3(X0,X1)
      | v2_tex_2(X1,X0)
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f96,plain,
    ( spl5_1
    | spl5_5 ),
    inference(avatar_split_clause,[],[f49,f94,f75])).

fof(f49,plain,(
    ! [X3] :
      ( k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X3)) = X3
      | ~ r1_tarski(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tex_2(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f92,plain,
    ( ~ spl5_1
    | spl5_4 ),
    inference(avatar_split_clause,[],[f50,f89,f75])).

fof(f50,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f87,plain,
    ( ~ spl5_1
    | spl5_3 ),
    inference(avatar_split_clause,[],[f51,f84,f75])).

fof(f51,plain,
    ( r1_tarski(sK2,sK1)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f82,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f52,f79,f75])).

fof(f52,plain,
    ( sK2 != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2))
    | ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

%------------------------------------------------------------------------------
