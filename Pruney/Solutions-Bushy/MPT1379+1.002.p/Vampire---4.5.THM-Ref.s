%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1379+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:50 EST 2020

% Result     : Theorem 2.06s
% Output     : Refutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :  174 (1125 expanded)
%              Number of leaves         :   22 ( 411 expanded)
%              Depth                    :   19
%              Number of atoms          :  707 (11141 expanded)
%              Number of equality atoms :   38 ( 118 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2839,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f75,f76,f207,f235,f305,f479,f2206,f2213,f2743,f2838])).

fof(f2838,plain,
    ( spl5_2
    | ~ spl5_13 ),
    inference(avatar_contradiction_clause,[],[f2837])).

fof(f2837,plain,
    ( $false
    | spl5_2
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f2830,f497])).

fof(f497,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f206,f180])).

fof(f180,plain,(
    ! [X5] : k9_subset_1(u1_struct_0(sK0),X5,sK3) = k3_xboole_0(X5,sK3) ),
    inference(resolution,[],[f41,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f41,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)
      | ~ m1_connsp_2(sK3,sK0,sK1)
      | ~ m1_connsp_2(sK2,sK0,sK1) )
    & ( m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)
      | ( m1_connsp_2(sK3,sK0,sK1)
        & m1_connsp_2(sK2,sK0,sK1) ) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f28,f27,f26,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                      | ~ m1_connsp_2(X3,X0,X1)
                      | ~ m1_connsp_2(X2,X0,X1) )
                    & ( m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                      | ( m1_connsp_2(X3,X0,X1)
                        & m1_connsp_2(X2,X0,X1) ) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(sK0),X2,X3),sK0,X1)
                    | ~ m1_connsp_2(X3,sK0,X1)
                    | ~ m1_connsp_2(X2,sK0,X1) )
                  & ( m1_connsp_2(k9_subset_1(u1_struct_0(sK0),X2,X3),sK0,X1)
                    | ( m1_connsp_2(X3,sK0,X1)
                      & m1_connsp_2(X2,sK0,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(sK0),X2,X3),sK0,X1)
                  | ~ m1_connsp_2(X3,sK0,X1)
                  | ~ m1_connsp_2(X2,sK0,X1) )
                & ( m1_connsp_2(k9_subset_1(u1_struct_0(sK0),X2,X3),sK0,X1)
                  | ( m1_connsp_2(X3,sK0,X1)
                    & m1_connsp_2(X2,sK0,X1) ) )
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(sK0),X2,X3),sK0,sK1)
                | ~ m1_connsp_2(X3,sK0,sK1)
                | ~ m1_connsp_2(X2,sK0,sK1) )
              & ( m1_connsp_2(k9_subset_1(u1_struct_0(sK0),X2,X3),sK0,sK1)
                | ( m1_connsp_2(X3,sK0,sK1)
                  & m1_connsp_2(X2,sK0,sK1) ) )
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(sK0),X2,X3),sK0,sK1)
              | ~ m1_connsp_2(X3,sK0,sK1)
              | ~ m1_connsp_2(X2,sK0,sK1) )
            & ( m1_connsp_2(k9_subset_1(u1_struct_0(sK0),X2,X3),sK0,sK1)
              | ( m1_connsp_2(X3,sK0,sK1)
                & m1_connsp_2(X2,sK0,sK1) ) )
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X3] :
          ( ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,X3),sK0,sK1)
            | ~ m1_connsp_2(X3,sK0,sK1)
            | ~ m1_connsp_2(sK2,sK0,sK1) )
          & ( m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,X3),sK0,sK1)
            | ( m1_connsp_2(X3,sK0,sK1)
              & m1_connsp_2(sK2,sK0,sK1) ) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X3] :
        ( ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,X3),sK0,sK1)
          | ~ m1_connsp_2(X3,sK0,sK1)
          | ~ m1_connsp_2(sK2,sK0,sK1) )
        & ( m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,X3),sK0,sK1)
          | ( m1_connsp_2(X3,sK0,sK1)
            & m1_connsp_2(sK2,sK0,sK1) ) )
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)
        | ~ m1_connsp_2(sK3,sK0,sK1)
        | ~ m1_connsp_2(sK2,sK0,sK1) )
      & ( m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)
        | ( m1_connsp_2(sK3,sK0,sK1)
          & m1_connsp_2(sK2,sK0,sK1) ) )
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                    | ~ m1_connsp_2(X3,X0,X1)
                    | ~ m1_connsp_2(X2,X0,X1) )
                  & ( m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                    | ( m1_connsp_2(X3,X0,X1)
                      & m1_connsp_2(X2,X0,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                    | ~ m1_connsp_2(X3,X0,X1)
                    | ~ m1_connsp_2(X2,X0,X1) )
                  & ( m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                    | ( m1_connsp_2(X3,X0,X1)
                      & m1_connsp_2(X2,X0,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( m1_connsp_2(X3,X0,X1)
                      & m1_connsp_2(X2,X0,X1) )
                  <~> m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( m1_connsp_2(X3,X0,X1)
                      & m1_connsp_2(X2,X0,X1) )
                  <~> m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( ( m1_connsp_2(X3,X0,X1)
                        & m1_connsp_2(X2,X0,X1) )
                    <=> m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( m1_connsp_2(X3,X0,X1)
                      & m1_connsp_2(X2,X0,X1) )
                  <=> m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_connsp_2)).

fof(f206,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK3)))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl5_13
  <=> r2_hidden(sK1,k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f2830,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))
    | spl5_2 ),
    inference(superposition,[],[f2771,f1752])).

fof(f1752,plain,(
    k1_tops_1(sK0,k3_xboole_0(sK2,sK3)) = k3_xboole_0(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2)) ),
    inference(forward_demodulation,[],[f1710,f58])).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f1710,plain,(
    k1_tops_1(sK0,k3_xboole_0(sK3,sK2)) = k3_xboole_0(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2)) ),
    inference(resolution,[],[f1662,f41])).

fof(f1662,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_tops_1(sK0,k3_xboole_0(X3,sK2)) = k3_xboole_0(k1_tops_1(sK0,X3),k1_tops_1(sK0,sK2)) ) ),
    inference(backward_demodulation,[],[f1079,f246])).

fof(f246,plain,(
    ! [X5] : k9_subset_1(u1_struct_0(sK0),X5,k1_tops_1(sK0,sK2)) = k3_xboole_0(X5,k1_tops_1(sK0,sK2)) ),
    inference(resolution,[],[f163,f45])).

fof(f163,plain,(
    m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f156,f38])).

fof(f38,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f156,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f40,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f40,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f1079,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X3),k1_tops_1(sK0,sK2)) = k1_tops_1(sK0,k3_xboole_0(X3,sK2)) ) ),
    inference(forward_demodulation,[],[f173,f162])).

fof(f162,plain,(
    ! [X5] : k9_subset_1(u1_struct_0(sK0),X5,sK2) = k3_xboole_0(X5,sK2) ),
    inference(resolution,[],[f40,f45])).

fof(f173,plain,(
    ! [X3] :
      ( k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X3),k1_tops_1(sK0,sK2)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X3,sK2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f172,f37])).

fof(f37,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f172,plain,(
    ! [X3] :
      ( k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X3),k1_tops_1(sK0,sK2)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X3,sK2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f160,f38])).

fof(f160,plain,(
    ! [X3] :
      ( k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X3),k1_tops_1(sK0,sK2)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X3,sK2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f40,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tops_1)).

fof(f2771,plain,
    ( ! [X0] : ~ r2_hidden(sK1,k3_xboole_0(k1_tops_1(sK0,sK3),X0))
    | spl5_2 ),
    inference(resolution,[],[f2769,f61])).

fof(f61,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f34])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f2769,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | spl5_2 ),
    inference(subsumption_resolution,[],[f2768,f36])).

fof(f36,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f2768,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | v2_struct_0(sK0)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f2767,f37])).

fof(f2767,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f2766,f38])).

fof(f2766,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f2765,f39])).

fof(f39,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f2765,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f2764,f41])).

fof(f2764,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_2 ),
    inference(resolution,[],[f69,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

fof(f69,plain,
    ( ~ m1_connsp_2(sK3,sK0,sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl5_2
  <=> m1_connsp_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f2743,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | spl5_3 ),
    inference(avatar_contradiction_clause,[],[f2742])).

fof(f2742,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | spl5_3 ),
    inference(subsumption_resolution,[],[f2730,f2271])).

fof(f2271,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))
    | spl5_3 ),
    inference(subsumption_resolution,[],[f2270,f36])).

fof(f2270,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))
    | v2_struct_0(sK0)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f2269,f37])).

fof(f2269,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f2268,f38])).

fof(f2268,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f2267,f39])).

fof(f2267,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f2241,f360])).

fof(f360,plain,(
    ! [X0] : m1_subset_1(k3_xboole_0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f331,f58])).

fof(f331,plain,(
    ! [X0] : m1_subset_1(k3_xboole_0(X0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f319,f40])).

fof(f319,plain,(
    ! [X0] :
      ( m1_subset_1(k3_xboole_0(X0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f161,f45])).

fof(f161,plain,(
    ! [X4] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X4,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f40,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f2241,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))
    | ~ m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_3 ),
    inference(resolution,[],[f485,f50])).

fof(f485,plain,
    ( ~ m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | spl5_3 ),
    inference(forward_demodulation,[],[f73,f180])).

fof(f73,plain,
    ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl5_3
  <=> m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f2730,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f2235,f1913])).

fof(f1913,plain,(
    k1_tops_1(sK0,k3_xboole_0(sK2,sK3)) = k3_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3)) ),
    inference(resolution,[],[f1811,f40])).

fof(f1811,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_tops_1(sK0,k3_xboole_0(X3,sK3)) = k3_xboole_0(k1_tops_1(sK0,X3),k1_tops_1(sK0,sK3)) ) ),
    inference(backward_demodulation,[],[f1299,f264])).

fof(f264,plain,(
    ! [X5] : k9_subset_1(u1_struct_0(sK0),X5,k1_tops_1(sK0,sK3)) = k3_xboole_0(X5,k1_tops_1(sK0,sK3)) ),
    inference(resolution,[],[f181,f45])).

fof(f181,plain,(
    m1_subset_1(k1_tops_1(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f174,f38])).

fof(f174,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f41,f51])).

fof(f1299,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X3),k1_tops_1(sK0,sK3)) = k1_tops_1(sK0,k3_xboole_0(X3,sK3)) ) ),
    inference(forward_demodulation,[],[f191,f180])).

fof(f191,plain,(
    ! [X3] :
      ( k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X3),k1_tops_1(sK0,sK3)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X3,sK3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f190,f37])).

fof(f190,plain,(
    ! [X3] :
      ( k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X3),k1_tops_1(sK0,sK3)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X3,sK3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f178,f38])).

fof(f178,plain,(
    ! [X3] :
      ( k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X3),k1_tops_1(sK0,sK3)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X3,sK3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f41,f47])).

fof(f2235,plain,
    ( r2_hidden(sK1,k3_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3)))
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f2219,f513])).

fof(f513,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK1,X1)
        | r2_hidden(sK1,k3_xboole_0(X1,k1_tops_1(sK0,sK3))) )
    | ~ spl5_2 ),
    inference(resolution,[],[f510,f59])).

fof(f59,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f510,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f509,f36])).

fof(f509,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | v2_struct_0(sK0)
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f508,f37])).

fof(f508,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f507,f38])).

fof(f507,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f506,f39])).

fof(f506,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f504,f41])).

fof(f504,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_2 ),
    inference(resolution,[],[f68,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f68,plain,
    ( m1_connsp_2(sK3,sK0,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f2219,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f2218,f36])).

fof(f2218,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | v2_struct_0(sK0)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f2217,f37])).

fof(f2217,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f2216,f38])).

fof(f2216,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f2215,f39])).

fof(f2215,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f488,f40])).

fof(f488,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_1 ),
    inference(resolution,[],[f64,f49])).

fof(f64,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl5_1
  <=> m1_connsp_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f2213,plain,
    ( spl5_1
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f749,f152,f63])).

fof(f152,plain,
    ( spl5_11
  <=> r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f749,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f169,f39])).

fof(f169,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,k1_tops_1(sK0,sK2))
      | m1_connsp_2(sK2,sK0,X1) ) ),
    inference(subsumption_resolution,[],[f168,f36])).

fof(f168,plain,(
    ! [X1] :
      ( m1_connsp_2(sK2,sK0,X1)
      | ~ r2_hidden(X1,k1_tops_1(sK0,sK2))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f167,f37])).

fof(f167,plain,(
    ! [X1] :
      ( m1_connsp_2(sK2,sK0,X1)
      | ~ r2_hidden(X1,k1_tops_1(sK0,sK2))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f158,f38])).

fof(f158,plain,(
    ! [X1] :
      ( m1_connsp_2(sK2,sK0,X1)
      | ~ r2_hidden(X1,k1_tops_1(sK0,sK2))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f40,f50])).

fof(f2206,plain,
    ( spl5_11
    | ~ spl5_15 ),
    inference(avatar_contradiction_clause,[],[f2205])).

fof(f2205,plain,
    ( $false
    | spl5_11
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f2189,f234])).

fof(f234,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f232])).

fof(f232,plain,
    ( spl5_15
  <=> r2_hidden(sK1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f2189,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))
    | spl5_11 ),
    inference(superposition,[],[f217,f1752])).

fof(f217,plain,
    ( ! [X1] : ~ r2_hidden(sK1,k3_xboole_0(X1,k1_tops_1(sK0,sK2)))
    | spl5_11 ),
    inference(resolution,[],[f154,f60])).

fof(f60,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f154,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | spl5_11 ),
    inference(avatar_component_clause,[],[f152])).

fof(f479,plain,(
    spl5_12 ),
    inference(avatar_contradiction_clause,[],[f478])).

fof(f478,plain,
    ( $false
    | spl5_12 ),
    inference(subsumption_resolution,[],[f470,f360])).

fof(f470,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_12 ),
    inference(forward_demodulation,[],[f202,f180])).

fof(f202,plain,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_12 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl5_12
  <=> m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f305,plain,
    ( ~ spl5_3
    | spl5_14 ),
    inference(avatar_contradiction_clause,[],[f304])).

fof(f304,plain,
    ( $false
    | ~ spl5_3
    | spl5_14 ),
    inference(subsumption_resolution,[],[f239,f230])).

fof(f230,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_14 ),
    inference(avatar_component_clause,[],[f228])).

fof(f228,plain,
    ( spl5_14
  <=> m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f239,plain,
    ( m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f238,f36])).

fof(f238,plain,
    ( m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f237,f37])).

fof(f237,plain,
    ( m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f236,f38])).

fof(f236,plain,
    ( m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f219,f39])).

fof(f219,plain,
    ( m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3 ),
    inference(resolution,[],[f212,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f212,plain,
    ( m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f194,f41])).

fof(f194,plain,
    ( m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_3 ),
    inference(superposition,[],[f72,f45])).

fof(f72,plain,
    ( m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f235,plain,
    ( ~ spl5_14
    | spl5_15
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f226,f71,f232,f228])).

fof(f226,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))
    | ~ m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f225,f36])).

fof(f225,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))
    | ~ m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f224,f37])).

fof(f224,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))
    | ~ m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f223,f38])).

fof(f223,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))
    | ~ m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f218,f39])).

fof(f218,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))
    | ~ m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3 ),
    inference(resolution,[],[f212,f49])).

fof(f207,plain,
    ( ~ spl5_12
    | spl5_13
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f198,f71,f204,f200])).

fof(f198,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK3)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f197,f36])).

fof(f197,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK3)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f196,f37])).

fof(f196,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK3)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f195,f38])).

fof(f195,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK3)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f192,f39])).

fof(f192,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK3)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3 ),
    inference(resolution,[],[f72,f49])).

fof(f76,plain,
    ( spl5_1
    | spl5_3 ),
    inference(avatar_split_clause,[],[f42,f71,f63])).

fof(f42,plain,
    ( m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f75,plain,
    ( spl5_2
    | spl5_3 ),
    inference(avatar_split_clause,[],[f43,f71,f67])).

fof(f43,plain,
    ( m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)
    | m1_connsp_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f74,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f44,f71,f67,f63])).

fof(f44,plain,
    ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)
    | ~ m1_connsp_2(sK3,sK0,sK1)
    | ~ m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

%------------------------------------------------------------------------------
