%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1379+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:50 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 868 expanded)
%              Number of leaves         :   32 ( 337 expanded)
%              Depth                    :   16
%              Number of atoms          :  643 (7669 expanded)
%              Number of equality atoms :   38 ( 140 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1853,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f74,f75,f127,f154,f162,f170,f174,f187,f195,f203,f223,f227,f231,f235,f242,f526,f1613,f1615,f1623,f1646,f1656,f1670,f1849])).

fof(f1849,plain,
    ( ~ spl5_14
    | ~ spl5_20
    | ~ spl5_22
    | spl5_26
    | ~ spl5_61 ),
    inference(avatar_contradiction_clause,[],[f1828])).

fof(f1828,plain,
    ( $false
    | ~ spl5_14
    | ~ spl5_20
    | ~ spl5_22
    | spl5_26
    | ~ spl5_61 ),
    inference(unit_resulting_resolution,[],[f139,f1679,f1796,f58])).

fof(f58,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).

fof(f33,plain,(
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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f31])).

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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f1796,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))
    | ~ spl5_14
    | ~ spl5_20
    | ~ spl5_22
    | ~ spl5_61 ),
    inference(forward_demodulation,[],[f1790,f1281])).

fof(f1281,plain,
    ( k1_tops_1(sK0,k3_xboole_0(sK2,sK3)) = k3_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3))
    | ~ spl5_20
    | ~ spl5_22 ),
    inference(resolution,[],[f1241,f39])).

fof(f39,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f27,f26,f25,f24])).

fof(f24,plain,
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

fof(f25,plain,
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

fof(f26,plain,
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

fof(f27,plain,
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_connsp_2)).

fof(f1241,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_tops_1(sK0,k3_xboole_0(X1,sK3)) = k3_xboole_0(k1_tops_1(sK0,X1),k1_tops_1(sK0,sK3)) )
    | ~ spl5_20
    | ~ spl5_22 ),
    inference(backward_demodulation,[],[f649,f290])).

fof(f290,plain,
    ( ! [X4] : k9_subset_1(u1_struct_0(sK0),X4,k1_tops_1(sK0,sK3)) = k3_xboole_0(X4,k1_tops_1(sK0,sK3))
    | ~ spl5_20 ),
    inference(resolution,[],[f186,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f186,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl5_20
  <=> m1_subset_1(k1_tops_1(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f649,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,sK3)) = k1_tops_1(sK0,k3_xboole_0(X1,sK3)) )
    | ~ spl5_22 ),
    inference(forward_demodulation,[],[f194,f180])).

fof(f180,plain,(
    ! [X4] : k9_subset_1(u1_struct_0(sK0),X4,sK3) = k3_xboole_0(X4,sK3) ),
    inference(resolution,[],[f40,f56])).

fof(f40,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f194,plain,
    ( ! [X1] :
        ( k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,sK3)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X1,sK3))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl5_22
  <=> ! [X1] :
        ( k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,sK3)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X1,sK3))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f1790,plain,
    ( r2_hidden(sK1,k3_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3)))
    | ~ spl5_14
    | ~ spl5_61 ),
    inference(resolution,[],[f1628,f524])).

fof(f524,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | ~ spl5_61 ),
    inference(avatar_component_clause,[],[f523])).

fof(f523,plain,
    ( spl5_61
  <=> r2_hidden(sK1,k1_tops_1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).

fof(f1628,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,X0)
        | r2_hidden(sK1,k3_xboole_0(k1_tops_1(sK0,sK2),X0)) )
    | ~ spl5_14 ),
    inference(resolution,[],[f139,f58])).

fof(f1679,plain,
    ( ! [X1] : ~ r2_hidden(sK1,k3_xboole_0(X1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3))))
    | spl5_26 ),
    inference(resolution,[],[f1672,f59])).

fof(f59,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1672,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))
    | spl5_26 ),
    inference(forward_demodulation,[],[f212,f180])).

fof(f212,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK3)))
    | spl5_26 ),
    inference(avatar_component_clause,[],[f211])).

fof(f211,plain,
    ( spl5_26
  <=> r2_hidden(sK1,k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f139,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl5_14
  <=> r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f1670,plain,
    ( spl5_3
    | ~ spl5_26 ),
    inference(avatar_contradiction_clause,[],[f1660])).

fof(f1660,plain,
    ( $false
    | spl5_3
    | ~ spl5_26 ),
    inference(unit_resulting_resolution,[],[f35,f36,f37,f38,f345,f435,f1648,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f1648,plain,
    ( ~ m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | spl5_3 ),
    inference(forward_demodulation,[],[f72,f180])).

fof(f72,plain,
    ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl5_3
  <=> m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f435,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))
    | ~ spl5_26 ),
    inference(forward_demodulation,[],[f213,f180])).

fof(f213,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK3)))
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f211])).

fof(f345,plain,(
    ! [X0] : m1_subset_1(k3_xboole_0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f336,f57])).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f336,plain,(
    ! [X5] : m1_subset_1(k3_xboole_0(X5,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f148,f147])).

fof(f147,plain,(
    ! [X4] : k9_subset_1(u1_struct_0(sK0),X4,sK2) = k3_xboole_0(X4,sK2) ),
    inference(resolution,[],[f39,f56])).

fof(f148,plain,(
    ! [X5] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X5,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f39,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f38,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f36,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f35,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f1656,plain,
    ( spl5_9
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_12
    | ~ spl5_27
    | spl5_61
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f1652,f66,f523,f216,f130,f83,f79,f102])).

fof(f102,plain,
    ( spl5_9
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f79,plain,
    ( spl5_4
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f83,plain,
    ( spl5_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f130,plain,
    ( spl5_12
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f216,plain,
    ( spl5_27
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f66,plain,
    ( spl5_2
  <=> m1_connsp_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f1652,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_2 ),
    inference(resolution,[],[f67,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f67,plain,
    ( m1_connsp_2(sK3,sK0,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f1646,plain,
    ( ~ spl5_15
    | ~ spl5_17
    | ~ spl5_28
    | spl5_61 ),
    inference(avatar_contradiction_clause,[],[f1634])).

fof(f1634,plain,
    ( $false
    | ~ spl5_15
    | ~ spl5_17
    | ~ spl5_28
    | spl5_61 ),
    inference(unit_resulting_resolution,[],[f35,f36,f37,f38,f222,f345,f1540,f46])).

fof(f1540,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))
    | ~ spl5_15
    | ~ spl5_17
    | spl5_61 ),
    inference(superposition,[],[f531,f1196])).

fof(f1196,plain,
    ( k1_tops_1(sK0,k3_xboole_0(sK2,sK3)) = k3_xboole_0(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2))
    | ~ spl5_15
    | ~ spl5_17 ),
    inference(forward_demodulation,[],[f1174,f57])).

fof(f1174,plain,
    ( k1_tops_1(sK0,k3_xboole_0(sK3,sK2)) = k3_xboole_0(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2))
    | ~ spl5_15
    | ~ spl5_17 ),
    inference(resolution,[],[f1133,f40])).

fof(f1133,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_tops_1(sK0,k3_xboole_0(X1,sK2)) = k3_xboole_0(k1_tops_1(sK0,X1),k1_tops_1(sK0,sK2)) )
    | ~ spl5_15
    | ~ spl5_17 ),
    inference(backward_demodulation,[],[f602,f261])).

fof(f261,plain,
    ( ! [X4] : k9_subset_1(u1_struct_0(sK0),X4,k1_tops_1(sK0,sK2)) = k3_xboole_0(X4,k1_tops_1(sK0,sK2))
    | ~ spl5_15 ),
    inference(resolution,[],[f153,f56])).

fof(f153,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl5_15
  <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f602,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,sK2)) = k1_tops_1(sK0,k3_xboole_0(X1,sK2)) )
    | ~ spl5_17 ),
    inference(forward_demodulation,[],[f161,f147])).

fof(f161,plain,
    ( ! [X1] :
        ( k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,sK2)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X1,sK2))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl5_17
  <=> ! [X1] :
        ( k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,sK2)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X1,sK2))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f531,plain,
    ( ! [X0] : ~ r2_hidden(sK1,k3_xboole_0(k1_tops_1(sK0,sK3),X0))
    | spl5_61 ),
    inference(resolution,[],[f525,f60])).

fof(f60,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f525,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | spl5_61 ),
    inference(avatar_component_clause,[],[f523])).

fof(f222,plain,
    ( m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f220])).

fof(f220,plain,
    ( spl5_28
  <=> m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f1623,plain,
    ( spl5_9
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_12
    | ~ spl5_13
    | spl5_14
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f1619,f62,f138,f134,f130,f83,f79,f102])).

fof(f134,plain,
    ( spl5_13
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f62,plain,
    ( spl5_1
  <=> m1_connsp_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f1619,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_1 ),
    inference(resolution,[],[f63,f46])).

fof(f63,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f1615,plain,
    ( ~ spl5_14
    | spl5_1
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f518,f168,f62,f138])).

fof(f168,plain,
    ( spl5_19
  <=> ! [X3] :
        ( m1_connsp_2(sK2,sK0,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_hidden(X3,k1_tops_1(sK0,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f518,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ spl5_19 ),
    inference(resolution,[],[f169,f38])).

fof(f169,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | m1_connsp_2(sK2,sK0,X3)
        | ~ r2_hidden(X3,k1_tops_1(sK0,sK2)) )
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f168])).

fof(f1613,plain,
    ( spl5_14
    | ~ spl5_15
    | ~ spl5_17
    | ~ spl5_28 ),
    inference(avatar_contradiction_clause,[],[f1601])).

fof(f1601,plain,
    ( $false
    | spl5_14
    | ~ spl5_15
    | ~ spl5_17
    | ~ spl5_28 ),
    inference(unit_resulting_resolution,[],[f35,f36,f37,f38,f222,f345,f1544,f46])).

fof(f1544,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))
    | spl5_14
    | ~ spl5_15
    | ~ spl5_17 ),
    inference(superposition,[],[f238,f1196])).

fof(f238,plain,
    ( ! [X1] : ~ r2_hidden(sK1,k3_xboole_0(X1,k1_tops_1(sK0,sK2)))
    | spl5_14 ),
    inference(resolution,[],[f140,f59])).

fof(f140,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | spl5_14 ),
    inference(avatar_component_clause,[],[f138])).

fof(f526,plain,
    ( ~ spl5_61
    | spl5_2
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f521,f201,f66,f523])).

fof(f201,plain,
    ( spl5_24
  <=> ! [X3] :
        ( m1_connsp_2(sK3,sK0,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_hidden(X3,k1_tops_1(sK0,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f521,plain,
    ( m1_connsp_2(sK3,sK0,sK1)
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | ~ spl5_24 ),
    inference(resolution,[],[f202,f38])).

fof(f202,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | m1_connsp_2(sK3,sK0,X3)
        | ~ r2_hidden(X3,k1_tops_1(sK0,sK3)) )
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f201])).

fof(f242,plain,(
    spl5_27 ),
    inference(avatar_contradiction_clause,[],[f239])).

fof(f239,plain,
    ( $false
    | spl5_27 ),
    inference(unit_resulting_resolution,[],[f40,f218])).

fof(f218,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_27 ),
    inference(avatar_component_clause,[],[f216])).

fof(f235,plain,(
    spl5_13 ),
    inference(avatar_contradiction_clause,[],[f232])).

fof(f232,plain,
    ( $false
    | spl5_13 ),
    inference(unit_resulting_resolution,[],[f39,f136])).

fof(f136,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_13 ),
    inference(avatar_component_clause,[],[f134])).

fof(f231,plain,(
    spl5_12 ),
    inference(avatar_contradiction_clause,[],[f228])).

fof(f228,plain,
    ( $false
    | spl5_12 ),
    inference(unit_resulting_resolution,[],[f38,f132])).

fof(f132,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl5_12 ),
    inference(avatar_component_clause,[],[f130])).

fof(f227,plain,(
    ~ spl5_9 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | ~ spl5_9 ),
    inference(unit_resulting_resolution,[],[f35,f104])).

fof(f104,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f102])).

fof(f223,plain,
    ( ~ spl5_27
    | spl5_28
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f205,f70,f220,f216])).

fof(f205,plain,
    ( m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_3 ),
    inference(superposition,[],[f71,f56])).

fof(f71,plain,
    ( m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f203,plain,
    ( spl5_9
    | ~ spl5_4
    | ~ spl5_5
    | spl5_24 ),
    inference(avatar_split_clause,[],[f179,f201,f83,f79,f102])).

fof(f179,plain,(
    ! [X3] :
      ( m1_connsp_2(sK3,sK0,X3)
      | ~ r2_hidden(X3,k1_tops_1(sK0,sK3))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f40,f47])).

fof(f195,plain,
    ( ~ spl5_4
    | ~ spl5_5
    | spl5_22 ),
    inference(avatar_split_clause,[],[f177,f193,f83,f79])).

fof(f177,plain,(
    ! [X1] :
      ( k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,sK3)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X1,sK3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f40,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tops_1)).

fof(f187,plain,
    ( ~ spl5_5
    | spl5_20 ),
    inference(avatar_split_clause,[],[f175,f184,f83])).

fof(f175,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f40,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f174,plain,(
    spl5_5 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | spl5_5 ),
    inference(unit_resulting_resolution,[],[f37,f85])).

fof(f85,plain,
    ( ~ l1_pre_topc(sK0)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f83])).

fof(f170,plain,
    ( spl5_9
    | ~ spl5_4
    | ~ spl5_5
    | spl5_19 ),
    inference(avatar_split_clause,[],[f146,f168,f83,f79,f102])).

fof(f146,plain,(
    ! [X3] :
      ( m1_connsp_2(sK2,sK0,X3)
      | ~ r2_hidden(X3,k1_tops_1(sK0,sK2))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f39,f47])).

fof(f162,plain,
    ( ~ spl5_4
    | ~ spl5_5
    | spl5_17 ),
    inference(avatar_split_clause,[],[f144,f160,f83,f79])).

fof(f144,plain,(
    ! [X1] :
      ( k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,sK2)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X1,sK2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f39,f48])).

fof(f154,plain,
    ( ~ spl5_5
    | spl5_15 ),
    inference(avatar_split_clause,[],[f142,f151,f83])).

fof(f142,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f39,f55])).

fof(f127,plain,(
    spl5_4 ),
    inference(avatar_contradiction_clause,[],[f124])).

fof(f124,plain,
    ( $false
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f36,f81])).

fof(f81,plain,
    ( ~ v2_pre_topc(sK0)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f75,plain,
    ( spl5_1
    | spl5_3 ),
    inference(avatar_split_clause,[],[f41,f70,f62])).

fof(f41,plain,
    ( m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f74,plain,
    ( spl5_2
    | spl5_3 ),
    inference(avatar_split_clause,[],[f42,f70,f66])).

fof(f42,plain,
    ( m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)
    | m1_connsp_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f73,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f43,f70,f66,f62])).

fof(f43,plain,
    ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)
    | ~ m1_connsp_2(sK3,sK0,sK1)
    | ~ m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

%------------------------------------------------------------------------------
