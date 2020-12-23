%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:56 EST 2020

% Result     : Theorem 1.95s
% Output     : Refutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 254 expanded)
%              Number of leaves         :   12 (  63 expanded)
%              Depth                    :   11
%              Number of atoms          :  241 (1327 expanded)
%              Number of equality atoms :    8 (   9 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f514,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f141,f145,f182,f273,f313,f513])).

fof(f513,plain,
    ( ~ spl6_6
    | spl6_7 ),
    inference(avatar_contradiction_clause,[],[f504])).

fof(f504,plain,
    ( $false
    | ~ spl6_6
    | spl6_7 ),
    inference(unit_resulting_resolution,[],[f462,f463,f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f463,plain,
    ( ~ r2_hidden(sK5(sK2,k2_xboole_0(sK2,sK3)),k2_xboole_0(sK2,sK3))
    | ~ spl6_6
    | spl6_7 ),
    inference(unit_resulting_resolution,[],[f332,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f332,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK2,sK3))
    | ~ spl6_6
    | spl6_7 ),
    inference(unit_resulting_resolution,[],[f61,f25,f267,f272,f167])).

fof(f167,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X2,k1_tops_1(sK0,X0))
      | ~ r2_hidden(X2,k1_tops_1(sK0,X1)) ) ),
    inference(resolution,[],[f52,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f29,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

fof(f29,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_connsp_2(X2,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_connsp_2(X2,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
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
                     => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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
                   => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_connsp_2)).

fof(f272,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))
    | spl6_7 ),
    inference(avatar_component_clause,[],[f270])).

fof(f270,plain,
    ( spl6_7
  <=> r2_hidden(sK1,k1_tops_1(sK0,k2_xboole_0(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f267,plain,
    ( m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f266])).

fof(f266,plain,
    ( spl6_6
  <=> m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f25,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f61,plain,(
    r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f29,f27,f28,f22,f26,f25,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f26,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f22,plain,(
    m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f28,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f27,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f462,plain,
    ( r2_hidden(sK5(sK2,k2_xboole_0(sK2,sK3)),sK2)
    | ~ spl6_6
    | spl6_7 ),
    inference(unit_resulting_resolution,[],[f332,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f313,plain,(
    spl6_6 ),
    inference(avatar_contradiction_clause,[],[f307])).

fof(f307,plain,
    ( $false
    | spl6_6 ),
    inference(unit_resulting_resolution,[],[f287,f286,f278,f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f278,plain,
    ( r2_hidden(sK5(k2_xboole_0(sK2,sK3),u1_struct_0(sK0)),k2_xboole_0(sK2,sK3))
    | spl6_6 ),
    inference(unit_resulting_resolution,[],[f277,f44])).

fof(f277,plain,
    ( ~ r1_tarski(k2_xboole_0(sK2,sK3),u1_struct_0(sK0))
    | spl6_6 ),
    inference(unit_resulting_resolution,[],[f268,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f268,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_6 ),
    inference(avatar_component_clause,[],[f266])).

fof(f286,plain,
    ( ~ r2_hidden(sK5(k2_xboole_0(sK2,sK3),u1_struct_0(sK0)),sK3)
    | spl6_6 ),
    inference(unit_resulting_resolution,[],[f56,f279,f43])).

fof(f279,plain,
    ( ~ r2_hidden(sK5(k2_xboole_0(sK2,sK3),u1_struct_0(sK0)),u1_struct_0(sK0))
    | spl6_6 ),
    inference(unit_resulting_resolution,[],[f277,f45])).

fof(f56,plain,(
    r1_tarski(sK3,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f21,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f21,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f287,plain,
    ( ~ r2_hidden(sK5(k2_xboole_0(sK2,sK3),u1_struct_0(sK0)),sK2)
    | spl6_6 ),
    inference(unit_resulting_resolution,[],[f62,f279,f43])).

fof(f62,plain,(
    r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f25,f35])).

fof(f273,plain,
    ( ~ spl6_6
    | ~ spl6_7
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f235,f180,f270,f266])).

fof(f180,plain,
    ( spl6_4
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_connsp_2(X1,sK0,X0)
        | ~ r2_hidden(X0,k1_tops_1(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f235,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))
    | ~ m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_4 ),
    inference(resolution,[],[f195,f69])).

fof(f69,plain,(
    ~ m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1) ),
    inference(backward_demodulation,[],[f24,f65])).

fof(f65,plain,(
    k4_subset_1(u1_struct_0(sK0),sK2,sK3) = k2_xboole_0(sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f21,f25,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f24,plain,(
    ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f195,plain,
    ( ! [X0] :
        ( m1_connsp_2(X0,sK0,sK1)
        | ~ r2_hidden(sK1,k1_tops_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl6_4 ),
    inference(resolution,[],[f181,f26])).

fof(f181,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_connsp_2(X1,sK0,X0)
        | ~ r2_hidden(X0,k1_tops_1(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f180])).

fof(f182,plain,
    ( spl6_4
    | ~ spl6_2
    | spl6_3 ),
    inference(avatar_split_clause,[],[f49,f134,f130,f180])).

fof(f130,plain,
    ( spl6_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f134,plain,
    ( spl6_3
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,k1_tops_1(sK0,X1))
      | m1_connsp_2(X1,sK0,X0) ) ),
    inference(resolution,[],[f28,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f145,plain,(
    ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f142])).

fof(f142,plain,
    ( $false
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f27,f136])).

fof(f136,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f134])).

fof(f141,plain,(
    spl6_2 ),
    inference(avatar_contradiction_clause,[],[f138])).

fof(f138,plain,
    ( $false
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f29,f132])).

fof(f132,plain,
    ( ~ l1_pre_topc(sK0)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f130])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:45:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.52  % (31976)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (31967)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (31961)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (31968)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (31975)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (31984)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (31983)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.57  % (31977)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.57  % (31969)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.58  % (31960)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.58  % (31955)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.59  % (31957)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.59  % (31958)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.59  % (31956)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.70/0.59  % (31971)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.70/0.60  % (31980)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.70/0.60  % (31981)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.70/0.60  % (31954)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.70/0.60  % (31972)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.70/0.61  % (31973)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.70/0.61  % (31974)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.95/0.61  % (31965)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.95/0.62  % (31979)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.95/0.62  % (31982)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.95/0.62  % (31956)Refutation not found, incomplete strategy% (31956)------------------------------
% 1.95/0.62  % (31956)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.95/0.62  % (31956)Termination reason: Refutation not found, incomplete strategy
% 1.95/0.62  
% 1.95/0.62  % (31956)Memory used [KB]: 10874
% 1.95/0.62  % (31956)Time elapsed: 0.190 s
% 1.95/0.62  % (31956)------------------------------
% 1.95/0.62  % (31956)------------------------------
% 1.95/0.62  % (31963)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.95/0.63  % (31963)Refutation not found, incomplete strategy% (31963)------------------------------
% 1.95/0.63  % (31963)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.95/0.63  % (31963)Termination reason: Refutation not found, incomplete strategy
% 1.95/0.63  
% 1.95/0.63  % (31963)Memory used [KB]: 10746
% 1.95/0.63  % (31963)Time elapsed: 0.199 s
% 1.95/0.63  % (31963)------------------------------
% 1.95/0.63  % (31963)------------------------------
% 1.95/0.63  % (31978)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.95/0.63  % (31964)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.95/0.64  % (31966)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.95/0.64  % (31965)Refutation not found, incomplete strategy% (31965)------------------------------
% 1.95/0.64  % (31965)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.95/0.64  % (31965)Termination reason: Refutation not found, incomplete strategy
% 1.95/0.64  
% 1.95/0.64  % (31965)Memory used [KB]: 10746
% 1.95/0.64  % (31965)Time elapsed: 0.192 s
% 1.95/0.64  % (31965)------------------------------
% 1.95/0.64  % (31965)------------------------------
% 1.95/0.64  % (31966)Refutation not found, incomplete strategy% (31966)------------------------------
% 1.95/0.64  % (31966)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.95/0.64  % (31966)Termination reason: Refutation not found, incomplete strategy
% 1.95/0.64  
% 1.95/0.64  % (31966)Memory used [KB]: 10746
% 1.95/0.64  % (31966)Time elapsed: 0.212 s
% 1.95/0.64  % (31966)------------------------------
% 1.95/0.64  % (31966)------------------------------
% 1.95/0.64  % (31962)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.95/0.65  % (31970)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.95/0.65  % (31958)Refutation found. Thanks to Tanya!
% 1.95/0.65  % SZS status Theorem for theBenchmark
% 1.95/0.65  % SZS output start Proof for theBenchmark
% 1.95/0.65  fof(f514,plain,(
% 1.95/0.65    $false),
% 1.95/0.65    inference(avatar_sat_refutation,[],[f141,f145,f182,f273,f313,f513])).
% 1.95/0.65  fof(f513,plain,(
% 1.95/0.65    ~spl6_6 | spl6_7),
% 1.95/0.65    inference(avatar_contradiction_clause,[],[f504])).
% 1.95/0.65  fof(f504,plain,(
% 1.95/0.65    $false | (~spl6_6 | spl6_7)),
% 1.95/0.65    inference(unit_resulting_resolution,[],[f462,f463,f47])).
% 1.95/0.65  fof(f47,plain,(
% 1.95/0.65    ( ! [X0,X3,X1] : (r2_hidden(X3,k2_xboole_0(X0,X1)) | ~r2_hidden(X3,X0)) )),
% 1.95/0.65    inference(equality_resolution,[],[f41])).
% 1.95/0.65  fof(f41,plain,(
% 1.95/0.65    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.95/0.65    inference(cnf_transformation,[],[f2])).
% 1.95/0.65  fof(f2,axiom,(
% 1.95/0.65    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.95/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.95/0.65  fof(f463,plain,(
% 1.95/0.65    ~r2_hidden(sK5(sK2,k2_xboole_0(sK2,sK3)),k2_xboole_0(sK2,sK3)) | (~spl6_6 | spl6_7)),
% 1.95/0.65    inference(unit_resulting_resolution,[],[f332,f45])).
% 1.95/0.65  fof(f45,plain,(
% 1.95/0.65    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK5(X0,X1),X1)) )),
% 1.95/0.65    inference(cnf_transformation,[],[f20])).
% 1.95/0.65  fof(f20,plain,(
% 1.95/0.65    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.95/0.65    inference(ennf_transformation,[],[f1])).
% 1.95/0.65  fof(f1,axiom,(
% 1.95/0.65    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.95/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.95/0.65  fof(f332,plain,(
% 1.95/0.65    ~r1_tarski(sK2,k2_xboole_0(sK2,sK3)) | (~spl6_6 | spl6_7)),
% 1.95/0.65    inference(unit_resulting_resolution,[],[f61,f25,f267,f272,f167])).
% 1.95/0.65  fof(f167,plain,(
% 1.95/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X2,k1_tops_1(sK0,X0)) | ~r2_hidden(X2,k1_tops_1(sK0,X1))) )),
% 1.95/0.65    inference(resolution,[],[f52,f43])).
% 1.95/0.65  fof(f43,plain,(
% 1.95/0.65    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.95/0.65    inference(cnf_transformation,[],[f20])).
% 1.95/0.65  fof(f52,plain,(
% 1.95/0.65    ( ! [X0,X1] : (r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.95/0.65    inference(resolution,[],[f29,f36])).
% 2.34/0.67  fof(f36,plain,(
% 2.34/0.67    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))) )),
% 2.34/0.67    inference(cnf_transformation,[],[f19])).
% 2.34/0.67  fof(f19,plain,(
% 2.34/0.67    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.34/0.67    inference(flattening,[],[f18])).
% 2.34/0.67  fof(f18,plain,(
% 2.34/0.67    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.34/0.67    inference(ennf_transformation,[],[f5])).
% 2.34/0.67  fof(f5,axiom,(
% 2.34/0.67    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 2.34/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).
% 2.34/0.67  fof(f29,plain,(
% 2.34/0.67    l1_pre_topc(sK0)),
% 2.34/0.67    inference(cnf_transformation,[],[f11])).
% 2.34/0.67  fof(f11,plain,(
% 2.34/0.67    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.34/0.67    inference(flattening,[],[f10])).
% 2.34/0.67  fof(f10,plain,(
% 2.34/0.67    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & (m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.34/0.67    inference(ennf_transformation,[],[f9])).
% 2.34/0.67  fof(f9,negated_conjecture,(
% 2.34/0.67    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1))))))),
% 2.34/0.67    inference(negated_conjecture,[],[f8])).
% 2.34/0.67  fof(f8,conjecture,(
% 2.34/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1))))))),
% 2.34/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_connsp_2)).
% 2.34/0.67  fof(f272,plain,(
% 2.34/0.67    ~r2_hidden(sK1,k1_tops_1(sK0,k2_xboole_0(sK2,sK3))) | spl6_7),
% 2.34/0.67    inference(avatar_component_clause,[],[f270])).
% 2.34/0.67  fof(f270,plain,(
% 2.34/0.67    spl6_7 <=> r2_hidden(sK1,k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))),
% 2.34/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 2.34/0.67  fof(f267,plain,(
% 2.34/0.67    m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_6),
% 2.34/0.67    inference(avatar_component_clause,[],[f266])).
% 2.34/0.67  fof(f266,plain,(
% 2.34/0.67    spl6_6 <=> m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.34/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 2.34/0.67  fof(f25,plain,(
% 2.34/0.67    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.34/0.67    inference(cnf_transformation,[],[f11])).
% 2.34/0.67  fof(f61,plain,(
% 2.34/0.67    r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 2.34/0.67    inference(unit_resulting_resolution,[],[f29,f27,f28,f22,f26,f25,f33])).
% 2.34/0.67  fof(f33,plain,(
% 2.34/0.67    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1)) )),
% 2.34/0.67    inference(cnf_transformation,[],[f17])).
% 2.34/0.67  fof(f17,plain,(
% 2.34/0.67    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.34/0.67    inference(flattening,[],[f16])).
% 2.34/0.67  fof(f16,plain,(
% 2.34/0.67    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.34/0.67    inference(ennf_transformation,[],[f6])).
% 2.34/0.67  fof(f6,axiom,(
% 2.34/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 2.34/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).
% 2.34/0.67  fof(f26,plain,(
% 2.34/0.67    m1_subset_1(sK1,u1_struct_0(sK0))),
% 2.34/0.67    inference(cnf_transformation,[],[f11])).
% 2.34/0.67  fof(f22,plain,(
% 2.34/0.67    m1_connsp_2(sK2,sK0,sK1)),
% 2.34/0.67    inference(cnf_transformation,[],[f11])).
% 2.34/0.67  fof(f28,plain,(
% 2.34/0.67    v2_pre_topc(sK0)),
% 2.34/0.67    inference(cnf_transformation,[],[f11])).
% 2.34/0.67  fof(f27,plain,(
% 2.34/0.67    ~v2_struct_0(sK0)),
% 2.34/0.67    inference(cnf_transformation,[],[f11])).
% 2.34/0.67  fof(f462,plain,(
% 2.34/0.67    r2_hidden(sK5(sK2,k2_xboole_0(sK2,sK3)),sK2) | (~spl6_6 | spl6_7)),
% 2.34/0.67    inference(unit_resulting_resolution,[],[f332,f44])).
% 2.34/0.67  fof(f44,plain,(
% 2.34/0.67    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.34/0.67    inference(cnf_transformation,[],[f20])).
% 2.34/0.67  fof(f313,plain,(
% 2.34/0.67    spl6_6),
% 2.34/0.67    inference(avatar_contradiction_clause,[],[f307])).
% 2.34/0.67  fof(f307,plain,(
% 2.34/0.67    $false | spl6_6),
% 2.34/0.67    inference(unit_resulting_resolution,[],[f287,f286,f278,f48])).
% 2.34/0.67  fof(f48,plain,(
% 2.34/0.67    ( ! [X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,k2_xboole_0(X0,X1))) )),
% 2.34/0.67    inference(equality_resolution,[],[f40])).
% 2.34/0.67  fof(f40,plain,(
% 2.34/0.67    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 2.34/0.67    inference(cnf_transformation,[],[f2])).
% 2.34/0.67  fof(f278,plain,(
% 2.34/0.67    r2_hidden(sK5(k2_xboole_0(sK2,sK3),u1_struct_0(sK0)),k2_xboole_0(sK2,sK3)) | spl6_6),
% 2.34/0.67    inference(unit_resulting_resolution,[],[f277,f44])).
% 2.34/0.67  fof(f277,plain,(
% 2.34/0.67    ~r1_tarski(k2_xboole_0(sK2,sK3),u1_struct_0(sK0)) | spl6_6),
% 2.34/0.67    inference(unit_resulting_resolution,[],[f268,f34])).
% 2.34/0.67  fof(f34,plain,(
% 2.34/0.67    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.34/0.67    inference(cnf_transformation,[],[f4])).
% 2.34/0.67  fof(f4,axiom,(
% 2.34/0.67    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.34/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.34/0.67  fof(f268,plain,(
% 2.34/0.67    ~m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | spl6_6),
% 2.34/0.67    inference(avatar_component_clause,[],[f266])).
% 2.34/0.67  fof(f286,plain,(
% 2.34/0.67    ~r2_hidden(sK5(k2_xboole_0(sK2,sK3),u1_struct_0(sK0)),sK3) | spl6_6),
% 2.34/0.67    inference(unit_resulting_resolution,[],[f56,f279,f43])).
% 2.34/0.67  fof(f279,plain,(
% 2.34/0.67    ~r2_hidden(sK5(k2_xboole_0(sK2,sK3),u1_struct_0(sK0)),u1_struct_0(sK0)) | spl6_6),
% 2.34/0.67    inference(unit_resulting_resolution,[],[f277,f45])).
% 2.34/0.67  fof(f56,plain,(
% 2.34/0.67    r1_tarski(sK3,u1_struct_0(sK0))),
% 2.34/0.67    inference(unit_resulting_resolution,[],[f21,f35])).
% 2.34/0.67  fof(f35,plain,(
% 2.34/0.67    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.34/0.67    inference(cnf_transformation,[],[f4])).
% 2.34/0.67  fof(f21,plain,(
% 2.34/0.67    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.34/0.67    inference(cnf_transformation,[],[f11])).
% 2.34/0.67  fof(f287,plain,(
% 2.34/0.67    ~r2_hidden(sK5(k2_xboole_0(sK2,sK3),u1_struct_0(sK0)),sK2) | spl6_6),
% 2.34/0.67    inference(unit_resulting_resolution,[],[f62,f279,f43])).
% 2.34/0.67  fof(f62,plain,(
% 2.34/0.67    r1_tarski(sK2,u1_struct_0(sK0))),
% 2.34/0.67    inference(unit_resulting_resolution,[],[f25,f35])).
% 2.34/0.67  fof(f273,plain,(
% 2.34/0.67    ~spl6_6 | ~spl6_7 | ~spl6_4),
% 2.34/0.67    inference(avatar_split_clause,[],[f235,f180,f270,f266])).
% 2.34/0.67  fof(f180,plain,(
% 2.34/0.67    spl6_4 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | m1_connsp_2(X1,sK0,X0) | ~r2_hidden(X0,k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.34/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 2.34/0.67  fof(f235,plain,(
% 2.34/0.67    ~r2_hidden(sK1,k1_tops_1(sK0,k2_xboole_0(sK2,sK3))) | ~m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_4),
% 2.34/0.67    inference(resolution,[],[f195,f69])).
% 2.34/0.67  fof(f69,plain,(
% 2.34/0.67    ~m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1)),
% 2.34/0.67    inference(backward_demodulation,[],[f24,f65])).
% 2.34/0.67  fof(f65,plain,(
% 2.34/0.67    k4_subset_1(u1_struct_0(sK0),sK2,sK3) = k2_xboole_0(sK2,sK3)),
% 2.34/0.67    inference(unit_resulting_resolution,[],[f21,f25,f30])).
% 2.34/0.67  fof(f30,plain,(
% 2.34/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)) )),
% 2.34/0.67    inference(cnf_transformation,[],[f13])).
% 2.34/0.67  fof(f13,plain,(
% 2.34/0.67    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.34/0.67    inference(flattening,[],[f12])).
% 2.34/0.67  fof(f12,plain,(
% 2.34/0.67    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.34/0.67    inference(ennf_transformation,[],[f3])).
% 2.34/0.67  fof(f3,axiom,(
% 2.34/0.67    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 2.34/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.34/0.67  fof(f24,plain,(
% 2.34/0.67    ~m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)),
% 2.34/0.67    inference(cnf_transformation,[],[f11])).
% 2.34/0.67  fof(f195,plain,(
% 2.34/0.67    ( ! [X0] : (m1_connsp_2(X0,sK0,sK1) | ~r2_hidden(sK1,k1_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl6_4),
% 2.34/0.67    inference(resolution,[],[f181,f26])).
% 2.34/0.67  fof(f181,plain,(
% 2.34/0.67    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | m1_connsp_2(X1,sK0,X0) | ~r2_hidden(X0,k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl6_4),
% 2.34/0.67    inference(avatar_component_clause,[],[f180])).
% 2.34/0.67  fof(f182,plain,(
% 2.34/0.67    spl6_4 | ~spl6_2 | spl6_3),
% 2.34/0.67    inference(avatar_split_clause,[],[f49,f134,f130,f180])).
% 2.34/0.67  fof(f130,plain,(
% 2.34/0.67    spl6_2 <=> l1_pre_topc(sK0)),
% 2.34/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 2.34/0.67  fof(f134,plain,(
% 2.34/0.67    spl6_3 <=> v2_struct_0(sK0)),
% 2.34/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 2.34/0.67  fof(f49,plain,(
% 2.34/0.67    ( ! [X0,X1] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,k1_tops_1(sK0,X1)) | m1_connsp_2(X1,sK0,X0)) )),
% 2.34/0.67    inference(resolution,[],[f28,f32])).
% 2.34/0.67  fof(f32,plain,(
% 2.34/0.67    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | m1_connsp_2(X2,X0,X1)) )),
% 2.34/0.67    inference(cnf_transformation,[],[f17])).
% 2.34/0.67  fof(f145,plain,(
% 2.34/0.67    ~spl6_3),
% 2.34/0.67    inference(avatar_contradiction_clause,[],[f142])).
% 2.34/0.67  fof(f142,plain,(
% 2.34/0.67    $false | ~spl6_3),
% 2.34/0.67    inference(unit_resulting_resolution,[],[f27,f136])).
% 2.34/0.67  fof(f136,plain,(
% 2.34/0.67    v2_struct_0(sK0) | ~spl6_3),
% 2.34/0.67    inference(avatar_component_clause,[],[f134])).
% 2.34/0.67  fof(f141,plain,(
% 2.34/0.67    spl6_2),
% 2.34/0.67    inference(avatar_contradiction_clause,[],[f138])).
% 2.34/0.67  fof(f138,plain,(
% 2.34/0.67    $false | spl6_2),
% 2.34/0.67    inference(unit_resulting_resolution,[],[f29,f132])).
% 2.34/0.67  fof(f132,plain,(
% 2.34/0.67    ~l1_pre_topc(sK0) | spl6_2),
% 2.34/0.67    inference(avatar_component_clause,[],[f130])).
% 2.34/0.67  % SZS output end Proof for theBenchmark
% 2.34/0.67  % (31958)------------------------------
% 2.34/0.67  % (31958)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.34/0.67  % (31958)Termination reason: Refutation
% 2.34/0.67  
% 2.34/0.67  % (31958)Memory used [KB]: 6780
% 2.34/0.67  % (31958)Time elapsed: 0.230 s
% 2.34/0.67  % (31958)------------------------------
% 2.34/0.67  % (31958)------------------------------
% 2.34/0.67  % (31953)Success in time 0.312 s
%------------------------------------------------------------------------------
