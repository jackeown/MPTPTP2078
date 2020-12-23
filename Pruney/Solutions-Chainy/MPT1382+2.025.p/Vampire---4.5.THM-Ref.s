%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:02 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 494 expanded)
%              Number of leaves         :   16 ( 172 expanded)
%              Depth                    :   17
%              Number of atoms          :  480 (4271 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f361,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f187,f201,f312,f340,f356])).

fof(f356,plain,
    ( ~ spl3_4
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(avatar_contradiction_clause,[],[f355])).

fof(f355,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f354,f37])).

fof(f37,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ! [X3] :
        ( ~ r1_tarski(X3,sK2)
        | ~ v3_pre_topc(X3,sK0)
        | ~ m1_connsp_2(X3,sK0,sK1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X3) )
    & m1_connsp_2(sK2,sK0,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f30,f29,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( ~ r1_tarski(X3,X2)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_connsp_2(X3,X0,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    | v1_xboole_0(X3) )
                & m1_connsp_2(X2,X0,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,sK0)
                  | ~ m1_connsp_2(X3,sK0,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
                  | v1_xboole_0(X3) )
              & m1_connsp_2(X2,sK0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X3,X2)
                | ~ v3_pre_topc(X3,sK0)
                | ~ m1_connsp_2(X3,sK0,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
                | v1_xboole_0(X3) )
            & m1_connsp_2(X2,sK0,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X3,X2)
              | ~ v3_pre_topc(X3,sK0)
              | ~ m1_connsp_2(X3,sK0,sK1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
              | v1_xboole_0(X3) )
          & m1_connsp_2(X2,sK0,sK1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X2] :
        ( ! [X3] :
            ( ~ r1_tarski(X3,X2)
            | ~ v3_pre_topc(X3,sK0)
            | ~ m1_connsp_2(X3,sK0,sK1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
            | v1_xboole_0(X3) )
        & m1_connsp_2(X2,sK0,sK1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ! [X3] :
          ( ~ r1_tarski(X3,sK2)
          | ~ v3_pre_topc(X3,sK0)
          | ~ m1_connsp_2(X3,sK0,sK1)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
          | v1_xboole_0(X3) )
      & m1_connsp_2(sK2,sK0,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_connsp_2(X3,X0,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  | v1_xboole_0(X3) )
              & m1_connsp_2(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_connsp_2(X3,X0,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  | v1_xboole_0(X3) )
              & m1_connsp_2(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                          & ~ v1_xboole_0(X3) )
                       => ~ ( r1_tarski(X3,X2)
                            & v3_pre_topc(X3,X0)
                            & m1_connsp_2(X3,X0,X1) ) )
                    & m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & ~ v1_xboole_0(X3) )
                     => ~ ( r1_tarski(X3,X2)
                          & v3_pre_topc(X3,X0)
                          & m1_connsp_2(X3,X0,X1) ) )
                  & m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_connsp_2)).

fof(f354,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f353,f182])).

fof(f182,plain,
    ( v1_xboole_0(k1_tops_1(sK0,sK2))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl3_9
  <=> v1_xboole_0(k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f353,plain,
    ( ~ v1_xboole_0(k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl3_4
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f352,f82])).

fof(f82,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl3_4
  <=> r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f352,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | ~ v1_xboole_0(k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f351,f34])).

fof(f34,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f351,plain,
    ( v2_struct_0(sK0)
    | ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | ~ v1_xboole_0(k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f350,f35])).

fof(f35,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f350,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | ~ v1_xboole_0(k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f348,f36])).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f348,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | ~ v1_xboole_0(k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl3_14 ),
    inference(resolution,[],[f306,f211])).

fof(f211,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X2,X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ r1_tarski(X2,u1_struct_0(X1))
      | ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f202])).

fof(f202,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ r1_tarski(X2,u1_struct_0(X1))
      | ~ v1_xboole_0(X2)
      | ~ m1_connsp_2(X2,X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ r1_tarski(X2,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f167,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f41,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

% (24663)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
fof(f167,plain,(
    ! [X10,X8,X7,X9] :
      ( ~ r1_tarski(k1_tops_1(X8,X7),X10)
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ r1_tarski(X7,u1_struct_0(X8))
      | ~ v1_xboole_0(X10)
      | ~ m1_connsp_2(X7,X8,X9) ) ),
    inference(resolution,[],[f110,f57])).

fof(f57,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_hidden(X2,X3)
      | ~ v1_xboole_0(X1)
      | ~ r1_tarski(X3,X1) ) ),
    inference(resolution,[],[f51,f48])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f110,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,k1_tops_1(X2,X1))
      | ~ m1_connsp_2(X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ r1_tarski(X1,u1_struct_0(X2)) ) ),
    inference(resolution,[],[f42,f48])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f306,plain,
    ( m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f305])).

fof(f305,plain,
    ( spl3_14
  <=> m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f340,plain,
    ( ~ spl3_10
    | spl3_14 ),
    inference(avatar_contradiction_clause,[],[f339])).

fof(f339,plain,
    ( $false
    | ~ spl3_10
    | spl3_14 ),
    inference(subsumption_resolution,[],[f338,f70])).

fof(f70,plain,(
    r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(subsumption_resolution,[],[f68,f36])).

fof(f68,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f41,f38])).

fof(f38,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f338,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl3_10
    | spl3_14 ),
    inference(subsumption_resolution,[],[f337,f185])).

fof(f185,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl3_10
  <=> r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f337,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | spl3_14 ),
    inference(subsumption_resolution,[],[f336,f87])).

fof(f87,plain,(
    v3_pre_topc(k1_tops_1(sK0,sK2),sK0) ),
    inference(subsumption_resolution,[],[f86,f35])).

fof(f86,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f84,f36])).

fof(f84,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f46,f38])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f336,plain,
    ( ~ v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | spl3_14 ),
    inference(resolution,[],[f307,f161])).

fof(f161,plain,(
    ! [X2,X1] :
      ( m1_connsp_2(X1,sK0,X2)
      | ~ v3_pre_topc(X1,sK0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_tarski(X1,sK2) ) ),
    inference(subsumption_resolution,[],[f160,f34])).

fof(f160,plain,(
    ! [X2,X1] :
      ( ~ v3_pre_topc(X1,sK0)
      | m1_connsp_2(X1,sK0,X2)
      | v2_struct_0(sK0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_tarski(X1,sK2) ) ),
    inference(subsumption_resolution,[],[f159,f35])).

fof(f159,plain,(
    ! [X2,X1] :
      ( ~ v3_pre_topc(X1,sK0)
      | m1_connsp_2(X1,sK0,X2)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_tarski(X1,sK2) ) ),
    inference(subsumption_resolution,[],[f155,f36])).

fof(f155,plain,(
    ! [X2,X1] :
      ( ~ v3_pre_topc(X1,sK0)
      | m1_connsp_2(X1,sK0,X2)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_tarski(X1,sK2) ) ),
    inference(resolution,[],[f151,f54])).

fof(f54,plain,(
    ! [X0] :
      ( r1_tarski(X0,u1_struct_0(sK0))
      | ~ r1_tarski(X0,sK2) ) ),
    inference(resolution,[],[f50,f52])).

fof(f52,plain,(
    r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f47,f38])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f151,plain,(
    ! [X2,X3,X1] :
      ( ~ r1_tarski(X2,u1_struct_0(X3))
      | ~ v3_pre_topc(X2,X3)
      | m1_connsp_2(X2,X3,X1)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ r2_hidden(X1,X2) ) ),
    inference(subsumption_resolution,[],[f138,f67])).

fof(f67,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_hidden(X1,X3)
      | m1_subset_1(X1,X2)
      | ~ r1_tarski(X3,X2) ) ),
    inference(resolution,[],[f49,f48])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f138,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_hidden(X1,X2)
      | ~ v3_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,u1_struct_0(X3))
      | m1_connsp_2(X2,X3,X1)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ r1_tarski(X2,u1_struct_0(X3)) ) ),
    inference(resolution,[],[f44,f48])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | m1_connsp_2(X1,X0,X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r2_hidden(X2,X1)
                  & v3_pre_topc(X1,X0) )
               => m1_connsp_2(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).

fof(f307,plain,
    ( ~ m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1)
    | spl3_14 ),
    inference(avatar_component_clause,[],[f305])).

fof(f312,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f311])).

fof(f311,plain,
    ( $false
    | spl3_4 ),
    inference(subsumption_resolution,[],[f310,f70])).

fof(f310,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | spl3_4 ),
    inference(resolution,[],[f81,f54])).

fof(f81,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f80])).

fof(f201,plain,(
    spl3_10 ),
    inference(avatar_contradiction_clause,[],[f200])).

fof(f200,plain,
    ( $false
    | spl3_10 ),
    inference(subsumption_resolution,[],[f199,f52])).

fof(f199,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | spl3_10 ),
    inference(subsumption_resolution,[],[f198,f34])).

fof(f198,plain,
    ( v2_struct_0(sK0)
    | ~ r1_tarski(sK2,u1_struct_0(sK0))
    | spl3_10 ),
    inference(subsumption_resolution,[],[f197,f35])).

fof(f197,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ r1_tarski(sK2,u1_struct_0(sK0))
    | spl3_10 ),
    inference(subsumption_resolution,[],[f196,f36])).

fof(f196,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ r1_tarski(sK2,u1_struct_0(sK0))
    | spl3_10 ),
    inference(subsumption_resolution,[],[f195,f37])).

fof(f195,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ r1_tarski(sK2,u1_struct_0(sK0))
    | spl3_10 ),
    inference(subsumption_resolution,[],[f191,f39])).

fof(f39,plain,(
    m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f191,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ r1_tarski(sK2,u1_struct_0(sK0))
    | spl3_10 ),
    inference(resolution,[],[f186,f110])).

fof(f186,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f184])).

fof(f187,plain,
    ( spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f178,f184,f180])).

fof(f178,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | v1_xboole_0(k1_tops_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f176,f70])).

fof(f176,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | v1_xboole_0(k1_tops_1(sK0,sK2)) ),
    inference(resolution,[],[f172,f87])).

fof(f172,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,sK0)
      | ~ r2_hidden(sK1,X0)
      | ~ r1_tarski(X0,sK2)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f169])).

fof(f169,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,sK0)
      | ~ r2_hidden(sK1,X0)
      | ~ r1_tarski(X0,sK2)
      | ~ v3_pre_topc(X0,sK0)
      | ~ r1_tarski(X0,sK2)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f161,f93])).

fof(f93,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK0,sK1)
      | ~ v3_pre_topc(X0,sK0)
      | ~ r1_tarski(X0,sK2)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f92,f54])).

fof(f92,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,sK0)
      | ~ m1_connsp_2(X0,sK0,sK1)
      | ~ r1_tarski(X0,sK2)
      | v1_xboole_0(X0)
      | ~ r1_tarski(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f40,f48])).

fof(f40,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_connsp_2(X3,sK0,sK1)
      | ~ r1_tarski(X3,sK2)
      | v1_xboole_0(X3) ) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:04:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.47  % (24669)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
% 0.22/0.48  % (24659)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.22/0.48  % (24669)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % (24655)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.22/0.48  % (24660)WARNING: option uwaf not known.
% 0.22/0.48  % (24661)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.22/0.48  % (24660)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.22/0.48  % (24652)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.22/0.48  % (24665)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f361,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f187,f201,f312,f340,f356])).
% 0.22/0.49  fof(f356,plain,(
% 0.22/0.49    ~spl3_4 | ~spl3_9 | ~spl3_14),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f355])).
% 0.22/0.49  fof(f355,plain,(
% 0.22/0.49    $false | (~spl3_4 | ~spl3_9 | ~spl3_14)),
% 0.22/0.49    inference(subsumption_resolution,[],[f354,f37])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.49    inference(cnf_transformation,[],[f31])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ((! [X3] : (~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_connsp_2(X3,sK0,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X3)) & m1_connsp_2(sK2,sK0,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f30,f29,f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_connsp_2(X3,sK0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,sK0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_connsp_2(X3,sK0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,sK0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_connsp_2(X3,sK0,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,sK0,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_connsp_2(X3,sK0,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,sK0,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (! [X3] : (~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_connsp_2(X3,sK0,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X3)) & m1_connsp_2(sK2,sK0,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : ((~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1)) | (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3))) & m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,negated_conjecture,(
% 0.22/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 0.22/0.49    inference(negated_conjecture,[],[f10])).
% 0.22/0.49  fof(f10,conjecture,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_connsp_2)).
% 0.22/0.49  fof(f354,plain,(
% 0.22/0.49    ~m1_subset_1(sK1,u1_struct_0(sK0)) | (~spl3_4 | ~spl3_9 | ~spl3_14)),
% 0.22/0.49    inference(subsumption_resolution,[],[f353,f182])).
% 0.22/0.49  fof(f182,plain,(
% 0.22/0.49    v1_xboole_0(k1_tops_1(sK0,sK2)) | ~spl3_9),
% 0.22/0.49    inference(avatar_component_clause,[],[f180])).
% 0.22/0.49  fof(f180,plain,(
% 0.22/0.49    spl3_9 <=> v1_xboole_0(k1_tops_1(sK0,sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.49  fof(f353,plain,(
% 0.22/0.49    ~v1_xboole_0(k1_tops_1(sK0,sK2)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (~spl3_4 | ~spl3_14)),
% 0.22/0.49    inference(subsumption_resolution,[],[f352,f82])).
% 0.22/0.49  fof(f82,plain,(
% 0.22/0.49    r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) | ~spl3_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f80])).
% 0.22/0.49  fof(f80,plain,(
% 0.22/0.49    spl3_4 <=> r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.49  fof(f352,plain,(
% 0.22/0.49    ~r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) | ~v1_xboole_0(k1_tops_1(sK0,sK2)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl3_14),
% 0.22/0.49    inference(subsumption_resolution,[],[f351,f34])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ~v2_struct_0(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f31])).
% 0.22/0.49  fof(f351,plain,(
% 0.22/0.49    v2_struct_0(sK0) | ~r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) | ~v1_xboole_0(k1_tops_1(sK0,sK2)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl3_14),
% 0.22/0.49    inference(subsumption_resolution,[],[f350,f35])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    v2_pre_topc(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f31])).
% 0.22/0.49  fof(f350,plain,(
% 0.22/0.49    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) | ~v1_xboole_0(k1_tops_1(sK0,sK2)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl3_14),
% 0.22/0.49    inference(subsumption_resolution,[],[f348,f36])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    l1_pre_topc(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f31])).
% 0.22/0.49  fof(f348,plain,(
% 0.22/0.49    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) | ~v1_xboole_0(k1_tops_1(sK0,sK2)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl3_14),
% 0.22/0.49    inference(resolution,[],[f306,f211])).
% 0.22/0.49  fof(f211,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_connsp_2(X2,X1,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~r1_tarski(X2,u1_struct_0(X1)) | ~v1_xboole_0(X2) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f202])).
% 0.22/0.49  fof(f202,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~r1_tarski(X2,u1_struct_0(X1)) | ~v1_xboole_0(X2) | ~m1_connsp_2(X2,X1,X0) | ~l1_pre_topc(X1) | ~r1_tarski(X2,u1_struct_0(X1))) )),
% 0.22/0.49    inference(resolution,[],[f167,f69])).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~l1_pre_topc(X0) | ~r1_tarski(X1,u1_struct_0(X0))) )),
% 0.22/0.49    inference(resolution,[],[f41,f48])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f33])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.49    inference(nnf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 0.22/0.49  % (24663)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.22/0.49  fof(f167,plain,(
% 0.22/0.49    ( ! [X10,X8,X7,X9] : (~r1_tarski(k1_tops_1(X8,X7),X10) | ~m1_subset_1(X9,u1_struct_0(X8)) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~r1_tarski(X7,u1_struct_0(X8)) | ~v1_xboole_0(X10) | ~m1_connsp_2(X7,X8,X9)) )),
% 0.22/0.49    inference(resolution,[],[f110,f57])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    ( ! [X2,X3,X1] : (~r2_hidden(X2,X3) | ~v1_xboole_0(X1) | ~r1_tarski(X3,X1)) )),
% 0.22/0.49    inference(resolution,[],[f51,f48])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.22/0.49  fof(f110,plain,(
% 0.22/0.49    ( ! [X2,X3,X1] : (r2_hidden(X3,k1_tops_1(X2,X1)) | ~m1_connsp_2(X1,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~r1_tarski(X1,u1_struct_0(X2))) )),
% 0.22/0.49    inference(resolution,[],[f42,f48])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f32])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(nnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).
% 0.22/0.49  fof(f306,plain,(
% 0.22/0.49    m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1) | ~spl3_14),
% 0.22/0.49    inference(avatar_component_clause,[],[f305])).
% 0.22/0.49  fof(f305,plain,(
% 0.22/0.49    spl3_14 <=> m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.49  fof(f340,plain,(
% 0.22/0.49    ~spl3_10 | spl3_14),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f339])).
% 0.22/0.49  fof(f339,plain,(
% 0.22/0.49    $false | (~spl3_10 | spl3_14)),
% 0.22/0.49    inference(subsumption_resolution,[],[f338,f70])).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 0.22/0.49    inference(subsumption_resolution,[],[f68,f36])).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    r1_tarski(k1_tops_1(sK0,sK2),sK2) | ~l1_pre_topc(sK0)),
% 0.22/0.49    inference(resolution,[],[f41,f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    inference(cnf_transformation,[],[f31])).
% 0.22/0.49  fof(f338,plain,(
% 0.22/0.49    ~r1_tarski(k1_tops_1(sK0,sK2),sK2) | (~spl3_10 | spl3_14)),
% 0.22/0.49    inference(subsumption_resolution,[],[f337,f185])).
% 0.22/0.49  fof(f185,plain,(
% 0.22/0.49    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~spl3_10),
% 0.22/0.49    inference(avatar_component_clause,[],[f184])).
% 0.22/0.49  fof(f184,plain,(
% 0.22/0.49    spl3_10 <=> r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.49  fof(f337,plain,(
% 0.22/0.49    ~r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~r1_tarski(k1_tops_1(sK0,sK2),sK2) | spl3_14),
% 0.22/0.49    inference(subsumption_resolution,[],[f336,f87])).
% 0.22/0.49  fof(f87,plain,(
% 0.22/0.49    v3_pre_topc(k1_tops_1(sK0,sK2),sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f86,f35])).
% 0.22/0.49  fof(f86,plain,(
% 0.22/0.49    v3_pre_topc(k1_tops_1(sK0,sK2),sK0) | ~v2_pre_topc(sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f84,f36])).
% 0.22/0.49  fof(f84,plain,(
% 0.22/0.49    v3_pre_topc(k1_tops_1(sK0,sK2),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.22/0.49    inference(resolution,[],[f46,f38])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.49    inference(flattening,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 0.22/0.49  fof(f336,plain,(
% 0.22/0.49    ~v3_pre_topc(k1_tops_1(sK0,sK2),sK0) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~r1_tarski(k1_tops_1(sK0,sK2),sK2) | spl3_14),
% 0.22/0.49    inference(resolution,[],[f307,f161])).
% 0.22/0.49  fof(f161,plain,(
% 0.22/0.49    ( ! [X2,X1] : (m1_connsp_2(X1,sK0,X2) | ~v3_pre_topc(X1,sK0) | ~r2_hidden(X2,X1) | ~r1_tarski(X1,sK2)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f160,f34])).
% 0.22/0.49  fof(f160,plain,(
% 0.22/0.49    ( ! [X2,X1] : (~v3_pre_topc(X1,sK0) | m1_connsp_2(X1,sK0,X2) | v2_struct_0(sK0) | ~r2_hidden(X2,X1) | ~r1_tarski(X1,sK2)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f159,f35])).
% 0.22/0.49  fof(f159,plain,(
% 0.22/0.49    ( ! [X2,X1] : (~v3_pre_topc(X1,sK0) | m1_connsp_2(X1,sK0,X2) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_hidden(X2,X1) | ~r1_tarski(X1,sK2)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f155,f36])).
% 0.22/0.49  fof(f155,plain,(
% 0.22/0.49    ( ! [X2,X1] : (~v3_pre_topc(X1,sK0) | m1_connsp_2(X1,sK0,X2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_hidden(X2,X1) | ~r1_tarski(X1,sK2)) )),
% 0.22/0.49    inference(resolution,[],[f151,f54])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    ( ! [X0] : (r1_tarski(X0,u1_struct_0(sK0)) | ~r1_tarski(X0,sK2)) )),
% 0.22/0.49    inference(resolution,[],[f50,f52])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    r1_tarski(sK2,u1_struct_0(sK0))),
% 0.22/0.49    inference(resolution,[],[f47,f38])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f33])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.49    inference(flattening,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.22/0.49  fof(f151,plain,(
% 0.22/0.49    ( ! [X2,X3,X1] : (~r1_tarski(X2,u1_struct_0(X3)) | ~v3_pre_topc(X2,X3) | m1_connsp_2(X2,X3,X1) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~r2_hidden(X1,X2)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f138,f67])).
% 0.22/0.49  fof(f67,plain,(
% 0.22/0.49    ( ! [X2,X3,X1] : (~r2_hidden(X1,X3) | m1_subset_1(X1,X2) | ~r1_tarski(X3,X2)) )),
% 0.22/0.49    inference(resolution,[],[f49,f48])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.49    inference(flattening,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.22/0.49  fof(f138,plain,(
% 0.22/0.49    ( ! [X2,X3,X1] : (~r2_hidden(X1,X2) | ~v3_pre_topc(X2,X3) | ~m1_subset_1(X1,u1_struct_0(X3)) | m1_connsp_2(X2,X3,X1) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~r1_tarski(X2,u1_struct_0(X3))) )),
% 0.22/0.49    inference(resolution,[],[f44,f48])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | m1_connsp_2(X1,X0,X2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).
% 0.22/0.49  fof(f307,plain,(
% 0.22/0.49    ~m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1) | spl3_14),
% 0.22/0.49    inference(avatar_component_clause,[],[f305])).
% 0.22/0.49  fof(f312,plain,(
% 0.22/0.49    spl3_4),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f311])).
% 0.22/0.49  fof(f311,plain,(
% 0.22/0.49    $false | spl3_4),
% 0.22/0.49    inference(subsumption_resolution,[],[f310,f70])).
% 0.22/0.49  fof(f310,plain,(
% 0.22/0.49    ~r1_tarski(k1_tops_1(sK0,sK2),sK2) | spl3_4),
% 0.22/0.49    inference(resolution,[],[f81,f54])).
% 0.22/0.49  fof(f81,plain,(
% 0.22/0.49    ~r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) | spl3_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f80])).
% 0.22/0.49  fof(f201,plain,(
% 0.22/0.49    spl3_10),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f200])).
% 0.22/0.49  fof(f200,plain,(
% 0.22/0.49    $false | spl3_10),
% 0.22/0.49    inference(subsumption_resolution,[],[f199,f52])).
% 0.22/0.49  fof(f199,plain,(
% 0.22/0.49    ~r1_tarski(sK2,u1_struct_0(sK0)) | spl3_10),
% 0.22/0.49    inference(subsumption_resolution,[],[f198,f34])).
% 0.22/0.49  fof(f198,plain,(
% 0.22/0.49    v2_struct_0(sK0) | ~r1_tarski(sK2,u1_struct_0(sK0)) | spl3_10),
% 0.22/0.49    inference(subsumption_resolution,[],[f197,f35])).
% 0.22/0.49  fof(f197,plain,(
% 0.22/0.49    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~r1_tarski(sK2,u1_struct_0(sK0)) | spl3_10),
% 0.22/0.49    inference(subsumption_resolution,[],[f196,f36])).
% 0.22/0.49  fof(f196,plain,(
% 0.22/0.49    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~r1_tarski(sK2,u1_struct_0(sK0)) | spl3_10),
% 0.22/0.49    inference(subsumption_resolution,[],[f195,f37])).
% 0.22/0.49  fof(f195,plain,(
% 0.22/0.49    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~r1_tarski(sK2,u1_struct_0(sK0)) | spl3_10),
% 0.22/0.49    inference(subsumption_resolution,[],[f191,f39])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    m1_connsp_2(sK2,sK0,sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f31])).
% 0.22/0.49  fof(f191,plain,(
% 0.22/0.49    ~m1_connsp_2(sK2,sK0,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~r1_tarski(sK2,u1_struct_0(sK0)) | spl3_10),
% 0.22/0.49    inference(resolution,[],[f186,f110])).
% 0.22/0.49  fof(f186,plain,(
% 0.22/0.49    ~r2_hidden(sK1,k1_tops_1(sK0,sK2)) | spl3_10),
% 0.22/0.49    inference(avatar_component_clause,[],[f184])).
% 0.22/0.49  fof(f187,plain,(
% 0.22/0.49    spl3_9 | ~spl3_10),
% 0.22/0.49    inference(avatar_split_clause,[],[f178,f184,f180])).
% 0.22/0.49  fof(f178,plain,(
% 0.22/0.49    ~r2_hidden(sK1,k1_tops_1(sK0,sK2)) | v1_xboole_0(k1_tops_1(sK0,sK2))),
% 0.22/0.49    inference(subsumption_resolution,[],[f176,f70])).
% 0.22/0.49  fof(f176,plain,(
% 0.22/0.49    ~r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~r1_tarski(k1_tops_1(sK0,sK2),sK2) | v1_xboole_0(k1_tops_1(sK0,sK2))),
% 0.22/0.49    inference(resolution,[],[f172,f87])).
% 0.22/0.49  fof(f172,plain,(
% 0.22/0.49    ( ! [X0] : (~v3_pre_topc(X0,sK0) | ~r2_hidden(sK1,X0) | ~r1_tarski(X0,sK2) | v1_xboole_0(X0)) )),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f169])).
% 0.22/0.49  fof(f169,plain,(
% 0.22/0.49    ( ! [X0] : (~v3_pre_topc(X0,sK0) | ~r2_hidden(sK1,X0) | ~r1_tarski(X0,sK2) | ~v3_pre_topc(X0,sK0) | ~r1_tarski(X0,sK2) | v1_xboole_0(X0)) )),
% 0.22/0.49    inference(resolution,[],[f161,f93])).
% 0.22/0.49  fof(f93,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_connsp_2(X0,sK0,sK1) | ~v3_pre_topc(X0,sK0) | ~r1_tarski(X0,sK2) | v1_xboole_0(X0)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f92,f54])).
% 0.22/0.49  fof(f92,plain,(
% 0.22/0.49    ( ! [X0] : (~v3_pre_topc(X0,sK0) | ~m1_connsp_2(X0,sK0,sK1) | ~r1_tarski(X0,sK2) | v1_xboole_0(X0) | ~r1_tarski(X0,u1_struct_0(sK0))) )),
% 0.22/0.49    inference(resolution,[],[f40,f48])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X3,sK0) | ~m1_connsp_2(X3,sK0,sK1) | ~r1_tarski(X3,sK2) | v1_xboole_0(X3)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f31])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (24669)------------------------------
% 0.22/0.49  % (24669)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (24669)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (24669)Memory used [KB]: 5500
% 0.22/0.49  % (24669)Time elapsed: 0.070 s
% 0.22/0.49  % (24669)------------------------------
% 0.22/0.49  % (24669)------------------------------
% 0.22/0.49  % (24657)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.22/0.49  % (24649)Success in time 0.132 s
%------------------------------------------------------------------------------
