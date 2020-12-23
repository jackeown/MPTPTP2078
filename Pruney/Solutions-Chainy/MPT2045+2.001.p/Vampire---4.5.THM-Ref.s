%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  166 (1970 expanded)
%              Number of leaves         :   25 ( 618 expanded)
%              Depth                    :   22
%              Number of atoms          :  744 (15057 expanded)
%              Number of equality atoms :    6 ( 137 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f275,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f124,f125,f226,f274])).

fof(f274,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_contradiction_clause,[],[f273])).

fof(f273,plain,
    ( $false
    | ~ spl8_1
    | spl8_2 ),
    inference(subsumption_resolution,[],[f267,f261])).

fof(f261,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK6(k1_yellow19(sK0,sK1),sK2)),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f255,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f255,plain,
    ( r1_tarski(k1_tops_1(sK0,sK6(k1_yellow19(sK0,sK1),sK2)),k2_struct_0(sK0))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f242,f239,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f239,plain,
    ( r1_tarski(k1_tops_1(sK0,sK6(k1_yellow19(sK0,sK1),sK2)),sK6(k1_yellow19(sK0,sK1),sK2))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f235,f179])).

fof(f179,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | r1_tarski(k1_tops_1(sK0,X0),X0) ) ),
    inference(subsumption_resolution,[],[f163,f70])).

fof(f70,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,
    ( ( ~ r1_tarski(k1_yellow19(sK0,sK1),sK2)
      | ~ r2_waybel_7(sK0,sK2,sK1) )
    & ( r1_tarski(k1_yellow19(sK0,sK1),sK2)
      | r2_waybel_7(sK0,sK2,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f48,f51,f50,f49])).

fof(f49,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r1_tarski(k1_yellow19(X0,X1),X2)
                  | ~ r2_waybel_7(X0,X2,X1) )
                & ( r1_tarski(k1_yellow19(X0,X1),X2)
                  | r2_waybel_7(X0,X2,X1) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k1_yellow19(sK0,X1),X2)
                | ~ r2_waybel_7(sK0,X2,X1) )
              & ( r1_tarski(k1_yellow19(sK0,X1),X2)
                | r2_waybel_7(sK0,X2,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
              & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(k1_yellow19(sK0,X1),X2)
              | ~ r2_waybel_7(sK0,X2,X1) )
            & ( r1_tarski(k1_yellow19(sK0,X1),X2)
              | r2_waybel_7(sK0,X2,X1) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
            & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0))) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(k1_yellow19(sK0,sK1),X2)
            | ~ r2_waybel_7(sK0,X2,sK1) )
          & ( r1_tarski(k1_yellow19(sK0,sK1),X2)
            | r2_waybel_7(sK0,X2,sK1) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
          & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X2] :
        ( ( ~ r1_tarski(k1_yellow19(sK0,sK1),X2)
          | ~ r2_waybel_7(sK0,X2,sK1) )
        & ( r1_tarski(k1_yellow19(sK0,sK1),X2)
          | r2_waybel_7(sK0,X2,sK1) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0))) )
   => ( ( ~ r1_tarski(k1_yellow19(sK0,sK1),sK2)
        | ~ r2_waybel_7(sK0,sK2,sK1) )
      & ( r1_tarski(k1_yellow19(sK0,sK1),sK2)
        | r2_waybel_7(sK0,sK2,sK1) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k1_yellow19(X0,X1),X2)
                | ~ r2_waybel_7(X0,X2,X1) )
              & ( r1_tarski(k1_yellow19(X0,X1),X2)
                | r2_waybel_7(X0,X2,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k1_yellow19(X0,X1),X2)
                | ~ r2_waybel_7(X0,X2,X1) )
              & ( r1_tarski(k1_yellow19(X0,X1),X2)
                | r2_waybel_7(X0,X2,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_waybel_7(X0,X2,X1)
              <~> r1_tarski(k1_yellow19(X0,X1),X2) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_waybel_7(X0,X2,X1)
              <~> r1_tarski(k1_yellow19(X0,X1),X2) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                  & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
               => ( r2_waybel_7(X0,X2,X1)
                <=> r1_tarski(k1_yellow19(X0,X1),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
             => ( r2_waybel_7(X0,X2,X1)
              <=> r1_tarski(k1_yellow19(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow19)).

fof(f163,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | r1_tarski(k1_tops_1(sK0,X0),X0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f81,f149])).

fof(f149,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f126,f79])).

fof(f79,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f126,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f70,f80])).

fof(f80,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f235,plain,
    ( m1_subset_1(sK6(k1_yellow19(sK0,sK1),sK2),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f132,f233,f203])).

fof(f203,plain,(
    ! [X26,X27] :
      ( ~ m1_subset_1(X27,k2_struct_0(sK0))
      | ~ m1_connsp_2(X26,sK0,X27)
      | m1_subset_1(X26,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f202,f68])).

fof(f68,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f202,plain,(
    ! [X26,X27] :
      ( m1_subset_1(X26,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_connsp_2(X26,sK0,X27)
      | ~ m1_subset_1(X27,k2_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f201,f69])).

fof(f69,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f201,plain,(
    ! [X26,X27] :
      ( m1_subset_1(X26,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_connsp_2(X26,sK0,X27)
      | ~ m1_subset_1(X27,k2_struct_0(sK0))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f176,f70])).

fof(f176,plain,(
    ! [X26,X27] :
      ( m1_subset_1(X26,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_connsp_2(X26,sK0,X27)
      | ~ m1_subset_1(X27,k2_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f98,f149])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f233,plain,
    ( m1_connsp_2(sK6(k1_yellow19(sK0,sK1),sK2),sK0,sK1)
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f132,f228,f189])).

fof(f189,plain,(
    ! [X14,X13] :
      ( ~ m1_subset_1(X13,k2_struct_0(sK0))
      | m1_connsp_2(X14,sK0,X13)
      | ~ r2_hidden(X14,k1_yellow19(sK0,X13)) ) ),
    inference(subsumption_resolution,[],[f188,f68])).

fof(f188,plain,(
    ! [X14,X13] :
      ( ~ m1_subset_1(X13,k2_struct_0(sK0))
      | m1_connsp_2(X14,sK0,X13)
      | ~ r2_hidden(X14,k1_yellow19(sK0,X13))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f187,f69])).

fof(f187,plain,(
    ! [X14,X13] :
      ( ~ m1_subset_1(X13,k2_struct_0(sK0))
      | m1_connsp_2(X14,sK0,X13)
      | ~ r2_hidden(X14,k1_yellow19(sK0,X13))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f170,f70])).

fof(f170,plain,(
    ! [X14,X13] :
      ( ~ m1_subset_1(X13,k2_struct_0(sK0))
      | m1_connsp_2(X14,sK0,X13)
      | ~ r2_hidden(X14,k1_yellow19(sK0,X13))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f85,f149])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X2,k1_yellow19(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k1_yellow19(X0,X1))
                | ~ m1_connsp_2(X2,X0,X1) )
              & ( m1_connsp_2(X2,X0,X1)
                | ~ r2_hidden(X2,k1_yellow19(X0,X1)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k1_yellow19(X0,X1))
            <=> m1_connsp_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k1_yellow19(X0,X1))
            <=> m1_connsp_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r2_hidden(X2,k1_yellow19(X0,X1))
            <=> m1_connsp_2(X2,X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow19)).

fof(f228,plain,
    ( r2_hidden(sK6(k1_yellow19(sK0,sK1),sK2),k1_yellow19(sK0,sK1))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f123,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK6(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f64,f65])).

fof(f65,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f123,plain,
    ( ~ r1_tarski(k1_yellow19(sK0,sK1),sK2)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl8_2
  <=> r1_tarski(k1_yellow19(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f132,plain,(
    m1_subset_1(sK1,k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f131,f126])).

fof(f131,plain,
    ( m1_subset_1(sK1,k2_struct_0(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(superposition,[],[f71,f79])).

fof(f71,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f52])).

fof(f242,plain,
    ( r1_tarski(sK6(k1_yellow19(sK0,sK1),sK2),k2_struct_0(sK0))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f235,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f267,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK6(k1_yellow19(sK0,sK1),sK2)),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl8_1
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f118,f240,f241,f256,f198])).

fof(f198,plain,(
    ! [X23,X21,X22] :
      ( ~ v3_pre_topc(X21,sK0)
      | r2_hidden(X21,X22)
      | ~ r2_hidden(X23,X21)
      | ~ m1_subset_1(X21,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_waybel_7(sK0,X22,X23) ) ),
    inference(subsumption_resolution,[],[f197,f69])).

fof(f197,plain,(
    ! [X23,X21,X22] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(k2_struct_0(sK0)))
      | r2_hidden(X21,X22)
      | ~ r2_hidden(X23,X21)
      | ~ v3_pre_topc(X21,sK0)
      | ~ r2_waybel_7(sK0,X22,X23)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f174,f70])).

fof(f174,plain,(
    ! [X23,X21,X22] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(k2_struct_0(sK0)))
      | r2_hidden(X21,X22)
      | ~ r2_hidden(X23,X21)
      | ~ v3_pre_topc(X21,sK0)
      | ~ r2_waybel_7(sK0,X22,X23)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(superposition,[],[f88,f149])).

fof(f88,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X2,X4)
      | ~ v3_pre_topc(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_waybel_7(X0,X1,X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_waybel_7(X0,X1,X2)
            | ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(X2,sK3(X0,X1,X2))
              & v3_pre_topc(sK3(X0,X1,X2),X0)
              & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
          & ( ! [X4] :
                ( r2_hidden(X4,X1)
                | ~ r2_hidden(X2,X4)
                | ~ v3_pre_topc(X4,X0)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_waybel_7(X0,X1,X2) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f56,f57])).

fof(f57,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r2_hidden(X2,X3)
          & v3_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(X2,sK3(X0,X1,X2))
        & v3_pre_topc(sK3(X0,X1,X2),X0)
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_waybel_7(X0,X1,X2)
            | ? [X3] :
                ( ~ r2_hidden(X3,X1)
                & r2_hidden(X2,X3)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & ( ! [X4] :
                ( r2_hidden(X4,X1)
                | ~ r2_hidden(X2,X4)
                | ~ v3_pre_topc(X4,X0)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_waybel_7(X0,X1,X2) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_waybel_7(X0,X1,X2)
            | ? [X3] :
                ( ~ r2_hidden(X3,X1)
                & r2_hidden(X2,X3)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & ( ! [X3] :
                ( r2_hidden(X3,X1)
                | ~ r2_hidden(X2,X3)
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_waybel_7(X0,X1,X2) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_waybel_7(X0,X1,X2)
        <=> ! [X3] :
              ( r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X3)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_waybel_7(X0,X1,X2)
        <=> ! [X3] :
              ( r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X3)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1,X2] :
          ( r2_waybel_7(X0,X1,X2)
        <=> ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r2_hidden(X2,X3)
                  & v3_pre_topc(X3,X0) )
               => r2_hidden(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_waybel_7)).

fof(f256,plain,
    ( ~ r2_hidden(k1_tops_1(sK0,sK6(k1_yellow19(sK0,sK1),sK2)),sK2)
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f239,f247,f114])).

fof(f114,plain,(
    ! [X4,X5,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r1_tarski(X4,X5)
      | sP7(X5,X1) ) ),
    inference(cnf_transformation,[],[f114_D])).

fof(f114_D,plain,(
    ! [X1,X5] :
      ( ! [X4] :
          ( ~ r2_hidden(X4,X1)
          | ~ r1_tarski(X4,X5) )
    <=> ~ sP7(X5,X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).

fof(f247,plain,
    ( ~ sP7(sK6(k1_yellow19(sK0,sK1),sK2),sK2)
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f108,f229,f107,f242,f115])).

fof(f115,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r1_tarski(X5,X0)
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
      | ~ sP7(X5,X1) ) ),
    inference(general_splitting,[],[f113,f114_D])).

fof(f113,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ r1_tarski(X5,X0)
      | ~ r1_tarski(X4,X5)
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) ) ),
    inference(definition_unfolding,[],[f93,f78,f78])).

fof(f78,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow_1)).

fof(f93,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ r1_tarski(X5,X0)
      | ~ r1_tarski(X4,X5)
      | ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( ( v13_waybel_0(X1,k3_yellow_1(X0))
          | ( ~ r2_hidden(sK5(X0,X1),X1)
            & r2_hidden(sK4(X0,X1),X1)
            & r1_tarski(sK5(X0,X1),X0)
            & r1_tarski(sK4(X0,X1),sK5(X0,X1)) ) )
        & ( ! [X4,X5] :
              ( r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X1)
              | ~ r1_tarski(X5,X0)
              | ~ r1_tarski(X4,X5) )
          | ~ v13_waybel_0(X1,k3_yellow_1(X0)) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f60,f61])).

fof(f61,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(X3,X1)
          & r2_hidden(X2,X1)
          & r1_tarski(X3,X0)
          & r1_tarski(X2,X3) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X1)
        & r1_tarski(sK5(X0,X1),X0)
        & r1_tarski(sK4(X0,X1),sK5(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( ( v13_waybel_0(X1,k3_yellow_1(X0))
          | ? [X2,X3] :
              ( ~ r2_hidden(X3,X1)
              & r2_hidden(X2,X1)
              & r1_tarski(X3,X0)
              & r1_tarski(X2,X3) ) )
        & ( ! [X4,X5] :
              ( r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X1)
              | ~ r1_tarski(X5,X0)
              | ~ r1_tarski(X4,X5) )
          | ~ v13_waybel_0(X1,k3_yellow_1(X0)) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( ( v13_waybel_0(X1,k3_yellow_1(X0))
          | ? [X2,X3] :
              ( ~ r2_hidden(X3,X1)
              & r2_hidden(X2,X1)
              & r1_tarski(X3,X0)
              & r1_tarski(X2,X3) ) )
        & ( ! [X2,X3] :
              ( r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1)
              | ~ r1_tarski(X3,X0)
              | ~ r1_tarski(X2,X3) )
          | ~ v13_waybel_0(X1,k3_yellow_1(X0)) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1)
            | ~ r1_tarski(X3,X0)
            | ~ r1_tarski(X2,X3) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1)
            | ~ r1_tarski(X3,X0)
            | ~ r1_tarski(X2,X3) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
     => ( v13_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( ( r2_hidden(X2,X1)
              & r1_tarski(X3,X0)
              & r1_tarski(X2,X3) )
           => r2_hidden(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_waybel_7)).

fof(f107,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
    inference(definition_unfolding,[],[f73,f78])).

fof(f73,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f52])).

fof(f229,plain,
    ( ~ r2_hidden(sK6(k1_yellow19(sK0,sK1),sK2),sK2)
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f123,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f108,plain,(
    v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f72,f78])).

fof(f72,plain,(
    v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f52])).

fof(f241,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK6(k1_yellow19(sK0,sK1),sK2)),sK0)
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f235,f205])).

fof(f205,plain,(
    ! [X30] :
      ( v3_pre_topc(k1_tops_1(sK0,X30),sK0)
      | ~ m1_subset_1(X30,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f204,f69])).

fof(f204,plain,(
    ! [X30] :
      ( ~ m1_subset_1(X30,k1_zfmisc_1(k2_struct_0(sK0)))
      | v3_pre_topc(k1_tops_1(sK0,X30),sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f178,f70])).

fof(f178,plain,(
    ! [X30] :
      ( ~ m1_subset_1(X30,k1_zfmisc_1(k2_struct_0(sK0)))
      | v3_pre_topc(k1_tops_1(sK0,X30),sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(superposition,[],[f99,f149])).

fof(f99,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f240,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK6(k1_yellow19(sK0,sK1),sK2)))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f132,f233,f235,f183])).

fof(f183,plain,(
    ! [X6,X5] :
      ( ~ m1_subset_1(X6,k2_struct_0(sK0))
      | r2_hidden(X6,k1_tops_1(sK0,X5))
      | ~ m1_connsp_2(X5,sK0,X6)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f182,f68])).

fof(f182,plain,(
    ! [X6,X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_struct_0(sK0)))
      | r2_hidden(X6,k1_tops_1(sK0,X5))
      | ~ m1_connsp_2(X5,sK0,X6)
      | ~ m1_subset_1(X6,k2_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f181,f69])).

fof(f181,plain,(
    ! [X6,X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_struct_0(sK0)))
      | r2_hidden(X6,k1_tops_1(sK0,X5))
      | ~ m1_connsp_2(X5,sK0,X6)
      | ~ m1_subset_1(X6,k2_struct_0(sK0))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f166,f70])).

fof(f166,plain,(
    ! [X6,X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_struct_0(sK0)))
      | r2_hidden(X6,k1_tops_1(sK0,X5))
      | ~ m1_connsp_2(X5,sK0,X6)
      | ~ m1_subset_1(X6,k2_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f83,f149])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f118,plain,
    ( r2_waybel_7(sK0,sK2,sK1)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl8_1
  <=> r2_waybel_7(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f226,plain,
    ( spl8_1
    | ~ spl8_2 ),
    inference(avatar_contradiction_clause,[],[f225])).

fof(f225,plain,
    ( $false
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f224,f223])).

fof(f223,plain,
    ( ~ m1_connsp_2(sK3(sK0,sK2,sK1),sK0,sK1)
    | spl8_1
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f155,f132,f192])).

fof(f192,plain,(
    ! [X15,X16] :
      ( ~ m1_subset_1(X15,k2_struct_0(sK0))
      | r2_hidden(X16,k1_yellow19(sK0,X15))
      | ~ m1_connsp_2(X16,sK0,X15) ) ),
    inference(subsumption_resolution,[],[f191,f68])).

fof(f191,plain,(
    ! [X15,X16] :
      ( ~ m1_subset_1(X15,k2_struct_0(sK0))
      | r2_hidden(X16,k1_yellow19(sK0,X15))
      | ~ m1_connsp_2(X16,sK0,X15)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f190,f69])).

fof(f190,plain,(
    ! [X15,X16] :
      ( ~ m1_subset_1(X15,k2_struct_0(sK0))
      | r2_hidden(X16,k1_yellow19(sK0,X15))
      | ~ m1_connsp_2(X16,sK0,X15)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f171,f70])).

fof(f171,plain,(
    ! [X15,X16] :
      ( ~ m1_subset_1(X15,k2_struct_0(sK0))
      | r2_hidden(X16,k1_yellow19(sK0,X15))
      | ~ m1_connsp_2(X16,sK0,X15)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f86,f149])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_yellow19(X0,X1))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f155,plain,
    ( ~ r2_hidden(sK3(sK0,sK2,sK1),k1_yellow19(sK0,sK1))
    | spl8_1
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f122,f136,f100])).

fof(f100,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f136,plain,
    ( ~ r2_hidden(sK3(sK0,sK2,sK1),sK2)
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f69,f70,f119,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f119,plain,
    ( ~ r2_waybel_7(sK0,sK2,sK1)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f117])).

fof(f122,plain,
    ( r1_tarski(k1_yellow19(sK0,sK1),sK2)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f121])).

fof(f224,plain,
    ( m1_connsp_2(sK3(sK0,sK2,sK1),sK0,sK1)
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f135,f134,f150,f196])).

fof(f196,plain,(
    ! [X17,X18] :
      ( m1_connsp_2(X17,sK0,X18)
      | ~ m1_subset_1(X17,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X18,X17)
      | ~ v3_pre_topc(X17,sK0) ) ),
    inference(subsumption_resolution,[],[f195,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f195,plain,(
    ! [X17,X18] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_connsp_2(X17,sK0,X18)
      | ~ r2_hidden(X18,X17)
      | ~ v3_pre_topc(X17,sK0)
      | ~ m1_subset_1(X18,k2_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f194,f68])).

fof(f194,plain,(
    ! [X17,X18] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_connsp_2(X17,sK0,X18)
      | ~ r2_hidden(X18,X17)
      | ~ v3_pre_topc(X17,sK0)
      | ~ m1_subset_1(X18,k2_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f193,f69])).

fof(f193,plain,(
    ! [X17,X18] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_connsp_2(X17,sK0,X18)
      | ~ r2_hidden(X18,X17)
      | ~ v3_pre_topc(X17,sK0)
      | ~ m1_subset_1(X18,k2_struct_0(sK0))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f172,f70])).

fof(f172,plain,(
    ! [X17,X18] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_connsp_2(X17,sK0,X18)
      | ~ r2_hidden(X18,X17)
      | ~ v3_pre_topc(X17,sK0)
      | ~ m1_subset_1(X18,k2_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f87,f149])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X1,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f150,plain,
    ( m1_subset_1(sK3(sK0,sK2,sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl8_1 ),
    inference(backward_demodulation,[],[f133,f149])).

fof(f133,plain,
    ( m1_subset_1(sK3(sK0,sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f69,f70,f119,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f134,plain,
    ( v3_pre_topc(sK3(sK0,sK2,sK1),sK0)
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f69,f70,f119,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | v3_pre_topc(sK3(X0,X1,X2),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f135,plain,
    ( r2_hidden(sK1,sK3(sK0,sK2,sK1))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f69,f70,f119,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | r2_hidden(X2,sK3(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f125,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f74,f121,f117])).

fof(f74,plain,
    ( r1_tarski(k1_yellow19(sK0,sK1),sK2)
    | r2_waybel_7(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f124,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f75,f121,f117])).

fof(f75,plain,
    ( ~ r1_tarski(k1_yellow19(sK0,sK1),sK2)
    | ~ r2_waybel_7(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n021.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:13:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (13175)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (13191)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (13174)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (13183)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (13172)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (13169)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (13173)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (13171)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (13178)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (13170)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (13196)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (13179)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (13177)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (13198)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (13197)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (13188)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (13193)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (13187)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (13190)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (13186)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (13189)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (13185)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (13195)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.56  % (13194)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.56  % (13182)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.56  % (13180)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (13181)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.57  % (13192)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.58  % (13184)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.58  % (13195)Refutation found. Thanks to Tanya!
% 0.21/0.58  % SZS status Theorem for theBenchmark
% 0.21/0.58  % SZS output start Proof for theBenchmark
% 0.21/0.58  fof(f275,plain,(
% 0.21/0.58    $false),
% 0.21/0.58    inference(avatar_sat_refutation,[],[f124,f125,f226,f274])).
% 0.21/0.58  fof(f274,plain,(
% 0.21/0.58    ~spl8_1 | spl8_2),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f273])).
% 0.21/0.58  fof(f273,plain,(
% 0.21/0.58    $false | (~spl8_1 | spl8_2)),
% 0.21/0.58    inference(subsumption_resolution,[],[f267,f261])).
% 0.21/0.58  fof(f261,plain,(
% 0.21/0.58    m1_subset_1(k1_tops_1(sK0,sK6(k1_yellow19(sK0,sK1),sK2)),k1_zfmisc_1(k2_struct_0(sK0))) | spl8_2),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f255,f104])).
% 0.21/0.58  fof(f104,plain,(
% 0.21/0.58    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f67])).
% 0.21/0.58  fof(f67,plain,(
% 0.21/0.58    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.58    inference(nnf_transformation,[],[f5])).
% 0.21/0.58  fof(f5,axiom,(
% 0.21/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.58  fof(f255,plain,(
% 0.21/0.58    r1_tarski(k1_tops_1(sK0,sK6(k1_yellow19(sK0,sK1),sK2)),k2_struct_0(sK0)) | spl8_2),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f242,f239,f106])).
% 0.21/0.58  fof(f106,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f46])).
% 0.21/0.58  fof(f46,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.58    inference(flattening,[],[f45])).
% 0.21/0.58  fof(f45,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.58    inference(ennf_transformation,[],[f2])).
% 0.21/0.58  fof(f2,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.58  fof(f239,plain,(
% 0.21/0.58    r1_tarski(k1_tops_1(sK0,sK6(k1_yellow19(sK0,sK1),sK2)),sK6(k1_yellow19(sK0,sK1),sK2)) | spl8_2),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f235,f179])).
% 0.21/0.58  fof(f179,plain,(
% 0.21/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,X0),X0)) )),
% 0.21/0.58    inference(subsumption_resolution,[],[f163,f70])).
% 0.21/0.58  fof(f70,plain,(
% 0.21/0.58    l1_pre_topc(sK0)),
% 0.21/0.58    inference(cnf_transformation,[],[f52])).
% 0.21/0.58  fof(f52,plain,(
% 0.21/0.58    (((~r1_tarski(k1_yellow19(sK0,sK1),sK2) | ~r2_waybel_7(sK0,sK2,sK1)) & (r1_tarski(k1_yellow19(sK0,sK1),sK2) | r2_waybel_7(sK0,sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f48,f51,f50,f49])).
% 0.21/0.58  fof(f49,plain,(
% 0.21/0.58    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k1_yellow19(X0,X1),X2) | ~r2_waybel_7(X0,X2,X1)) & (r1_tarski(k1_yellow19(X0,X1),X2) | r2_waybel_7(X0,X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r1_tarski(k1_yellow19(sK0,X1),X2) | ~r2_waybel_7(sK0,X2,X1)) & (r1_tarski(k1_yellow19(sK0,X1),X2) | r2_waybel_7(sK0,X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f50,plain,(
% 0.21/0.58    ? [X1] : (? [X2] : ((~r1_tarski(k1_yellow19(sK0,X1),X2) | ~r2_waybel_7(sK0,X2,X1)) & (r1_tarski(k1_yellow19(sK0,X1),X2) | r2_waybel_7(sK0,X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : ((~r1_tarski(k1_yellow19(sK0,sK1),X2) | ~r2_waybel_7(sK0,X2,sK1)) & (r1_tarski(k1_yellow19(sK0,sK1),X2) | r2_waybel_7(sK0,X2,sK1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f51,plain,(
% 0.21/0.58    ? [X2] : ((~r1_tarski(k1_yellow19(sK0,sK1),X2) | ~r2_waybel_7(sK0,X2,sK1)) & (r1_tarski(k1_yellow19(sK0,sK1),X2) | r2_waybel_7(sK0,X2,sK1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))) => ((~r1_tarski(k1_yellow19(sK0,sK1),sK2) | ~r2_waybel_7(sK0,sK2,sK1)) & (r1_tarski(k1_yellow19(sK0,sK1),sK2) | r2_waybel_7(sK0,sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))))),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f48,plain,(
% 0.21/0.58    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k1_yellow19(X0,X1),X2) | ~r2_waybel_7(X0,X2,X1)) & (r1_tarski(k1_yellow19(X0,X1),X2) | r2_waybel_7(X0,X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.58    inference(flattening,[],[f47])).
% 0.21/0.58  fof(f47,plain,(
% 0.21/0.58    ? [X0] : (? [X1] : (? [X2] : (((~r1_tarski(k1_yellow19(X0,X1),X2) | ~r2_waybel_7(X0,X2,X1)) & (r1_tarski(k1_yellow19(X0,X1),X2) | r2_waybel_7(X0,X2,X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.58    inference(nnf_transformation,[],[f22])).
% 0.21/0.58  fof(f22,plain,(
% 0.21/0.58    ? [X0] : (? [X1] : (? [X2] : ((r2_waybel_7(X0,X2,X1) <~> r1_tarski(k1_yellow19(X0,X1),X2)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.58    inference(flattening,[],[f21])).
% 0.21/0.58  fof(f21,plain,(
% 0.21/0.58    ? [X0] : (? [X1] : (? [X2] : ((r2_waybel_7(X0,X2,X1) <~> r1_tarski(k1_yellow19(X0,X1),X2)) & (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f20])).
% 0.21/0.58  fof(f20,negated_conjecture,(
% 0.21/0.58    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) => (r2_waybel_7(X0,X2,X1) <=> r1_tarski(k1_yellow19(X0,X1),X2)))))),
% 0.21/0.58    inference(negated_conjecture,[],[f19])).
% 0.21/0.58  fof(f19,conjecture,(
% 0.21/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) => (r2_waybel_7(X0,X2,X1) <=> r1_tarski(k1_yellow19(X0,X1),X2)))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow19)).
% 0.21/0.58  fof(f163,plain,(
% 0.21/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,X0),X0) | ~l1_pre_topc(sK0)) )),
% 0.21/0.58    inference(superposition,[],[f81,f149])).
% 0.21/0.58  fof(f149,plain,(
% 0.21/0.58    k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f126,f79])).
% 0.21/0.58  fof(f79,plain,(
% 0.21/0.58    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f23])).
% 0.21/0.58  fof(f23,plain,(
% 0.21/0.58    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.58    inference(ennf_transformation,[],[f7])).
% 0.21/0.58  fof(f7,axiom,(
% 0.21/0.58    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.58  fof(f126,plain,(
% 0.21/0.58    l1_struct_0(sK0)),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f70,f80])).
% 0.21/0.58  fof(f80,plain,(
% 0.21/0.58    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f24])).
% 0.21/0.58  fof(f24,plain,(
% 0.21/0.58    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.58    inference(ennf_transformation,[],[f8])).
% 0.21/0.58  fof(f8,axiom,(
% 0.21/0.58    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.58  fof(f81,plain,(
% 0.21/0.58    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f25])).
% 0.21/0.58  fof(f25,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.58    inference(ennf_transformation,[],[f10])).
% 0.21/0.58  fof(f10,axiom,(
% 0.21/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 0.21/0.58  fof(f235,plain,(
% 0.21/0.58    m1_subset_1(sK6(k1_yellow19(sK0,sK1),sK2),k1_zfmisc_1(k2_struct_0(sK0))) | spl8_2),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f132,f233,f203])).
% 0.21/0.58  fof(f203,plain,(
% 0.21/0.58    ( ! [X26,X27] : (~m1_subset_1(X27,k2_struct_0(sK0)) | ~m1_connsp_2(X26,sK0,X27) | m1_subset_1(X26,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.21/0.58    inference(subsumption_resolution,[],[f202,f68])).
% 0.21/0.58  fof(f68,plain,(
% 0.21/0.58    ~v2_struct_0(sK0)),
% 0.21/0.58    inference(cnf_transformation,[],[f52])).
% 0.21/0.58  fof(f202,plain,(
% 0.21/0.58    ( ! [X26,X27] : (m1_subset_1(X26,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_connsp_2(X26,sK0,X27) | ~m1_subset_1(X27,k2_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 0.21/0.58    inference(subsumption_resolution,[],[f201,f69])).
% 0.21/0.58  fof(f69,plain,(
% 0.21/0.58    v2_pre_topc(sK0)),
% 0.21/0.58    inference(cnf_transformation,[],[f52])).
% 0.21/0.58  fof(f201,plain,(
% 0.21/0.58    ( ! [X26,X27] : (m1_subset_1(X26,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_connsp_2(X26,sK0,X27) | ~m1_subset_1(X27,k2_struct_0(sK0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.58    inference(subsumption_resolution,[],[f176,f70])).
% 0.21/0.58  fof(f176,plain,(
% 0.21/0.58    ( ! [X26,X27] : (m1_subset_1(X26,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_connsp_2(X26,sK0,X27) | ~m1_subset_1(X27,k2_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.58    inference(superposition,[],[f98,f149])).
% 0.21/0.58  fof(f98,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f39])).
% 0.21/0.58  fof(f39,plain,(
% 0.21/0.58    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.58    inference(flattening,[],[f38])).
% 0.21/0.58  fof(f38,plain,(
% 0.21/0.58    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f13])).
% 0.21/0.58  fof(f13,axiom,(
% 0.21/0.58    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 0.21/0.58  fof(f233,plain,(
% 0.21/0.58    m1_connsp_2(sK6(k1_yellow19(sK0,sK1),sK2),sK0,sK1) | spl8_2),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f132,f228,f189])).
% 0.21/0.58  fof(f189,plain,(
% 0.21/0.58    ( ! [X14,X13] : (~m1_subset_1(X13,k2_struct_0(sK0)) | m1_connsp_2(X14,sK0,X13) | ~r2_hidden(X14,k1_yellow19(sK0,X13))) )),
% 0.21/0.58    inference(subsumption_resolution,[],[f188,f68])).
% 0.21/0.58  fof(f188,plain,(
% 0.21/0.58    ( ! [X14,X13] : (~m1_subset_1(X13,k2_struct_0(sK0)) | m1_connsp_2(X14,sK0,X13) | ~r2_hidden(X14,k1_yellow19(sK0,X13)) | v2_struct_0(sK0)) )),
% 0.21/0.58    inference(subsumption_resolution,[],[f187,f69])).
% 0.21/0.58  fof(f187,plain,(
% 0.21/0.58    ( ! [X14,X13] : (~m1_subset_1(X13,k2_struct_0(sK0)) | m1_connsp_2(X14,sK0,X13) | ~r2_hidden(X14,k1_yellow19(sK0,X13)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.58    inference(subsumption_resolution,[],[f170,f70])).
% 0.21/0.58  fof(f170,plain,(
% 0.21/0.58    ( ! [X14,X13] : (~m1_subset_1(X13,k2_struct_0(sK0)) | m1_connsp_2(X14,sK0,X13) | ~r2_hidden(X14,k1_yellow19(sK0,X13)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.58    inference(superposition,[],[f85,f149])).
% 0.21/0.58  fof(f85,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X2,k1_yellow19(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f54])).
% 0.21/0.58  fof(f54,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k1_yellow19(X0,X1)) | ~m1_connsp_2(X2,X0,X1)) & (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X2,k1_yellow19(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.58    inference(nnf_transformation,[],[f31])).
% 0.21/0.58  fof(f31,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,k1_yellow19(X0,X1)) <=> m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.58    inference(flattening,[],[f30])).
% 0.21/0.58  fof(f30,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,k1_yellow19(X0,X1)) <=> m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f18])).
% 0.21/0.58  fof(f18,axiom,(
% 0.21/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X2,k1_yellow19(X0,X1)) <=> m1_connsp_2(X2,X0,X1))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow19)).
% 0.21/0.58  fof(f228,plain,(
% 0.21/0.58    r2_hidden(sK6(k1_yellow19(sK0,sK1),sK2),k1_yellow19(sK0,sK1)) | spl8_2),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f123,f101])).
% 0.21/0.58  fof(f101,plain,(
% 0.21/0.58    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK6(X0,X1),X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f66])).
% 0.21/0.58  fof(f66,plain,(
% 0.21/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f64,f65])).
% 0.21/0.58  fof(f65,plain,(
% 0.21/0.58    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f64,plain,(
% 0.21/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.58    inference(rectify,[],[f63])).
% 0.21/0.58  fof(f63,plain,(
% 0.21/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.58    inference(nnf_transformation,[],[f42])).
% 0.21/0.58  fof(f42,plain,(
% 0.21/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f1])).
% 0.21/0.58  fof(f1,axiom,(
% 0.21/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.58  fof(f123,plain,(
% 0.21/0.58    ~r1_tarski(k1_yellow19(sK0,sK1),sK2) | spl8_2),
% 0.21/0.58    inference(avatar_component_clause,[],[f121])).
% 0.21/0.58  fof(f121,plain,(
% 0.21/0.58    spl8_2 <=> r1_tarski(k1_yellow19(sK0,sK1),sK2)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.58  fof(f132,plain,(
% 0.21/0.58    m1_subset_1(sK1,k2_struct_0(sK0))),
% 0.21/0.58    inference(subsumption_resolution,[],[f131,f126])).
% 0.21/0.58  fof(f131,plain,(
% 0.21/0.58    m1_subset_1(sK1,k2_struct_0(sK0)) | ~l1_struct_0(sK0)),
% 0.21/0.58    inference(superposition,[],[f71,f79])).
% 0.21/0.58  fof(f71,plain,(
% 0.21/0.58    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.58    inference(cnf_transformation,[],[f52])).
% 0.21/0.58  fof(f242,plain,(
% 0.21/0.58    r1_tarski(sK6(k1_yellow19(sK0,sK1),sK2),k2_struct_0(sK0)) | spl8_2),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f235,f103])).
% 0.21/0.58  fof(f103,plain,(
% 0.21/0.58    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f67])).
% 0.21/0.58  fof(f267,plain,(
% 0.21/0.58    ~m1_subset_1(k1_tops_1(sK0,sK6(k1_yellow19(sK0,sK1),sK2)),k1_zfmisc_1(k2_struct_0(sK0))) | (~spl8_1 | spl8_2)),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f118,f240,f241,f256,f198])).
% 0.21/0.58  fof(f198,plain,(
% 0.21/0.58    ( ! [X23,X21,X22] : (~v3_pre_topc(X21,sK0) | r2_hidden(X21,X22) | ~r2_hidden(X23,X21) | ~m1_subset_1(X21,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_waybel_7(sK0,X22,X23)) )),
% 0.21/0.58    inference(subsumption_resolution,[],[f197,f69])).
% 0.21/0.58  fof(f197,plain,(
% 0.21/0.58    ( ! [X23,X21,X22] : (~m1_subset_1(X21,k1_zfmisc_1(k2_struct_0(sK0))) | r2_hidden(X21,X22) | ~r2_hidden(X23,X21) | ~v3_pre_topc(X21,sK0) | ~r2_waybel_7(sK0,X22,X23) | ~v2_pre_topc(sK0)) )),
% 0.21/0.58    inference(subsumption_resolution,[],[f174,f70])).
% 0.21/0.58  fof(f174,plain,(
% 0.21/0.58    ( ! [X23,X21,X22] : (~m1_subset_1(X21,k1_zfmisc_1(k2_struct_0(sK0))) | r2_hidden(X21,X22) | ~r2_hidden(X23,X21) | ~v3_pre_topc(X21,sK0) | ~r2_waybel_7(sK0,X22,X23) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.58    inference(superposition,[],[f88,f149])).
% 0.21/0.58  fof(f88,plain,(
% 0.21/0.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_waybel_7(X0,X1,X2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f58])).
% 0.21/0.58  fof(f58,plain,(
% 0.21/0.58    ! [X0] : (! [X1,X2] : ((r2_waybel_7(X0,X1,X2) | (~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(X2,sK3(X0,X1,X2)) & v3_pre_topc(sK3(X0,X1,X2),X0) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r2_hidden(X4,X1) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_waybel_7(X0,X1,X2))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f56,f57])).
% 0.21/0.58  fof(f57,plain,(
% 0.21/0.58    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(X2,sK3(X0,X1,X2)) & v3_pre_topc(sK3(X0,X1,X2),X0) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f56,plain,(
% 0.21/0.58    ! [X0] : (! [X1,X2] : ((r2_waybel_7(X0,X1,X2) | ? [X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r2_hidden(X4,X1) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_waybel_7(X0,X1,X2))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.58    inference(rectify,[],[f55])).
% 0.21/0.58  fof(f55,plain,(
% 0.21/0.58    ! [X0] : (! [X1,X2] : ((r2_waybel_7(X0,X1,X2) | ? [X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_waybel_7(X0,X1,X2))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.58    inference(nnf_transformation,[],[f35])).
% 0.21/0.58  fof(f35,plain,(
% 0.21/0.58    ! [X0] : (! [X1,X2] : (r2_waybel_7(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.58    inference(flattening,[],[f34])).
% 0.21/0.58  fof(f34,plain,(
% 0.21/0.58    ! [X0] : (! [X1,X2] : (r2_waybel_7(X0,X1,X2) <=> ! [X3] : ((r2_hidden(X3,X1) | (~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f16])).
% 0.21/0.58  fof(f16,axiom,(
% 0.21/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (r2_waybel_7(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,X3) & v3_pre_topc(X3,X0)) => r2_hidden(X3,X1)))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_waybel_7)).
% 0.21/0.58  fof(f256,plain,(
% 0.21/0.58    ~r2_hidden(k1_tops_1(sK0,sK6(k1_yellow19(sK0,sK1),sK2)),sK2) | spl8_2),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f239,f247,f114])).
% 0.21/0.58  fof(f114,plain,(
% 0.21/0.58    ( ! [X4,X5,X1] : (~r2_hidden(X4,X1) | ~r1_tarski(X4,X5) | sP7(X5,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f114_D])).
% 0.21/0.58  fof(f114_D,plain,(
% 0.21/0.58    ( ! [X1,X5] : (( ! [X4] : (~r2_hidden(X4,X1) | ~r1_tarski(X4,X5)) ) <=> ~sP7(X5,X1)) )),
% 0.21/0.58    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).
% 0.21/0.58  fof(f247,plain,(
% 0.21/0.58    ~sP7(sK6(k1_yellow19(sK0,sK1),sK2),sK2) | spl8_2),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f108,f229,f107,f242,f115])).
% 0.21/0.58  fof(f115,plain,(
% 0.21/0.58    ( ! [X0,X5,X1] : (r2_hidden(X5,X1) | ~r1_tarski(X5,X0) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) | ~sP7(X5,X1)) )),
% 0.21/0.58    inference(general_splitting,[],[f113,f114_D])).
% 0.21/0.58  fof(f113,plain,(
% 0.21/0.58    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~r1_tarski(X5,X0) | ~r1_tarski(X4,X5) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))) )),
% 0.21/0.58    inference(definition_unfolding,[],[f93,f78,f78])).
% 0.21/0.58  fof(f78,plain,(
% 0.21/0.58    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f15])).
% 0.21/0.58  fof(f15,axiom,(
% 0.21/0.58    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow_1)).
% 0.21/0.58  fof(f93,plain,(
% 0.21/0.58    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~r1_tarski(X5,X0) | ~r1_tarski(X4,X5) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f62])).
% 0.21/0.58  fof(f62,plain,(
% 0.21/0.58    ! [X0,X1] : (((v13_waybel_0(X1,k3_yellow_1(X0)) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK4(X0,X1),X1) & r1_tarski(sK5(X0,X1),X0) & r1_tarski(sK4(X0,X1),sK5(X0,X1)))) & (! [X4,X5] : (r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~r1_tarski(X5,X0) | ~r1_tarski(X4,X5)) | ~v13_waybel_0(X1,k3_yellow_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 0.21/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f60,f61])).
% 0.21/0.58  fof(f61,plain,(
% 0.21/0.58    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X1) & r1_tarski(X3,X0) & r1_tarski(X2,X3)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK4(X0,X1),X1) & r1_tarski(sK5(X0,X1),X0) & r1_tarski(sK4(X0,X1),sK5(X0,X1))))),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f60,plain,(
% 0.21/0.58    ! [X0,X1] : (((v13_waybel_0(X1,k3_yellow_1(X0)) | ? [X2,X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X1) & r1_tarski(X3,X0) & r1_tarski(X2,X3))) & (! [X4,X5] : (r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~r1_tarski(X5,X0) | ~r1_tarski(X4,X5)) | ~v13_waybel_0(X1,k3_yellow_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 0.21/0.58    inference(rectify,[],[f59])).
% 0.21/0.58  fof(f59,plain,(
% 0.21/0.58    ! [X0,X1] : (((v13_waybel_0(X1,k3_yellow_1(X0)) | ? [X2,X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X1) & r1_tarski(X3,X0) & r1_tarski(X2,X3))) & (! [X2,X3] : (r2_hidden(X3,X1) | ~r2_hidden(X2,X1) | ~r1_tarski(X3,X0) | ~r1_tarski(X2,X3)) | ~v13_waybel_0(X1,k3_yellow_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 0.21/0.58    inference(nnf_transformation,[],[f37])).
% 0.21/0.58  fof(f37,plain,(
% 0.21/0.58    ! [X0,X1] : ((v13_waybel_0(X1,k3_yellow_1(X0)) <=> ! [X2,X3] : (r2_hidden(X3,X1) | ~r2_hidden(X2,X1) | ~r1_tarski(X3,X0) | ~r1_tarski(X2,X3))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 0.21/0.58    inference(flattening,[],[f36])).
% 0.21/0.58  fof(f36,plain,(
% 0.21/0.58    ! [X0,X1] : ((v13_waybel_0(X1,k3_yellow_1(X0)) <=> ! [X2,X3] : (r2_hidden(X3,X1) | (~r2_hidden(X2,X1) | ~r1_tarski(X3,X0) | ~r1_tarski(X2,X3)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 0.21/0.58    inference(ennf_transformation,[],[f17])).
% 0.21/0.58  fof(f17,axiom,(
% 0.21/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) => (v13_waybel_0(X1,k3_yellow_1(X0)) <=> ! [X2,X3] : ((r2_hidden(X2,X1) & r1_tarski(X3,X0) & r1_tarski(X2,X3)) => r2_hidden(X3,X1))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_waybel_7)).
% 0.21/0.58  fof(f107,plain,(
% 0.21/0.58    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))),
% 0.21/0.58    inference(definition_unfolding,[],[f73,f78])).
% 0.21/0.58  fof(f73,plain,(
% 0.21/0.58    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 0.21/0.58    inference(cnf_transformation,[],[f52])).
% 0.21/0.58  fof(f229,plain,(
% 0.21/0.58    ~r2_hidden(sK6(k1_yellow19(sK0,sK1),sK2),sK2) | spl8_2),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f123,f102])).
% 0.21/0.58  fof(f102,plain,(
% 0.21/0.58    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK6(X0,X1),X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f66])).
% 0.21/0.58  fof(f108,plain,(
% 0.21/0.58    v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 0.21/0.58    inference(definition_unfolding,[],[f72,f78])).
% 0.21/0.58  fof(f72,plain,(
% 0.21/0.58    v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))),
% 0.21/0.58    inference(cnf_transformation,[],[f52])).
% 0.21/0.58  fof(f241,plain,(
% 0.21/0.58    v3_pre_topc(k1_tops_1(sK0,sK6(k1_yellow19(sK0,sK1),sK2)),sK0) | spl8_2),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f235,f205])).
% 0.21/0.58  fof(f205,plain,(
% 0.21/0.58    ( ! [X30] : (v3_pre_topc(k1_tops_1(sK0,X30),sK0) | ~m1_subset_1(X30,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.21/0.58    inference(subsumption_resolution,[],[f204,f69])).
% 0.21/0.58  fof(f204,plain,(
% 0.21/0.58    ( ! [X30] : (~m1_subset_1(X30,k1_zfmisc_1(k2_struct_0(sK0))) | v3_pre_topc(k1_tops_1(sK0,X30),sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.58    inference(subsumption_resolution,[],[f178,f70])).
% 0.21/0.58  fof(f178,plain,(
% 0.21/0.58    ( ! [X30] : (~m1_subset_1(X30,k1_zfmisc_1(k2_struct_0(sK0))) | v3_pre_topc(k1_tops_1(sK0,X30),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.58    inference(superposition,[],[f99,f149])).
% 0.21/0.58  fof(f99,plain,(
% 0.21/0.58    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f41])).
% 0.21/0.58  fof(f41,plain,(
% 0.21/0.58    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.58    inference(flattening,[],[f40])).
% 0.21/0.58  fof(f40,plain,(
% 0.21/0.58    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f9])).
% 0.21/0.58  fof(f9,axiom,(
% 0.21/0.58    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 0.21/0.58  fof(f240,plain,(
% 0.21/0.58    r2_hidden(sK1,k1_tops_1(sK0,sK6(k1_yellow19(sK0,sK1),sK2))) | spl8_2),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f132,f233,f235,f183])).
% 0.21/0.58  fof(f183,plain,(
% 0.21/0.58    ( ! [X6,X5] : (~m1_subset_1(X6,k2_struct_0(sK0)) | r2_hidden(X6,k1_tops_1(sK0,X5)) | ~m1_connsp_2(X5,sK0,X6) | ~m1_subset_1(X5,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.21/0.58    inference(subsumption_resolution,[],[f182,f68])).
% 0.21/0.58  fof(f182,plain,(
% 0.21/0.58    ( ! [X6,X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_struct_0(sK0))) | r2_hidden(X6,k1_tops_1(sK0,X5)) | ~m1_connsp_2(X5,sK0,X6) | ~m1_subset_1(X6,k2_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 0.21/0.58    inference(subsumption_resolution,[],[f181,f69])).
% 0.21/0.58  fof(f181,plain,(
% 0.21/0.58    ( ! [X6,X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_struct_0(sK0))) | r2_hidden(X6,k1_tops_1(sK0,X5)) | ~m1_connsp_2(X5,sK0,X6) | ~m1_subset_1(X6,k2_struct_0(sK0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.58    inference(subsumption_resolution,[],[f166,f70])).
% 0.21/0.58  fof(f166,plain,(
% 0.21/0.58    ( ! [X6,X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_struct_0(sK0))) | r2_hidden(X6,k1_tops_1(sK0,X5)) | ~m1_connsp_2(X5,sK0,X6) | ~m1_subset_1(X6,k2_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.58    inference(superposition,[],[f83,f149])).
% 0.21/0.58  fof(f83,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f53])).
% 0.21/0.58  fof(f53,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.58    inference(nnf_transformation,[],[f29])).
% 0.21/0.58  fof(f29,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.58    inference(flattening,[],[f28])).
% 0.21/0.58  fof(f28,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f12])).
% 0.21/0.58  fof(f12,axiom,(
% 0.21/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).
% 0.21/0.58  fof(f118,plain,(
% 0.21/0.58    r2_waybel_7(sK0,sK2,sK1) | ~spl8_1),
% 0.21/0.58    inference(avatar_component_clause,[],[f117])).
% 0.21/0.58  fof(f117,plain,(
% 0.21/0.58    spl8_1 <=> r2_waybel_7(sK0,sK2,sK1)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.58  fof(f226,plain,(
% 0.21/0.58    spl8_1 | ~spl8_2),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f225])).
% 0.21/0.58  fof(f225,plain,(
% 0.21/0.58    $false | (spl8_1 | ~spl8_2)),
% 0.21/0.58    inference(subsumption_resolution,[],[f224,f223])).
% 0.21/0.58  fof(f223,plain,(
% 0.21/0.58    ~m1_connsp_2(sK3(sK0,sK2,sK1),sK0,sK1) | (spl8_1 | ~spl8_2)),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f155,f132,f192])).
% 0.21/0.58  fof(f192,plain,(
% 0.21/0.58    ( ! [X15,X16] : (~m1_subset_1(X15,k2_struct_0(sK0)) | r2_hidden(X16,k1_yellow19(sK0,X15)) | ~m1_connsp_2(X16,sK0,X15)) )),
% 0.21/0.58    inference(subsumption_resolution,[],[f191,f68])).
% 0.21/0.58  fof(f191,plain,(
% 0.21/0.58    ( ! [X15,X16] : (~m1_subset_1(X15,k2_struct_0(sK0)) | r2_hidden(X16,k1_yellow19(sK0,X15)) | ~m1_connsp_2(X16,sK0,X15) | v2_struct_0(sK0)) )),
% 0.21/0.58    inference(subsumption_resolution,[],[f190,f69])).
% 0.21/0.58  fof(f190,plain,(
% 0.21/0.58    ( ! [X15,X16] : (~m1_subset_1(X15,k2_struct_0(sK0)) | r2_hidden(X16,k1_yellow19(sK0,X15)) | ~m1_connsp_2(X16,sK0,X15) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.58    inference(subsumption_resolution,[],[f171,f70])).
% 0.21/0.58  fof(f171,plain,(
% 0.21/0.58    ( ! [X15,X16] : (~m1_subset_1(X15,k2_struct_0(sK0)) | r2_hidden(X16,k1_yellow19(sK0,X15)) | ~m1_connsp_2(X16,sK0,X15) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.58    inference(superposition,[],[f86,f149])).
% 0.21/0.58  fof(f86,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (r2_hidden(X2,k1_yellow19(X0,X1)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f54])).
% 0.21/0.58  fof(f155,plain,(
% 0.21/0.58    ~r2_hidden(sK3(sK0,sK2,sK1),k1_yellow19(sK0,sK1)) | (spl8_1 | ~spl8_2)),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f122,f136,f100])).
% 0.21/0.58  fof(f100,plain,(
% 0.21/0.58    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f66])).
% 0.21/0.58  fof(f136,plain,(
% 0.21/0.58    ~r2_hidden(sK3(sK0,sK2,sK1),sK2) | spl8_1),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f69,f70,f119,f92])).
% 0.21/0.58  fof(f92,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (r2_waybel_7(X0,X1,X2) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f58])).
% 0.21/0.58  fof(f119,plain,(
% 0.21/0.58    ~r2_waybel_7(sK0,sK2,sK1) | spl8_1),
% 0.21/0.58    inference(avatar_component_clause,[],[f117])).
% 0.21/0.58  fof(f122,plain,(
% 0.21/0.58    r1_tarski(k1_yellow19(sK0,sK1),sK2) | ~spl8_2),
% 0.21/0.58    inference(avatar_component_clause,[],[f121])).
% 0.21/0.58  fof(f224,plain,(
% 0.21/0.58    m1_connsp_2(sK3(sK0,sK2,sK1),sK0,sK1) | spl8_1),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f135,f134,f150,f196])).
% 0.21/0.58  fof(f196,plain,(
% 0.21/0.58    ( ! [X17,X18] : (m1_connsp_2(X17,sK0,X18) | ~m1_subset_1(X17,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X18,X17) | ~v3_pre_topc(X17,sK0)) )),
% 0.21/0.58    inference(subsumption_resolution,[],[f195,f105])).
% 0.21/0.58  fof(f105,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f44])).
% 0.21/0.58  fof(f44,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.58    inference(flattening,[],[f43])).
% 0.21/0.58  fof(f43,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.58    inference(ennf_transformation,[],[f6])).
% 0.21/0.58  fof(f6,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.58  fof(f195,plain,(
% 0.21/0.58    ( ! [X17,X18] : (~m1_subset_1(X17,k1_zfmisc_1(k2_struct_0(sK0))) | m1_connsp_2(X17,sK0,X18) | ~r2_hidden(X18,X17) | ~v3_pre_topc(X17,sK0) | ~m1_subset_1(X18,k2_struct_0(sK0))) )),
% 0.21/0.58    inference(subsumption_resolution,[],[f194,f68])).
% 0.21/0.58  fof(f194,plain,(
% 0.21/0.58    ( ! [X17,X18] : (~m1_subset_1(X17,k1_zfmisc_1(k2_struct_0(sK0))) | m1_connsp_2(X17,sK0,X18) | ~r2_hidden(X18,X17) | ~v3_pre_topc(X17,sK0) | ~m1_subset_1(X18,k2_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 0.21/0.58    inference(subsumption_resolution,[],[f193,f69])).
% 0.21/0.58  fof(f193,plain,(
% 0.21/0.58    ( ! [X17,X18] : (~m1_subset_1(X17,k1_zfmisc_1(k2_struct_0(sK0))) | m1_connsp_2(X17,sK0,X18) | ~r2_hidden(X18,X17) | ~v3_pre_topc(X17,sK0) | ~m1_subset_1(X18,k2_struct_0(sK0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.58    inference(subsumption_resolution,[],[f172,f70])).
% 0.21/0.58  fof(f172,plain,(
% 0.21/0.58    ( ! [X17,X18] : (~m1_subset_1(X17,k1_zfmisc_1(k2_struct_0(sK0))) | m1_connsp_2(X17,sK0,X18) | ~r2_hidden(X18,X17) | ~v3_pre_topc(X17,sK0) | ~m1_subset_1(X18,k2_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.58    inference(superposition,[],[f87,f149])).
% 0.21/0.58  fof(f87,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f33])).
% 0.21/0.58  fof(f33,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.58    inference(flattening,[],[f32])).
% 0.21/0.58  fof(f32,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f14])).
% 0.21/0.58  fof(f14,axiom,(
% 0.21/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).
% 0.21/0.58  fof(f150,plain,(
% 0.21/0.58    m1_subset_1(sK3(sK0,sK2,sK1),k1_zfmisc_1(k2_struct_0(sK0))) | spl8_1),
% 0.21/0.58    inference(backward_demodulation,[],[f133,f149])).
% 0.21/0.58  fof(f133,plain,(
% 0.21/0.58    m1_subset_1(sK3(sK0,sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl8_1),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f69,f70,f119,f89])).
% 0.21/0.58  fof(f89,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (r2_waybel_7(X0,X1,X2) | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f58])).
% 0.21/0.58  fof(f134,plain,(
% 0.21/0.58    v3_pre_topc(sK3(sK0,sK2,sK1),sK0) | spl8_1),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f69,f70,f119,f90])).
% 0.21/0.58  fof(f90,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (r2_waybel_7(X0,X1,X2) | v3_pre_topc(sK3(X0,X1,X2),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f58])).
% 0.21/0.58  fof(f135,plain,(
% 0.21/0.58    r2_hidden(sK1,sK3(sK0,sK2,sK1)) | spl8_1),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f69,f70,f119,f91])).
% 0.21/0.58  fof(f91,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (r2_waybel_7(X0,X1,X2) | r2_hidden(X2,sK3(X0,X1,X2)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f58])).
% 0.21/0.58  fof(f125,plain,(
% 0.21/0.58    spl8_1 | spl8_2),
% 0.21/0.58    inference(avatar_split_clause,[],[f74,f121,f117])).
% 0.21/0.58  fof(f74,plain,(
% 0.21/0.58    r1_tarski(k1_yellow19(sK0,sK1),sK2) | r2_waybel_7(sK0,sK2,sK1)),
% 0.21/0.58    inference(cnf_transformation,[],[f52])).
% 0.21/0.58  fof(f124,plain,(
% 0.21/0.58    ~spl8_1 | ~spl8_2),
% 0.21/0.58    inference(avatar_split_clause,[],[f75,f121,f117])).
% 0.21/0.58  fof(f75,plain,(
% 0.21/0.58    ~r1_tarski(k1_yellow19(sK0,sK1),sK2) | ~r2_waybel_7(sK0,sK2,sK1)),
% 0.21/0.58    inference(cnf_transformation,[],[f52])).
% 0.21/0.58  % SZS output end Proof for theBenchmark
% 0.21/0.58  % (13195)------------------------------
% 0.21/0.58  % (13195)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (13195)Termination reason: Refutation
% 0.21/0.58  
% 0.21/0.58  % (13195)Memory used [KB]: 11001
% 0.21/0.58  % (13195)Time elapsed: 0.159 s
% 0.21/0.58  % (13195)------------------------------
% 0.21/0.58  % (13195)------------------------------
% 0.21/0.59  % (13176)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.59  % (13168)Success in time 0.225 s
%------------------------------------------------------------------------------
