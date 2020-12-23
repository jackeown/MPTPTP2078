%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:12 EST 2020

% Result     : Theorem 1.71s
% Output     : Refutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 273 expanded)
%              Number of leaves         :   20 (  96 expanded)
%              Depth                    :   16
%              Number of atoms          :  275 (1001 expanded)
%              Number of equality atoms :    3 (  15 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1324,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f184,f232,f284,f328,f346,f354,f1321])).

fof(f1321,plain,
    ( spl3_23
    | ~ spl3_24 ),
    inference(avatar_contradiction_clause,[],[f1320])).

fof(f1320,plain,
    ( $false
    | spl3_23
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f1319,f35])).

fof(f35,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f29,f28,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),X1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),X1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)))
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tops_1)).

fof(f1319,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_23
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f1318,f41])).

fof(f41,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f1318,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK1,sK2),sK2)
    | ~ l1_pre_topc(sK0)
    | spl3_23
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f1294,f399])).

fof(f399,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0))
    | ~ spl3_24 ),
    inference(resolution,[],[f397,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f397,plain,
    ( m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f395,f36])).

fof(f36,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f395,plain,
    ( m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_24 ),
    inference(superposition,[],[f322,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f322,plain,
    ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f321])).

fof(f321,plain,
    ( spl3_24
  <=> m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f1294,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0))
    | ~ r1_xboole_0(k4_xboole_0(sK1,sK2),sK2)
    | ~ l1_pre_topc(sK0)
    | spl3_23 ),
    inference(resolution,[],[f382,f594])).

fof(f594,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),sK2)
    | spl3_23 ),
    inference(resolution,[],[f592,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f592,plain,
    ( ~ r1_xboole_0(sK2,k1_tops_1(sK0,k4_xboole_0(sK1,sK2)))
    | spl3_23 ),
    inference(resolution,[],[f590,f143])).

fof(f143,plain,(
    ! [X0] :
      ( r1_xboole_0(k1_tops_1(sK0,sK2),X0)
      | ~ r1_xboole_0(sK2,X0) ) ),
    inference(resolution,[],[f131,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f131,plain,(
    r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(subsumption_resolution,[],[f128,f35])).

fof(f128,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f39,f37])).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f590,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_xboole_0(sK1,sK2)))
    | spl3_23 ),
    inference(resolution,[],[f589,f43])).

fof(f589,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2))
    | spl3_23 ),
    inference(subsumption_resolution,[],[f588,f36])).

fof(f588,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_23 ),
    inference(superposition,[],[f283,f49])).

fof(f283,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK2))
    | spl3_23 ),
    inference(avatar_component_clause,[],[f281])).

fof(f281,plain,
    ( spl3_23
  <=> r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f382,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k1_tops_1(X0,X1),X2)
      | ~ r1_tarski(X1,u1_struct_0(X0))
      | ~ r1_xboole_0(X1,X2)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f129,f50])).

fof(f129,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f39,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f354,plain,(
    spl3_25 ),
    inference(avatar_contradiction_clause,[],[f353])).

fof(f353,plain,
    ( $false
    | spl3_25 ),
    inference(subsumption_resolution,[],[f352,f36])).

fof(f352,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_25 ),
    inference(subsumption_resolution,[],[f351,f42])).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f351,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_25 ),
    inference(superposition,[],[f327,f49])).

fof(f327,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
    | spl3_25 ),
    inference(avatar_component_clause,[],[f325])).

fof(f325,plain,
    ( spl3_25
  <=> r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f346,plain,(
    spl3_24 ),
    inference(avatar_contradiction_clause,[],[f345])).

fof(f345,plain,
    ( $false
    | spl3_24 ),
    inference(subsumption_resolution,[],[f341,f55])).

fof(f55,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f47,f36])).

fof(f341,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | spl3_24 ),
    inference(resolution,[],[f334,f42])).

fof(f334,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k4_xboole_0(sK1,sK2),X0)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | spl3_24 ),
    inference(resolution,[],[f333,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f333,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0))
    | spl3_24 ),
    inference(resolution,[],[f332,f48])).

fof(f332,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_24 ),
    inference(subsumption_resolution,[],[f331,f36])).

fof(f331,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_24 ),
    inference(superposition,[],[f323,f49])).

fof(f323,plain,
    ( ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_24 ),
    inference(avatar_component_clause,[],[f321])).

fof(f328,plain,
    ( ~ spl3_24
    | ~ spl3_25
    | spl3_22 ),
    inference(avatar_split_clause,[],[f319,f277,f325,f321])).

fof(f277,plain,
    ( spl3_22
  <=> r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f319,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
    | ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_22 ),
    inference(subsumption_resolution,[],[f318,f35])).

fof(f318,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
    | ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_22 ),
    inference(subsumption_resolution,[],[f315,f36])).

fof(f315,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_22 ),
    inference(resolution,[],[f279,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
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
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

fof(f279,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1))
    | spl3_22 ),
    inference(avatar_component_clause,[],[f277])).

fof(f284,plain,
    ( ~ spl3_22
    | ~ spl3_23
    | spl3_13 ),
    inference(avatar_split_clause,[],[f273,f181,f281,f277])).

fof(f181,plain,
    ( spl3_13
  <=> r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f273,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK2))
    | ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1))
    | spl3_13 ),
    inference(resolution,[],[f183,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f183,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f181])).

fof(f232,plain,(
    spl3_12 ),
    inference(avatar_contradiction_clause,[],[f231])).

fof(f231,plain,
    ( $false
    | spl3_12 ),
    inference(subsumption_resolution,[],[f228,f55])).

fof(f228,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | spl3_12 ),
    inference(resolution,[],[f187,f130])).

fof(f130,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f127,f35])).

fof(f127,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f39,f36])).

fof(f187,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_tops_1(sK0,sK1),X0)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | spl3_12 ),
    inference(resolution,[],[f186,f52])).

fof(f186,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | spl3_12 ),
    inference(resolution,[],[f179,f48])).

fof(f179,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_12 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl3_12
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f184,plain,
    ( ~ spl3_12
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f174,f181,f177])).

fof(f174,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f38,f49])).

fof(f38,plain,(
    ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:57:11 EST 2020
% 0.18/0.34  % CPUTime    : 
% 0.20/0.47  % (23136)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.49  % (23141)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.49  % (23145)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.49  % (23142)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.49  % (23138)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.50  % (23137)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (23140)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.50  % (23146)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.50  % (23144)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.50  % (23139)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.50  % (23159)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.51  % (23155)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.51  % (23149)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (23147)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.51  % (23148)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.51  % (23157)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.51  % (23152)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.51  % (23151)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.52  % (23160)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.52  % (23158)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.52  % (23156)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.52  % (23143)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.53  % (23154)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.54  % (23150)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.54  % (23153)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.55  % (23161)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.71/0.58  % (23140)Refutation found. Thanks to Tanya!
% 1.71/0.58  % SZS status Theorem for theBenchmark
% 1.71/0.58  % SZS output start Proof for theBenchmark
% 1.71/0.58  fof(f1324,plain,(
% 1.71/0.58    $false),
% 1.71/0.58    inference(avatar_sat_refutation,[],[f184,f232,f284,f328,f346,f354,f1321])).
% 1.71/0.58  fof(f1321,plain,(
% 1.71/0.58    spl3_23 | ~spl3_24),
% 1.71/0.58    inference(avatar_contradiction_clause,[],[f1320])).
% 1.71/0.58  fof(f1320,plain,(
% 1.71/0.58    $false | (spl3_23 | ~spl3_24)),
% 1.71/0.58    inference(subsumption_resolution,[],[f1319,f35])).
% 1.71/0.58  fof(f35,plain,(
% 1.71/0.58    l1_pre_topc(sK0)),
% 1.71/0.58    inference(cnf_transformation,[],[f30])).
% 1.71/0.58  fof(f30,plain,(
% 1.71/0.58    ((~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 1.71/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f29,f28,f27])).
% 1.71/0.58  fof(f27,plain,(
% 1.71/0.58    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),X1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 1.71/0.58    introduced(choice_axiom,[])).
% 1.71/0.58  fof(f28,plain,(
% 1.71/0.58    ? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),X1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.71/0.58    introduced(choice_axiom,[])).
% 1.71/0.58  fof(f29,plain,(
% 1.71/0.58    ? [X2] : (~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.71/0.58    introduced(choice_axiom,[])).
% 1.71/0.58  fof(f15,plain,(
% 1.71/0.58    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.71/0.58    inference(flattening,[],[f14])).
% 1.71/0.58  fof(f14,plain,(
% 1.71/0.58    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.71/0.58    inference(ennf_transformation,[],[f13])).
% 1.71/0.58  fof(f13,negated_conjecture,(
% 1.71/0.58    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 1.71/0.58    inference(negated_conjecture,[],[f12])).
% 1.71/0.58  fof(f12,conjecture,(
% 1.71/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tops_1)).
% 1.71/0.58  fof(f1319,plain,(
% 1.71/0.58    ~l1_pre_topc(sK0) | (spl3_23 | ~spl3_24)),
% 1.71/0.58    inference(subsumption_resolution,[],[f1318,f41])).
% 1.71/0.58  fof(f41,plain,(
% 1.71/0.58    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.71/0.58    inference(cnf_transformation,[],[f6])).
% 1.71/0.58  fof(f6,axiom,(
% 1.71/0.58    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.71/0.58  fof(f1318,plain,(
% 1.71/0.58    ~r1_xboole_0(k4_xboole_0(sK1,sK2),sK2) | ~l1_pre_topc(sK0) | (spl3_23 | ~spl3_24)),
% 1.71/0.58    inference(subsumption_resolution,[],[f1294,f399])).
% 1.71/0.58  fof(f399,plain,(
% 1.71/0.58    r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0)) | ~spl3_24),
% 1.71/0.58    inference(resolution,[],[f397,f47])).
% 1.71/0.58  fof(f47,plain,(
% 1.71/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.71/0.58    inference(cnf_transformation,[],[f33])).
% 1.71/0.58  fof(f33,plain,(
% 1.71/0.58    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.71/0.58    inference(nnf_transformation,[],[f9])).
% 1.71/0.58  fof(f9,axiom,(
% 1.71/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.71/0.58  fof(f397,plain,(
% 1.71/0.58    m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_24),
% 1.71/0.58    inference(subsumption_resolution,[],[f395,f36])).
% 1.71/0.58  fof(f36,plain,(
% 1.71/0.58    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.71/0.58    inference(cnf_transformation,[],[f30])).
% 1.71/0.58  fof(f395,plain,(
% 1.71/0.58    m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_24),
% 1.71/0.58    inference(superposition,[],[f322,f49])).
% 1.71/0.58  fof(f49,plain,(
% 1.71/0.58    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.71/0.58    inference(cnf_transformation,[],[f20])).
% 1.71/0.58  fof(f20,plain,(
% 1.71/0.58    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.71/0.58    inference(ennf_transformation,[],[f8])).
% 1.71/0.58  fof(f8,axiom,(
% 1.71/0.58    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.71/0.58  fof(f322,plain,(
% 1.71/0.58    m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_24),
% 1.71/0.58    inference(avatar_component_clause,[],[f321])).
% 1.71/0.58  fof(f321,plain,(
% 1.71/0.58    spl3_24 <=> m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.71/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 1.71/0.58  fof(f1294,plain,(
% 1.71/0.58    ~r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0)) | ~r1_xboole_0(k4_xboole_0(sK1,sK2),sK2) | ~l1_pre_topc(sK0) | spl3_23),
% 1.71/0.58    inference(resolution,[],[f382,f594])).
% 1.71/0.58  fof(f594,plain,(
% 1.71/0.58    ~r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),sK2) | spl3_23),
% 1.71/0.58    inference(resolution,[],[f592,f43])).
% 1.71/0.58  fof(f43,plain,(
% 1.71/0.58    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.71/0.58    inference(cnf_transformation,[],[f19])).
% 1.71/0.58  fof(f19,plain,(
% 1.71/0.58    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.71/0.58    inference(ennf_transformation,[],[f1])).
% 1.71/0.58  fof(f1,axiom,(
% 1.71/0.58    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.71/0.58  fof(f592,plain,(
% 1.71/0.58    ~r1_xboole_0(sK2,k1_tops_1(sK0,k4_xboole_0(sK1,sK2))) | spl3_23),
% 1.71/0.58    inference(resolution,[],[f590,f143])).
% 1.71/0.58  fof(f143,plain,(
% 1.71/0.58    ( ! [X0] : (r1_xboole_0(k1_tops_1(sK0,sK2),X0) | ~r1_xboole_0(sK2,X0)) )),
% 1.71/0.58    inference(resolution,[],[f131,f50])).
% 1.71/0.58  fof(f50,plain,(
% 1.71/0.58    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 1.71/0.58    inference(cnf_transformation,[],[f22])).
% 1.71/0.58  fof(f22,plain,(
% 1.71/0.58    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 1.71/0.58    inference(flattening,[],[f21])).
% 1.71/0.58  fof(f21,plain,(
% 1.71/0.58    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.71/0.58    inference(ennf_transformation,[],[f5])).
% 1.71/0.58  fof(f5,axiom,(
% 1.71/0.58    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 1.71/0.58  fof(f131,plain,(
% 1.71/0.58    r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 1.71/0.58    inference(subsumption_resolution,[],[f128,f35])).
% 1.71/0.58  fof(f128,plain,(
% 1.71/0.58    r1_tarski(k1_tops_1(sK0,sK2),sK2) | ~l1_pre_topc(sK0)),
% 1.71/0.58    inference(resolution,[],[f39,f37])).
% 1.71/0.58  fof(f37,plain,(
% 1.71/0.58    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.71/0.58    inference(cnf_transformation,[],[f30])).
% 1.71/0.58  fof(f39,plain,(
% 1.71/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 1.71/0.58    inference(cnf_transformation,[],[f16])).
% 1.71/0.58  fof(f16,plain,(
% 1.71/0.58    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.71/0.58    inference(ennf_transformation,[],[f10])).
% 1.71/0.58  fof(f10,axiom,(
% 1.71/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 1.71/0.58  fof(f590,plain,(
% 1.71/0.58    ~r1_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_xboole_0(sK1,sK2))) | spl3_23),
% 1.71/0.58    inference(resolution,[],[f589,f43])).
% 1.71/0.58  fof(f589,plain,(
% 1.71/0.58    ~r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) | spl3_23),
% 1.71/0.58    inference(subsumption_resolution,[],[f588,f36])).
% 1.71/0.58  fof(f588,plain,(
% 1.71/0.58    ~r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_23),
% 1.71/0.58    inference(superposition,[],[f283,f49])).
% 1.71/0.58  fof(f283,plain,(
% 1.71/0.58    ~r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK2)) | spl3_23),
% 1.71/0.58    inference(avatar_component_clause,[],[f281])).
% 1.71/0.58  fof(f281,plain,(
% 1.71/0.58    spl3_23 <=> r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK2))),
% 1.71/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 1.71/0.58  fof(f382,plain,(
% 1.71/0.58    ( ! [X2,X0,X1] : (r1_xboole_0(k1_tops_1(X0,X1),X2) | ~r1_tarski(X1,u1_struct_0(X0)) | ~r1_xboole_0(X1,X2) | ~l1_pre_topc(X0)) )),
% 1.71/0.58    inference(resolution,[],[f129,f50])).
% 1.71/0.58  fof(f129,plain,(
% 1.71/0.58    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~l1_pre_topc(X0) | ~r1_tarski(X1,u1_struct_0(X0))) )),
% 1.71/0.58    inference(resolution,[],[f39,f48])).
% 1.71/0.58  fof(f48,plain,(
% 1.71/0.58    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.71/0.58    inference(cnf_transformation,[],[f33])).
% 1.71/0.58  fof(f354,plain,(
% 1.71/0.58    spl3_25),
% 1.71/0.58    inference(avatar_contradiction_clause,[],[f353])).
% 1.71/0.58  fof(f353,plain,(
% 1.71/0.58    $false | spl3_25),
% 1.71/0.58    inference(subsumption_resolution,[],[f352,f36])).
% 1.71/0.58  fof(f352,plain,(
% 1.71/0.58    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_25),
% 1.71/0.58    inference(subsumption_resolution,[],[f351,f42])).
% 1.71/0.58  fof(f42,plain,(
% 1.71/0.58    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.71/0.58    inference(cnf_transformation,[],[f4])).
% 1.71/0.58  fof(f4,axiom,(
% 1.71/0.58    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.71/0.58  fof(f351,plain,(
% 1.71/0.58    ~r1_tarski(k4_xboole_0(sK1,sK2),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_25),
% 1.71/0.58    inference(superposition,[],[f327,f49])).
% 1.71/0.58  fof(f327,plain,(
% 1.71/0.58    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1) | spl3_25),
% 1.71/0.58    inference(avatar_component_clause,[],[f325])).
% 1.71/0.58  fof(f325,plain,(
% 1.71/0.58    spl3_25 <=> r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)),
% 1.71/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 1.71/0.58  fof(f346,plain,(
% 1.71/0.58    spl3_24),
% 1.71/0.58    inference(avatar_contradiction_clause,[],[f345])).
% 1.71/0.58  fof(f345,plain,(
% 1.71/0.58    $false | spl3_24),
% 1.71/0.58    inference(subsumption_resolution,[],[f341,f55])).
% 1.71/0.58  fof(f55,plain,(
% 1.71/0.58    r1_tarski(sK1,u1_struct_0(sK0))),
% 1.71/0.58    inference(resolution,[],[f47,f36])).
% 1.71/0.58  fof(f341,plain,(
% 1.71/0.58    ~r1_tarski(sK1,u1_struct_0(sK0)) | spl3_24),
% 1.71/0.58    inference(resolution,[],[f334,f42])).
% 1.71/0.58  fof(f334,plain,(
% 1.71/0.58    ( ! [X0] : (~r1_tarski(k4_xboole_0(sK1,sK2),X0) | ~r1_tarski(X0,u1_struct_0(sK0))) ) | spl3_24),
% 1.71/0.58    inference(resolution,[],[f333,f52])).
% 1.71/0.58  fof(f52,plain,(
% 1.71/0.58    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.71/0.58    inference(cnf_transformation,[],[f26])).
% 1.71/0.58  fof(f26,plain,(
% 1.71/0.58    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.71/0.58    inference(flattening,[],[f25])).
% 1.71/0.58  fof(f25,plain,(
% 1.71/0.58    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.71/0.58    inference(ennf_transformation,[],[f3])).
% 1.71/0.58  fof(f3,axiom,(
% 1.71/0.58    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.71/0.58  fof(f333,plain,(
% 1.71/0.58    ~r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0)) | spl3_24),
% 1.71/0.58    inference(resolution,[],[f332,f48])).
% 1.71/0.58  fof(f332,plain,(
% 1.71/0.58    ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_24),
% 1.71/0.58    inference(subsumption_resolution,[],[f331,f36])).
% 1.71/0.58  fof(f331,plain,(
% 1.71/0.58    ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_24),
% 1.71/0.58    inference(superposition,[],[f323,f49])).
% 1.71/0.58  fof(f323,plain,(
% 1.71/0.58    ~m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_24),
% 1.71/0.58    inference(avatar_component_clause,[],[f321])).
% 1.71/0.58  fof(f328,plain,(
% 1.71/0.58    ~spl3_24 | ~spl3_25 | spl3_22),
% 1.71/0.58    inference(avatar_split_clause,[],[f319,f277,f325,f321])).
% 1.71/0.58  fof(f277,plain,(
% 1.71/0.58    spl3_22 <=> r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1))),
% 1.71/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 1.71/0.58  fof(f319,plain,(
% 1.71/0.58    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1) | ~m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_22),
% 1.71/0.58    inference(subsumption_resolution,[],[f318,f35])).
% 1.71/0.58  fof(f318,plain,(
% 1.71/0.58    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1) | ~m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_22),
% 1.71/0.58    inference(subsumption_resolution,[],[f315,f36])).
% 1.71/0.58  fof(f315,plain,(
% 1.71/0.58    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_22),
% 1.71/0.58    inference(resolution,[],[f279,f40])).
% 1.71/0.58  fof(f40,plain,(
% 1.71/0.58    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.71/0.58    inference(cnf_transformation,[],[f18])).
% 1.71/0.58  fof(f18,plain,(
% 1.71/0.58    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.71/0.58    inference(flattening,[],[f17])).
% 1.71/0.58  fof(f17,plain,(
% 1.71/0.58    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.71/0.58    inference(ennf_transformation,[],[f11])).
% 1.71/0.58  fof(f11,axiom,(
% 1.71/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).
% 1.71/0.58  fof(f279,plain,(
% 1.71/0.58    ~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1)) | spl3_22),
% 1.71/0.58    inference(avatar_component_clause,[],[f277])).
% 1.71/0.58  fof(f284,plain,(
% 1.71/0.58    ~spl3_22 | ~spl3_23 | spl3_13),
% 1.71/0.58    inference(avatar_split_clause,[],[f273,f181,f281,f277])).
% 1.71/0.58  fof(f181,plain,(
% 1.71/0.58    spl3_13 <=> r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 1.71/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 1.71/0.58  fof(f273,plain,(
% 1.71/0.58    ~r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK2)) | ~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1)) | spl3_13),
% 1.71/0.58    inference(resolution,[],[f183,f51])).
% 1.71/0.58  fof(f51,plain,(
% 1.71/0.58    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.71/0.58    inference(cnf_transformation,[],[f24])).
% 1.71/0.58  fof(f24,plain,(
% 1.71/0.58    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 1.71/0.58    inference(flattening,[],[f23])).
% 1.71/0.58  fof(f23,plain,(
% 1.71/0.58    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.71/0.58    inference(ennf_transformation,[],[f7])).
% 1.71/0.58  fof(f7,axiom,(
% 1.71/0.58    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).
% 1.71/0.58  fof(f183,plain,(
% 1.71/0.58    ~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) | spl3_13),
% 1.71/0.58    inference(avatar_component_clause,[],[f181])).
% 1.71/0.58  fof(f232,plain,(
% 1.71/0.58    spl3_12),
% 1.71/0.58    inference(avatar_contradiction_clause,[],[f231])).
% 1.71/0.58  fof(f231,plain,(
% 1.71/0.58    $false | spl3_12),
% 1.71/0.58    inference(subsumption_resolution,[],[f228,f55])).
% 1.71/0.58  fof(f228,plain,(
% 1.71/0.58    ~r1_tarski(sK1,u1_struct_0(sK0)) | spl3_12),
% 1.71/0.58    inference(resolution,[],[f187,f130])).
% 1.71/0.58  fof(f130,plain,(
% 1.71/0.58    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 1.71/0.58    inference(subsumption_resolution,[],[f127,f35])).
% 1.71/0.58  fof(f127,plain,(
% 1.71/0.58    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0)),
% 1.71/0.58    inference(resolution,[],[f39,f36])).
% 1.71/0.58  fof(f187,plain,(
% 1.71/0.58    ( ! [X0] : (~r1_tarski(k1_tops_1(sK0,sK1),X0) | ~r1_tarski(X0,u1_struct_0(sK0))) ) | spl3_12),
% 1.71/0.58    inference(resolution,[],[f186,f52])).
% 1.71/0.58  fof(f186,plain,(
% 1.71/0.58    ~r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | spl3_12),
% 1.71/0.58    inference(resolution,[],[f179,f48])).
% 1.71/0.58  fof(f179,plain,(
% 1.71/0.58    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_12),
% 1.71/0.58    inference(avatar_component_clause,[],[f177])).
% 1.71/0.58  fof(f177,plain,(
% 1.71/0.58    spl3_12 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.71/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.71/0.58  fof(f184,plain,(
% 1.71/0.58    ~spl3_12 | ~spl3_13),
% 1.71/0.58    inference(avatar_split_clause,[],[f174,f181,f177])).
% 1.71/0.58  fof(f174,plain,(
% 1.71/0.58    ~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.71/0.58    inference(superposition,[],[f38,f49])).
% 1.71/0.58  fof(f38,plain,(
% 1.71/0.58    ~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 1.71/0.58    inference(cnf_transformation,[],[f30])).
% 1.71/0.58  % SZS output end Proof for theBenchmark
% 1.71/0.58  % (23140)------------------------------
% 1.71/0.58  % (23140)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.58  % (23140)Termination reason: Refutation
% 1.71/0.58  
% 1.71/0.58  % (23140)Memory used [KB]: 6780
% 1.71/0.58  % (23140)Time elapsed: 0.161 s
% 1.71/0.58  % (23140)------------------------------
% 1.71/0.58  % (23140)------------------------------
% 1.71/0.58  % (23135)Success in time 0.227 s
%------------------------------------------------------------------------------
