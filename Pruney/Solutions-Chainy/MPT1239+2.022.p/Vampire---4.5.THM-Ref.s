%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:14 EST 2020

% Result     : Theorem 1.62s
% Output     : Refutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 271 expanded)
%              Number of leaves         :   21 (  96 expanded)
%              Depth                    :   14
%              Number of atoms          :  289 ( 999 expanded)
%              Number of equality atoms :    6 (  18 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1577,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f219,f307,f325,f333,f469,f520,f1576])).

fof(f1576,plain,
    ( spl3_18
    | ~ spl3_19 ),
    inference(avatar_contradiction_clause,[],[f1575])).

fof(f1575,plain,
    ( $false
    | spl3_18
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f1571,f155])).

fof(f155,plain,(
    r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(subsumption_resolution,[],[f152,f37])).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f31,f30,f29])).

fof(f29,plain,
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

fof(f30,plain,
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

fof(f31,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)))
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tops_1)).

fof(f152,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f41,f39])).

fof(f39,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f1571,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | spl3_18
    | ~ spl3_19 ),
    inference(resolution,[],[f1568,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k4_xboole_0(X2,X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f63,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f63,plain,(
    ! [X2,X0,X1] : r1_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X1) ),
    inference(resolution,[],[f52,f43])).

fof(f43,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f1568,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK1,sK2),k1_tops_1(sK0,sK2))
    | spl3_18
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f1567,f569])).

fof(f569,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0))
    | ~ spl3_19 ),
    inference(resolution,[],[f567,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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

fof(f567,plain,
    ( m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f565,f38])).

fof(f38,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f565,plain,
    ( m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_19 ),
    inference(superposition,[],[f301,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f301,plain,
    ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f300])).

fof(f300,plain,
    ( spl3_19
  <=> m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f1567,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK1,sK2),k1_tops_1(sK0,sK2))
    | ~ r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0))
    | spl3_18 ),
    inference(subsumption_resolution,[],[f1560,f37])).

fof(f1560,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK1,sK2),k1_tops_1(sK0,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0))
    | spl3_18 ),
    inference(resolution,[],[f840,f153])).

fof(f153,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f41,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f840,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),X1)
        | ~ r1_xboole_0(X1,k1_tops_1(sK0,sK2)) )
    | spl3_18 ),
    inference(resolution,[],[f838,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f838,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2))
    | spl3_18 ),
    inference(subsumption_resolution,[],[f837,f38])).

fof(f837,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_18 ),
    inference(superposition,[],[f290,f54])).

fof(f290,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK2))
    | spl3_18 ),
    inference(avatar_component_clause,[],[f288])).

fof(f288,plain,
    ( spl3_18
  <=> r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f520,plain,
    ( ~ spl3_17
    | ~ spl3_18
    | spl3_12 ),
    inference(avatar_split_clause,[],[f517,f203,f288,f284])).

fof(f284,plain,
    ( spl3_17
  <=> r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f203,plain,
    ( spl3_12
  <=> r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f517,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK2))
    | ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1))
    | spl3_12 ),
    inference(resolution,[],[f205,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f205,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    | spl3_12 ),
    inference(avatar_component_clause,[],[f203])).

fof(f469,plain,
    ( ~ spl3_12
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f468,f191,f203])).

fof(f191,plain,
    ( spl3_9
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f468,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f466,f192])).

fof(f192,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f191])).

fof(f466,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f40,f54])).

fof(f40,plain,(
    ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f32])).

fof(f333,plain,(
    spl3_20 ),
    inference(avatar_contradiction_clause,[],[f332])).

fof(f332,plain,
    ( $false
    | spl3_20 ),
    inference(subsumption_resolution,[],[f331,f38])).

fof(f331,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_20 ),
    inference(subsumption_resolution,[],[f330,f44])).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f330,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_20 ),
    inference(superposition,[],[f306,f54])).

fof(f306,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
    | spl3_20 ),
    inference(avatar_component_clause,[],[f304])).

fof(f304,plain,
    ( spl3_20
  <=> r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f325,plain,(
    spl3_19 ),
    inference(avatar_contradiction_clause,[],[f324])).

fof(f324,plain,
    ( $false
    | spl3_19 ),
    inference(subsumption_resolution,[],[f320,f60])).

fof(f60,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f49,f38])).

fof(f320,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | spl3_19 ),
    inference(resolution,[],[f313,f44])).

fof(f313,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k4_xboole_0(sK1,sK2),X0)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | spl3_19 ),
    inference(resolution,[],[f312,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f312,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0))
    | spl3_19 ),
    inference(resolution,[],[f311,f50])).

fof(f311,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_19 ),
    inference(subsumption_resolution,[],[f310,f38])).

fof(f310,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_19 ),
    inference(superposition,[],[f302,f54])).

fof(f302,plain,
    ( ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_19 ),
    inference(avatar_component_clause,[],[f300])).

fof(f307,plain,
    ( ~ spl3_19
    | ~ spl3_20
    | spl3_17 ),
    inference(avatar_split_clause,[],[f298,f284,f304,f300])).

fof(f298,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
    | ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_17 ),
    inference(subsumption_resolution,[],[f297,f37])).

fof(f297,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
    | ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_17 ),
    inference(subsumption_resolution,[],[f294,f38])).

fof(f294,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_17 ),
    inference(resolution,[],[f286,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

fof(f286,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1))
    | spl3_17 ),
    inference(avatar_component_clause,[],[f284])).

fof(f219,plain,(
    spl3_9 ),
    inference(avatar_contradiction_clause,[],[f218])).

fof(f218,plain,
    ( $false
    | spl3_9 ),
    inference(subsumption_resolution,[],[f217,f60])).

fof(f217,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | spl3_9 ),
    inference(resolution,[],[f208,f154])).

fof(f154,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f151,f37])).

fof(f151,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f41,f38])).

fof(f208,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_tops_1(sK0,sK1),X0)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | spl3_9 ),
    inference(resolution,[],[f207,f57])).

fof(f207,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | spl3_9 ),
    inference(resolution,[],[f193,f50])).

fof(f193,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f191])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:50:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (31711)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.47  % (31718)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.50  % (31704)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (31702)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.52  % (31722)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.52  % (31710)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.53  % (31720)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.53  % (31715)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.53  % (31714)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.54  % (31707)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.54  % (31701)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (31708)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.54  % (31725)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.54  % (31706)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.54  % (31700)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.55  % (31712)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.43/0.55  % (31723)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.43/0.56  % (31705)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.43/0.56  % (31713)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.62/0.57  % (31724)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.62/0.57  % (31717)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.62/0.58  % (31703)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.62/0.58  % (31716)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.62/0.58  % (31721)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.62/0.58  % (31709)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.62/0.59  % (31719)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.62/0.63  % (31704)Refutation found. Thanks to Tanya!
% 1.62/0.63  % SZS status Theorem for theBenchmark
% 1.62/0.63  % SZS output start Proof for theBenchmark
% 1.62/0.63  fof(f1577,plain,(
% 1.62/0.63    $false),
% 1.62/0.63    inference(avatar_sat_refutation,[],[f219,f307,f325,f333,f469,f520,f1576])).
% 1.62/0.63  fof(f1576,plain,(
% 1.62/0.63    spl3_18 | ~spl3_19),
% 1.62/0.63    inference(avatar_contradiction_clause,[],[f1575])).
% 1.62/0.63  fof(f1575,plain,(
% 1.62/0.63    $false | (spl3_18 | ~spl3_19)),
% 1.62/0.63    inference(subsumption_resolution,[],[f1571,f155])).
% 1.62/0.63  fof(f155,plain,(
% 1.62/0.63    r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 1.62/0.63    inference(subsumption_resolution,[],[f152,f37])).
% 1.62/0.63  fof(f37,plain,(
% 1.62/0.63    l1_pre_topc(sK0)),
% 1.62/0.63    inference(cnf_transformation,[],[f32])).
% 1.62/0.63  fof(f32,plain,(
% 1.62/0.63    ((~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 1.62/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f31,f30,f29])).
% 1.62/0.63  fof(f29,plain,(
% 1.62/0.63    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),X1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 1.62/0.63    introduced(choice_axiom,[])).
% 1.62/0.63  fof(f30,plain,(
% 1.62/0.63    ? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),X1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.62/0.63    introduced(choice_axiom,[])).
% 1.62/0.63  fof(f31,plain,(
% 1.62/0.63    ? [X2] : (~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.62/0.63    introduced(choice_axiom,[])).
% 1.62/0.63  fof(f16,plain,(
% 1.62/0.63    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.62/0.63    inference(flattening,[],[f15])).
% 1.62/0.63  fof(f15,plain,(
% 1.62/0.63    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.62/0.63    inference(ennf_transformation,[],[f14])).
% 1.62/0.63  fof(f14,negated_conjecture,(
% 1.62/0.63    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 1.62/0.63    inference(negated_conjecture,[],[f13])).
% 1.62/0.63  fof(f13,conjecture,(
% 1.62/0.63    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 1.62/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tops_1)).
% 1.62/0.63  fof(f152,plain,(
% 1.62/0.63    r1_tarski(k1_tops_1(sK0,sK2),sK2) | ~l1_pre_topc(sK0)),
% 1.62/0.63    inference(resolution,[],[f41,f39])).
% 1.62/0.63  fof(f39,plain,(
% 1.62/0.63    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.62/0.63    inference(cnf_transformation,[],[f32])).
% 1.62/0.63  fof(f41,plain,(
% 1.62/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 1.62/0.63    inference(cnf_transformation,[],[f17])).
% 1.62/0.63  fof(f17,plain,(
% 1.62/0.63    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.62/0.63    inference(ennf_transformation,[],[f11])).
% 1.62/0.63  fof(f11,axiom,(
% 1.62/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 1.62/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 1.62/0.63  fof(f1571,plain,(
% 1.62/0.63    ~r1_tarski(k1_tops_1(sK0,sK2),sK2) | (spl3_18 | ~spl3_19)),
% 1.62/0.63    inference(resolution,[],[f1568,f69])).
% 1.62/0.63  fof(f69,plain,(
% 1.62/0.63    ( ! [X2,X0,X1] : (r1_xboole_0(k4_xboole_0(X2,X1),X0) | ~r1_tarski(X0,X1)) )),
% 1.62/0.63    inference(superposition,[],[f63,f45])).
% 1.62/0.63  fof(f45,plain,(
% 1.62/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.62/0.63    inference(cnf_transformation,[],[f20])).
% 1.62/0.63  fof(f20,plain,(
% 1.62/0.63    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.62/0.63    inference(ennf_transformation,[],[f2])).
% 1.62/0.63  fof(f2,axiom,(
% 1.62/0.63    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.62/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.62/0.63  fof(f63,plain,(
% 1.62/0.63    ( ! [X2,X0,X1] : (r1_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X1)) )),
% 1.62/0.63    inference(resolution,[],[f52,f43])).
% 1.62/0.63  fof(f43,plain,(
% 1.62/0.63    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.62/0.63    inference(cnf_transformation,[],[f7])).
% 1.62/0.63  fof(f7,axiom,(
% 1.62/0.63    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.62/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.62/0.63  fof(f52,plain,(
% 1.62/0.63    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) )),
% 1.62/0.63    inference(cnf_transformation,[],[f21])).
% 1.62/0.63  fof(f21,plain,(
% 1.62/0.63    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.62/0.63    inference(ennf_transformation,[],[f6])).
% 1.62/0.63  fof(f6,axiom,(
% 1.62/0.63    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.62/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 1.62/0.63  fof(f1568,plain,(
% 1.62/0.63    ~r1_xboole_0(k4_xboole_0(sK1,sK2),k1_tops_1(sK0,sK2)) | (spl3_18 | ~spl3_19)),
% 1.62/0.63    inference(subsumption_resolution,[],[f1567,f569])).
% 1.62/0.63  fof(f569,plain,(
% 1.62/0.63    r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0)) | ~spl3_19),
% 1.62/0.63    inference(resolution,[],[f567,f49])).
% 1.62/0.63  fof(f49,plain,(
% 1.62/0.63    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.62/0.63    inference(cnf_transformation,[],[f35])).
% 1.62/0.63  fof(f35,plain,(
% 1.62/0.63    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.62/0.63    inference(nnf_transformation,[],[f10])).
% 1.62/0.63  fof(f10,axiom,(
% 1.62/0.63    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.62/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.62/0.63  fof(f567,plain,(
% 1.62/0.63    m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_19),
% 1.62/0.63    inference(subsumption_resolution,[],[f565,f38])).
% 1.62/0.63  fof(f38,plain,(
% 1.62/0.63    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.62/0.63    inference(cnf_transformation,[],[f32])).
% 1.62/0.63  fof(f565,plain,(
% 1.62/0.63    m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_19),
% 1.62/0.63    inference(superposition,[],[f301,f54])).
% 1.62/0.63  fof(f54,plain,(
% 1.62/0.63    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.62/0.63    inference(cnf_transformation,[],[f22])).
% 1.62/0.63  fof(f22,plain,(
% 1.62/0.63    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.62/0.63    inference(ennf_transformation,[],[f9])).
% 1.62/0.63  fof(f9,axiom,(
% 1.62/0.63    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 1.62/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.62/0.63  fof(f301,plain,(
% 1.62/0.63    m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_19),
% 1.62/0.63    inference(avatar_component_clause,[],[f300])).
% 1.62/0.63  fof(f300,plain,(
% 1.62/0.63    spl3_19 <=> m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.62/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 1.62/0.63  fof(f1567,plain,(
% 1.62/0.63    ~r1_xboole_0(k4_xboole_0(sK1,sK2),k1_tops_1(sK0,sK2)) | ~r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0)) | spl3_18),
% 1.62/0.63    inference(subsumption_resolution,[],[f1560,f37])).
% 1.62/0.63  fof(f1560,plain,(
% 1.62/0.63    ~r1_xboole_0(k4_xboole_0(sK1,sK2),k1_tops_1(sK0,sK2)) | ~l1_pre_topc(sK0) | ~r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0)) | spl3_18),
% 1.62/0.63    inference(resolution,[],[f840,f153])).
% 1.62/0.63  fof(f153,plain,(
% 1.62/0.63    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~l1_pre_topc(X0) | ~r1_tarski(X1,u1_struct_0(X0))) )),
% 1.62/0.63    inference(resolution,[],[f41,f50])).
% 1.62/0.63  fof(f50,plain,(
% 1.62/0.63    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.62/0.63    inference(cnf_transformation,[],[f35])).
% 1.62/0.63  fof(f840,plain,(
% 1.62/0.63    ( ! [X1] : (~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),X1) | ~r1_xboole_0(X1,k1_tops_1(sK0,sK2))) ) | spl3_18),
% 1.62/0.63    inference(resolution,[],[f838,f55])).
% 1.62/0.63  fof(f55,plain,(
% 1.62/0.63    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.62/0.63    inference(cnf_transformation,[],[f24])).
% 1.62/0.63  fof(f24,plain,(
% 1.62/0.63    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 1.62/0.63    inference(flattening,[],[f23])).
% 1.62/0.63  fof(f23,plain,(
% 1.62/0.63    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.62/0.63    inference(ennf_transformation,[],[f5])).
% 1.62/0.63  fof(f5,axiom,(
% 1.62/0.63    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 1.62/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 1.62/0.63  fof(f838,plain,(
% 1.62/0.63    ~r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) | spl3_18),
% 1.62/0.63    inference(subsumption_resolution,[],[f837,f38])).
% 1.62/0.63  fof(f837,plain,(
% 1.62/0.63    ~r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_18),
% 1.62/0.63    inference(superposition,[],[f290,f54])).
% 1.62/0.63  fof(f290,plain,(
% 1.62/0.63    ~r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK2)) | spl3_18),
% 1.62/0.63    inference(avatar_component_clause,[],[f288])).
% 1.62/0.63  fof(f288,plain,(
% 1.62/0.63    spl3_18 <=> r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK2))),
% 1.62/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 1.62/0.63  fof(f520,plain,(
% 1.62/0.63    ~spl3_17 | ~spl3_18 | spl3_12),
% 1.62/0.63    inference(avatar_split_clause,[],[f517,f203,f288,f284])).
% 1.62/0.63  fof(f284,plain,(
% 1.62/0.63    spl3_17 <=> r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1))),
% 1.62/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 1.62/0.63  fof(f203,plain,(
% 1.62/0.63    spl3_12 <=> r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 1.62/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.62/0.63  fof(f517,plain,(
% 1.62/0.63    ~r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK2)) | ~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1)) | spl3_12),
% 1.62/0.63    inference(resolution,[],[f205,f56])).
% 1.62/0.63  fof(f56,plain,(
% 1.62/0.63    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.62/0.63    inference(cnf_transformation,[],[f26])).
% 1.62/0.63  fof(f26,plain,(
% 1.62/0.63    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 1.62/0.63    inference(flattening,[],[f25])).
% 1.62/0.63  fof(f25,plain,(
% 1.62/0.63    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.62/0.63    inference(ennf_transformation,[],[f8])).
% 1.62/0.63  fof(f8,axiom,(
% 1.62/0.63    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.62/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).
% 1.62/0.63  fof(f205,plain,(
% 1.62/0.63    ~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) | spl3_12),
% 1.62/0.63    inference(avatar_component_clause,[],[f203])).
% 1.62/0.63  fof(f469,plain,(
% 1.62/0.63    ~spl3_12 | ~spl3_9),
% 1.62/0.63    inference(avatar_split_clause,[],[f468,f191,f203])).
% 1.62/0.63  fof(f191,plain,(
% 1.62/0.63    spl3_9 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.62/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.62/0.63  fof(f468,plain,(
% 1.62/0.63    ~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) | ~spl3_9),
% 1.62/0.63    inference(subsumption_resolution,[],[f466,f192])).
% 1.62/0.63  fof(f192,plain,(
% 1.62/0.63    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_9),
% 1.62/0.63    inference(avatar_component_clause,[],[f191])).
% 1.62/0.63  fof(f466,plain,(
% 1.62/0.63    ~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.62/0.63    inference(superposition,[],[f40,f54])).
% 1.62/0.63  fof(f40,plain,(
% 1.62/0.63    ~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 1.62/0.63    inference(cnf_transformation,[],[f32])).
% 1.62/0.63  fof(f333,plain,(
% 1.62/0.63    spl3_20),
% 1.62/0.63    inference(avatar_contradiction_clause,[],[f332])).
% 1.62/0.63  fof(f332,plain,(
% 1.62/0.63    $false | spl3_20),
% 1.62/0.63    inference(subsumption_resolution,[],[f331,f38])).
% 1.62/0.63  fof(f331,plain,(
% 1.62/0.63    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_20),
% 1.62/0.63    inference(subsumption_resolution,[],[f330,f44])).
% 1.62/0.63  fof(f44,plain,(
% 1.62/0.63    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.62/0.63    inference(cnf_transformation,[],[f4])).
% 1.62/0.63  fof(f4,axiom,(
% 1.62/0.63    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.62/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.62/0.63  fof(f330,plain,(
% 1.62/0.63    ~r1_tarski(k4_xboole_0(sK1,sK2),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_20),
% 1.62/0.63    inference(superposition,[],[f306,f54])).
% 1.62/0.63  fof(f306,plain,(
% 1.62/0.63    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1) | spl3_20),
% 1.62/0.63    inference(avatar_component_clause,[],[f304])).
% 1.62/0.63  fof(f304,plain,(
% 1.62/0.63    spl3_20 <=> r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)),
% 1.62/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 1.62/0.63  fof(f325,plain,(
% 1.62/0.63    spl3_19),
% 1.62/0.63    inference(avatar_contradiction_clause,[],[f324])).
% 1.62/0.63  fof(f324,plain,(
% 1.62/0.63    $false | spl3_19),
% 1.62/0.63    inference(subsumption_resolution,[],[f320,f60])).
% 1.62/0.63  fof(f60,plain,(
% 1.62/0.63    r1_tarski(sK1,u1_struct_0(sK0))),
% 1.62/0.63    inference(resolution,[],[f49,f38])).
% 1.62/0.63  fof(f320,plain,(
% 1.62/0.63    ~r1_tarski(sK1,u1_struct_0(sK0)) | spl3_19),
% 1.62/0.63    inference(resolution,[],[f313,f44])).
% 1.62/0.63  fof(f313,plain,(
% 1.62/0.63    ( ! [X0] : (~r1_tarski(k4_xboole_0(sK1,sK2),X0) | ~r1_tarski(X0,u1_struct_0(sK0))) ) | spl3_19),
% 1.62/0.63    inference(resolution,[],[f312,f57])).
% 1.62/0.63  fof(f57,plain,(
% 1.62/0.63    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.62/0.63    inference(cnf_transformation,[],[f28])).
% 1.62/0.63  fof(f28,plain,(
% 1.62/0.63    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.62/0.63    inference(flattening,[],[f27])).
% 1.62/0.63  fof(f27,plain,(
% 1.62/0.63    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.62/0.63    inference(ennf_transformation,[],[f3])).
% 1.62/0.63  fof(f3,axiom,(
% 1.62/0.63    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.62/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.62/0.63  fof(f312,plain,(
% 1.62/0.63    ~r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0)) | spl3_19),
% 1.62/0.63    inference(resolution,[],[f311,f50])).
% 1.62/0.63  fof(f311,plain,(
% 1.62/0.63    ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_19),
% 1.62/0.63    inference(subsumption_resolution,[],[f310,f38])).
% 1.62/0.63  fof(f310,plain,(
% 1.62/0.63    ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_19),
% 1.62/0.63    inference(superposition,[],[f302,f54])).
% 1.62/0.63  fof(f302,plain,(
% 1.62/0.63    ~m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_19),
% 1.62/0.63    inference(avatar_component_clause,[],[f300])).
% 1.62/0.63  fof(f307,plain,(
% 1.62/0.63    ~spl3_19 | ~spl3_20 | spl3_17),
% 1.62/0.63    inference(avatar_split_clause,[],[f298,f284,f304,f300])).
% 1.62/0.63  fof(f298,plain,(
% 1.62/0.63    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1) | ~m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_17),
% 1.62/0.63    inference(subsumption_resolution,[],[f297,f37])).
% 1.62/0.63  fof(f297,plain,(
% 1.62/0.63    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1) | ~m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_17),
% 1.62/0.63    inference(subsumption_resolution,[],[f294,f38])).
% 1.62/0.63  fof(f294,plain,(
% 1.62/0.63    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_17),
% 1.62/0.63    inference(resolution,[],[f286,f42])).
% 1.62/0.63  fof(f42,plain,(
% 1.62/0.63    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.62/0.63    inference(cnf_transformation,[],[f19])).
% 1.62/0.63  fof(f19,plain,(
% 1.62/0.63    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.62/0.63    inference(flattening,[],[f18])).
% 1.62/0.63  fof(f18,plain,(
% 1.62/0.63    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.62/0.63    inference(ennf_transformation,[],[f12])).
% 1.62/0.63  fof(f12,axiom,(
% 1.62/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 1.62/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).
% 1.62/0.63  fof(f286,plain,(
% 1.62/0.63    ~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1)) | spl3_17),
% 1.62/0.63    inference(avatar_component_clause,[],[f284])).
% 1.62/0.63  fof(f219,plain,(
% 1.62/0.63    spl3_9),
% 1.62/0.63    inference(avatar_contradiction_clause,[],[f218])).
% 1.62/0.63  fof(f218,plain,(
% 1.62/0.63    $false | spl3_9),
% 1.62/0.63    inference(subsumption_resolution,[],[f217,f60])).
% 1.62/0.63  fof(f217,plain,(
% 1.62/0.63    ~r1_tarski(sK1,u1_struct_0(sK0)) | spl3_9),
% 1.62/0.63    inference(resolution,[],[f208,f154])).
% 1.62/0.63  fof(f154,plain,(
% 1.62/0.63    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 1.62/0.63    inference(subsumption_resolution,[],[f151,f37])).
% 1.62/0.63  fof(f151,plain,(
% 1.62/0.63    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0)),
% 1.62/0.63    inference(resolution,[],[f41,f38])).
% 1.62/0.63  fof(f208,plain,(
% 1.62/0.63    ( ! [X0] : (~r1_tarski(k1_tops_1(sK0,sK1),X0) | ~r1_tarski(X0,u1_struct_0(sK0))) ) | spl3_9),
% 1.62/0.63    inference(resolution,[],[f207,f57])).
% 1.62/0.63  fof(f207,plain,(
% 1.62/0.63    ~r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | spl3_9),
% 1.62/0.63    inference(resolution,[],[f193,f50])).
% 1.62/0.63  fof(f193,plain,(
% 1.62/0.63    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_9),
% 1.62/0.63    inference(avatar_component_clause,[],[f191])).
% 1.62/0.63  % SZS output end Proof for theBenchmark
% 1.62/0.63  % (31704)------------------------------
% 1.62/0.63  % (31704)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.63  % (31704)Termination reason: Refutation
% 1.62/0.63  
% 1.62/0.63  % (31704)Memory used [KB]: 7036
% 1.62/0.63  % (31704)Time elapsed: 0.185 s
% 1.62/0.63  % (31704)------------------------------
% 1.62/0.63  % (31704)------------------------------
% 1.62/0.63  % (31699)Success in time 0.267 s
%------------------------------------------------------------------------------
