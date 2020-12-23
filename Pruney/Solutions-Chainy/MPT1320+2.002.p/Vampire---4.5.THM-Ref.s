%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:51 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 290 expanded)
%              Number of leaves         :   18 ( 120 expanded)
%              Depth                    :   16
%              Number of atoms          :  367 (1629 expanded)
%              Number of equality atoms :   58 (  92 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f412,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f345,f403,f411])).

fof(f411,plain,(
    spl7_31 ),
    inference(avatar_contradiction_clause,[],[f410])).

fof(f410,plain,
    ( $false
    | spl7_31 ),
    inference(subsumption_resolution,[],[f153,f409])).

fof(f409,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2)
    | spl7_31 ),
    inference(resolution,[],[f344,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f344,plain,
    ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(sK2))
    | spl7_31 ),
    inference(avatar_component_clause,[],[f343])).

fof(f343,plain,
    ( spl7_31
  <=> m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f153,plain,(
    r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2) ),
    inference(superposition,[],[f59,f150])).

fof(f150,plain,(
    k1_setfam_1(k2_tarski(sK1,sK2)) = k1_setfam_1(k2_tarski(sK2,sK1)) ),
    inference(superposition,[],[f149,f74])).

fof(f74,plain,(
    ! [X2] : k9_subset_1(u1_struct_0(sK0),X2,sK2) = k1_setfam_1(k2_tarski(X2,sK2)) ),
    inference(resolution,[],[f38,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f55,f53])).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f38,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_2(sK0,sK2,sK3))
    & r2_hidden(sK1,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f27,f26,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3))
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),X1,X2),k1_tops_2(sK0,X2,X3))
                  & r2_hidden(X1,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),X1,X2),k1_tops_2(sK0,X2,X3))
                & r2_hidden(X1,X3)
                & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,X2),k1_tops_2(sK0,X2,X3))
              & r2_hidden(sK1,X3)
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,X2),k1_tops_2(sK0,X2,X3))
            & r2_hidden(sK1,X3)
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X3] :
          ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_2(sK0,sK2,X3))
          & r2_hidden(sK1,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X3] :
        ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_2(sK0,sK2,X3))
        & r2_hidden(sK1,X3)
        & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_2(sK0,sK2,sK3))
      & r2_hidden(sK1,sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3))
                  & r2_hidden(X1,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3))
                  & r2_hidden(X1,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                   => ( r2_hidden(X1,X3)
                     => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                 => ( r2_hidden(X1,X3)
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tops_2)).

fof(f149,plain,(
    ! [X1] : k9_subset_1(u1_struct_0(sK0),sK1,X1) = k1_setfam_1(k2_tarski(X1,sK1)) ),
    inference(forward_demodulation,[],[f68,f69])).

fof(f69,plain,(
    ! [X2] : k9_subset_1(u1_struct_0(sK0),X2,sK1) = k1_setfam_1(k2_tarski(X2,sK1)) ),
    inference(resolution,[],[f37,f60])).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f68,plain,(
    ! [X1] : k9_subset_1(u1_struct_0(sK0),X1,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X1) ),
    inference(resolution,[],[f37,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f59,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f52,f53])).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f403,plain,(
    spl7_30 ),
    inference(avatar_contradiction_clause,[],[f401])).

fof(f401,plain,
    ( $false
    | spl7_30 ),
    inference(subsumption_resolution,[],[f39,f350])).

fof(f350,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl7_30 ),
    inference(resolution,[],[f341,f125])).

fof(f125,plain,(
    ! [X8] :
      ( m1_subset_1(k1_tops_2(sK0,sK2,X8),k1_zfmisc_1(k1_zfmisc_1(sK2)))
      | ~ m1_subset_1(X8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    inference(global_subsumption,[],[f36,f38,f114])).

fof(f114,plain,(
    ! [X8] :
      ( m1_subset_1(k1_tops_2(sK0,sK2,X8),k1_zfmisc_1(k1_zfmisc_1(sK2)))
      | ~ m1_subset_1(X8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f57,f75])).

fof(f75,plain,(
    sK2 = u1_struct_0(k1_pre_topc(sK0,sK2)) ),
    inference(global_subsumption,[],[f36,f71])).

fof(f71,plain,
    ( sK2 = u1_struct_0(k1_pre_topc(sK0,sK2))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f38,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_2)).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f341,plain,
    ( ~ m1_subset_1(k1_tops_2(sK0,sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | spl7_30 ),
    inference(avatar_component_clause,[],[f340])).

fof(f340,plain,
    ( spl7_30
  <=> m1_subset_1(k1_tops_2(sK0,sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f39,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f28])).

fof(f345,plain,
    ( ~ spl7_30
    | ~ spl7_31 ),
    inference(avatar_split_clause,[],[f338,f343,f340])).

fof(f338,plain,
    ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(sK2))
    | ~ m1_subset_1(k1_tops_2(sK0,sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(global_subsumption,[],[f40,f37,f39,f335])).

fof(f335,plain,
    ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(sK2))
    | ~ m1_subset_1(k1_tops_2(sK0,sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | ~ r2_hidden(sK1,sK3)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f334,f145])).

fof(f145,plain,(
    ~ r2_hidden(k1_setfam_1(k2_tarski(sK1,sK2)),k1_tops_2(sK0,sK2,sK3)) ),
    inference(backward_demodulation,[],[f41,f74])).

fof(f41,plain,(
    ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_2(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f28])).

fof(f334,plain,(
    ! [X10,X9] :
      ( r2_hidden(k1_setfam_1(k2_tarski(X10,sK2)),k1_tops_2(sK0,sK2,X9))
      | ~ m1_subset_1(k1_setfam_1(k2_tarski(X10,sK2)),k1_zfmisc_1(sK2))
      | ~ m1_subset_1(k1_tops_2(sK0,sK2,X9),k1_zfmisc_1(k1_zfmisc_1(sK2)))
      | ~ r2_hidden(X10,X9)
      | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    inference(forward_demodulation,[],[f333,f74])).

fof(f333,plain,(
    ! [X10,X9] :
      ( ~ m1_subset_1(k1_setfam_1(k2_tarski(X10,sK2)),k1_zfmisc_1(sK2))
      | ~ m1_subset_1(k1_tops_2(sK0,sK2,X9),k1_zfmisc_1(k1_zfmisc_1(sK2)))
      | ~ r2_hidden(X10,X9)
      | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(k9_subset_1(u1_struct_0(sK0),X10,sK2),k1_tops_2(sK0,sK2,X9))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    inference(forward_demodulation,[],[f126,f74])).

fof(f126,plain,(
    ! [X10,X9] :
      ( ~ m1_subset_1(k1_tops_2(sK0,sK2,X9),k1_zfmisc_1(k1_zfmisc_1(sK2)))
      | ~ r2_hidden(X10,X9)
      | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),X10,sK2),k1_zfmisc_1(sK2))
      | r2_hidden(k9_subset_1(u1_struct_0(sK0),X10,sK2),k1_tops_2(sK0,sK2,X9))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    inference(global_subsumption,[],[f36,f38,f115])).

fof(f115,plain,(
    ! [X10,X9] :
      ( ~ m1_subset_1(k1_tops_2(sK0,sK2,X9),k1_zfmisc_1(k1_zfmisc_1(sK2)))
      | ~ r2_hidden(X10,X9)
      | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),X10,sK2),k1_zfmisc_1(sK2))
      | r2_hidden(k9_subset_1(u1_struct_0(sK0),X10,sK2),k1_tops_2(sK0,sK2,X9))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f62,f75])).

fof(f62,plain,(
    ! [X2,X0,X8,X1] :
      ( ~ m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ r2_hidden(X8,X2)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X8,X1),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
      | r2_hidden(k9_subset_1(u1_struct_0(X0),X8,X1),k1_tops_2(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X8,X3,X1] :
      ( r2_hidden(k9_subset_1(u1_struct_0(X0),X8,X1),X3)
      | ~ r2_hidden(X8,X2)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X8,X1),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
      | k1_tops_2(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X8,X7,X3,X1] :
      ( r2_hidden(X7,X3)
      | k9_subset_1(u1_struct_0(X0),X8,X1) != X7
      | ~ r2_hidden(X8,X2)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
      | k1_tops_2(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k1_tops_2(X0,X1,X2) = X3
                      | ( ( ! [X5] :
                              ( k9_subset_1(u1_struct_0(X0),X5,X1) != sK4(X0,X1,X2,X3)
                              | ~ r2_hidden(X5,X2)
                              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                          | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
                        & ( ( sK4(X0,X1,X2,X3) = k9_subset_1(u1_struct_0(X0),sK5(X0,X1,X2,X3),X1)
                            & r2_hidden(sK5(X0,X1,X2,X3),X2)
                            & m1_subset_1(sK5(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(X0))) )
                          | r2_hidden(sK4(X0,X1,X2,X3),X3) )
                        & m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) )
                    & ( ! [X7] :
                          ( ( ( r2_hidden(X7,X3)
                              | ! [X8] :
                                  ( k9_subset_1(u1_struct_0(X0),X8,X1) != X7
                                  | ~ r2_hidden(X8,X2)
                                  | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0))) ) )
                            & ( ( k9_subset_1(u1_struct_0(X0),sK6(X0,X1,X2,X7),X1) = X7
                                & r2_hidden(sK6(X0,X1,X2,X7),X2)
                                & m1_subset_1(sK6(X0,X1,X2,X7),k1_zfmisc_1(u1_struct_0(X0))) )
                              | ~ r2_hidden(X7,X3) ) )
                          | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) )
                      | k1_tops_2(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f31,f34,f33,f32])).

fof(f32,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( k9_subset_1(u1_struct_0(X0),X5,X1) != X4
                | ~ r2_hidden(X5,X2)
                | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_hidden(X4,X3) )
          & ( ? [X6] :
                ( k9_subset_1(u1_struct_0(X0),X6,X1) = X4
                & r2_hidden(X6,X2)
                & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
            | r2_hidden(X4,X3) )
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) )
     => ( ( ! [X5] :
              ( k9_subset_1(u1_struct_0(X0),X5,X1) != sK4(X0,X1,X2,X3)
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
        & ( ? [X6] :
              ( k9_subset_1(u1_struct_0(X0),X6,X1) = sK4(X0,X1,X2,X3)
              & r2_hidden(X6,X2)
              & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
          | r2_hidden(sK4(X0,X1,X2,X3),X3) )
        & m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6] :
          ( k9_subset_1(u1_struct_0(X0),X6,X1) = sK4(X0,X1,X2,X3)
          & r2_hidden(X6,X2)
          & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK4(X0,X1,X2,X3) = k9_subset_1(u1_struct_0(X0),sK5(X0,X1,X2,X3),X1)
        & r2_hidden(sK5(X0,X1,X2,X3),X2)
        & m1_subset_1(sK5(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X7,X2,X1,X0] :
      ( ? [X9] :
          ( k9_subset_1(u1_struct_0(X0),X9,X1) = X7
          & r2_hidden(X9,X2)
          & m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),sK6(X0,X1,X2,X7),X1) = X7
        & r2_hidden(sK6(X0,X1,X2,X7),X2)
        & m1_subset_1(sK6(X0,X1,X2,X7),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k1_tops_2(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ( ! [X5] :
                                ( k9_subset_1(u1_struct_0(X0),X5,X1) != X4
                                | ~ r2_hidden(X5,X2)
                                | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                            | ~ r2_hidden(X4,X3) )
                          & ( ? [X6] :
                                ( k9_subset_1(u1_struct_0(X0),X6,X1) = X4
                                & r2_hidden(X6,X2)
                                & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
                            | r2_hidden(X4,X3) )
                          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) )
                    & ( ! [X7] :
                          ( ( ( r2_hidden(X7,X3)
                              | ! [X8] :
                                  ( k9_subset_1(u1_struct_0(X0),X8,X1) != X7
                                  | ~ r2_hidden(X8,X2)
                                  | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0))) ) )
                            & ( ? [X9] :
                                  ( k9_subset_1(u1_struct_0(X0),X9,X1) = X7
                                  & r2_hidden(X9,X2)
                                  & m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X0))) )
                              | ~ r2_hidden(X7,X3) ) )
                          | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) )
                      | k1_tops_2(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k1_tops_2(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ( ! [X5] :
                                ( k9_subset_1(u1_struct_0(X0),X5,X1) != X4
                                | ~ r2_hidden(X5,X2)
                                | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                            | ~ r2_hidden(X4,X3) )
                          & ( ? [X5] :
                                ( k9_subset_1(u1_struct_0(X0),X5,X1) = X4
                                & r2_hidden(X5,X2)
                                & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                            | r2_hidden(X4,X3) )
                          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) )
                    & ( ! [X4] :
                          ( ( ( r2_hidden(X4,X3)
                              | ! [X5] :
                                  ( k9_subset_1(u1_struct_0(X0),X5,X1) != X4
                                  | ~ r2_hidden(X5,X2)
                                  | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) ) )
                            & ( ? [X5] :
                                  ( k9_subset_1(u1_struct_0(X0),X5,X1) = X4
                                  & r2_hidden(X5,X2)
                                  & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                              | ~ r2_hidden(X4,X3) ) )
                          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) )
                      | k1_tops_2(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k1_tops_2(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ( ! [X5] :
                                ( k9_subset_1(u1_struct_0(X0),X5,X1) != X4
                                | ~ r2_hidden(X5,X2)
                                | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                            | ~ r2_hidden(X4,X3) )
                          & ( ? [X5] :
                                ( k9_subset_1(u1_struct_0(X0),X5,X1) = X4
                                & r2_hidden(X5,X2)
                                & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                            | r2_hidden(X4,X3) )
                          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) )
                    & ( ! [X4] :
                          ( ( ( r2_hidden(X4,X3)
                              | ! [X5] :
                                  ( k9_subset_1(u1_struct_0(X0),X5,X1) != X4
                                  | ~ r2_hidden(X5,X2)
                                  | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) ) )
                            & ( ? [X5] :
                                  ( k9_subset_1(u1_struct_0(X0),X5,X1) = X4
                                  & r2_hidden(X5,X2)
                                  & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                              | ~ r2_hidden(X4,X3) ) )
                          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) )
                      | k1_tops_2(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tops_2(X0,X1,X2) = X3
                  <=> ! [X4] :
                        ( ( r2_hidden(X4,X3)
                        <=> ? [X5] :
                              ( k9_subset_1(u1_struct_0(X0),X5,X1) = X4
                              & r2_hidden(X5,X2)
                              & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) ) )
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
                 => ( k1_tops_2(X0,X1,X2) = X3
                  <=> ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
                       => ( r2_hidden(X4,X3)
                        <=> ? [X5] :
                              ( k9_subset_1(u1_struct_0(X0),X5,X1) = X4
                              & r2_hidden(X5,X2)
                              & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_2)).

fof(f40,plain,(
    r2_hidden(sK1,sK3) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:51:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (26083)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (26091)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.17/0.52  % (26084)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.17/0.52  % (26086)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.17/0.52  % (26088)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.17/0.52  % (26103)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.17/0.53  % (26094)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.17/0.53  % (26095)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.17/0.53  % (26085)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.17/0.53  % (26099)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.17/0.53  % (26081)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.17/0.53  % (26093)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.17/0.53  % (26087)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.34/0.53  % (26092)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.34/0.54  % (26103)Refutation not found, incomplete strategy% (26103)------------------------------
% 1.34/0.54  % (26103)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (26103)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (26103)Memory used [KB]: 10746
% 1.34/0.54  % (26103)Time elapsed: 0.098 s
% 1.34/0.54  % (26103)------------------------------
% 1.34/0.54  % (26103)------------------------------
% 1.34/0.54  % (26101)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.34/0.54  % (26109)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.34/0.54  % (26107)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.34/0.54  % (26108)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.34/0.54  % (26102)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.34/0.54  % (26096)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.34/0.54  % (26110)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.34/0.54  % (26105)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.34/0.54  % (26090)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.34/0.55  % (26083)Refutation found. Thanks to Tanya!
% 1.34/0.55  % SZS status Theorem for theBenchmark
% 1.34/0.55  % SZS output start Proof for theBenchmark
% 1.34/0.55  fof(f412,plain,(
% 1.34/0.55    $false),
% 1.34/0.55    inference(avatar_sat_refutation,[],[f345,f403,f411])).
% 1.34/0.55  fof(f411,plain,(
% 1.34/0.55    spl7_31),
% 1.34/0.55    inference(avatar_contradiction_clause,[],[f410])).
% 1.34/0.55  fof(f410,plain,(
% 1.34/0.55    $false | spl7_31),
% 1.34/0.55    inference(subsumption_resolution,[],[f153,f409])).
% 1.34/0.55  fof(f409,plain,(
% 1.34/0.55    ~r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2) | spl7_31),
% 1.34/0.55    inference(resolution,[],[f344,f54])).
% 1.34/0.55  fof(f54,plain,(
% 1.34/0.55    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.34/0.55    inference(cnf_transformation,[],[f17])).
% 1.34/0.55  fof(f17,plain,(
% 1.34/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 1.34/0.55    inference(ennf_transformation,[],[f12])).
% 1.34/0.55  fof(f12,plain,(
% 1.34/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 1.34/0.55    inference(unused_predicate_definition_removal,[],[f5])).
% 1.34/0.55  fof(f5,axiom,(
% 1.34/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.34/0.55  fof(f344,plain,(
% 1.34/0.55    ~m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(sK2)) | spl7_31),
% 1.34/0.55    inference(avatar_component_clause,[],[f343])).
% 1.34/0.55  fof(f343,plain,(
% 1.34/0.55    spl7_31 <=> m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(sK2))),
% 1.34/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 1.34/0.55  fof(f153,plain,(
% 1.34/0.55    r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2)),
% 1.34/0.55    inference(superposition,[],[f59,f150])).
% 1.34/0.55  fof(f150,plain,(
% 1.34/0.55    k1_setfam_1(k2_tarski(sK1,sK2)) = k1_setfam_1(k2_tarski(sK2,sK1))),
% 1.34/0.55    inference(superposition,[],[f149,f74])).
% 1.34/0.55  fof(f74,plain,(
% 1.34/0.55    ( ! [X2] : (k9_subset_1(u1_struct_0(sK0),X2,sK2) = k1_setfam_1(k2_tarski(X2,sK2))) )),
% 1.34/0.55    inference(resolution,[],[f38,f60])).
% 1.34/0.55  fof(f60,plain,(
% 1.34/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))) )),
% 1.34/0.55    inference(definition_unfolding,[],[f55,f53])).
% 1.34/0.55  fof(f53,plain,(
% 1.34/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.34/0.55    inference(cnf_transformation,[],[f4])).
% 1.34/0.55  fof(f4,axiom,(
% 1.34/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.34/0.55  fof(f55,plain,(
% 1.34/0.55    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.34/0.55    inference(cnf_transformation,[],[f18])).
% 1.34/0.55  fof(f18,plain,(
% 1.34/0.55    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.34/0.55    inference(ennf_transformation,[],[f3])).
% 1.34/0.55  fof(f3,axiom,(
% 1.34/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.34/0.55  fof(f38,plain,(
% 1.34/0.55    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.34/0.55    inference(cnf_transformation,[],[f28])).
% 1.34/0.55  fof(f28,plain,(
% 1.34/0.55    (((~r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_2(sK0,sK2,sK3)) & r2_hidden(sK1,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 1.34/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f27,f26,f25,f24])).
% 1.34/0.55  fof(f24,plain,(
% 1.34/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k9_subset_1(u1_struct_0(sK0),X1,X2),k1_tops_2(sK0,X2,X3)) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 1.34/0.55    introduced(choice_axiom,[])).
% 1.34/0.55  fof(f25,plain,(
% 1.34/0.55    ? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k9_subset_1(u1_struct_0(sK0),X1,X2),k1_tops_2(sK0,X2,X3)) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (? [X3] : (~r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,X2),k1_tops_2(sK0,X2,X3)) & r2_hidden(sK1,X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.34/0.55    introduced(choice_axiom,[])).
% 1.34/0.55  fof(f26,plain,(
% 1.34/0.55    ? [X2] : (? [X3] : (~r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,X2),k1_tops_2(sK0,X2,X3)) & r2_hidden(sK1,X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X3] : (~r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_2(sK0,sK2,X3)) & r2_hidden(sK1,X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.34/0.55    introduced(choice_axiom,[])).
% 1.34/0.55  fof(f27,plain,(
% 1.34/0.55    ? [X3] : (~r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_2(sK0,sK2,X3)) & r2_hidden(sK1,X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (~r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_2(sK0,sK2,sK3)) & r2_hidden(sK1,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 1.34/0.55    introduced(choice_axiom,[])).
% 1.34/0.55  fof(f14,plain,(
% 1.34/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.34/0.55    inference(flattening,[],[f13])).
% 1.34/0.55  fof(f13,plain,(
% 1.34/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)) & r2_hidden(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.34/0.55    inference(ennf_transformation,[],[f11])).
% 1.34/0.55  fof(f11,negated_conjecture,(
% 1.34/0.55    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,X3) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)))))))),
% 1.34/0.55    inference(negated_conjecture,[],[f10])).
% 1.34/0.55  fof(f10,conjecture,(
% 1.34/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,X3) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)))))))),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tops_2)).
% 1.34/0.55  fof(f149,plain,(
% 1.34/0.55    ( ! [X1] : (k9_subset_1(u1_struct_0(sK0),sK1,X1) = k1_setfam_1(k2_tarski(X1,sK1))) )),
% 1.34/0.55    inference(forward_demodulation,[],[f68,f69])).
% 1.34/0.55  fof(f69,plain,(
% 1.34/0.55    ( ! [X2] : (k9_subset_1(u1_struct_0(sK0),X2,sK1) = k1_setfam_1(k2_tarski(X2,sK1))) )),
% 1.34/0.55    inference(resolution,[],[f37,f60])).
% 1.34/0.55  fof(f37,plain,(
% 1.34/0.55    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.34/0.55    inference(cnf_transformation,[],[f28])).
% 1.34/0.55  fof(f68,plain,(
% 1.34/0.55    ( ! [X1] : (k9_subset_1(u1_struct_0(sK0),X1,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X1)) )),
% 1.34/0.55    inference(resolution,[],[f37,f56])).
% 1.34/0.55  fof(f56,plain,(
% 1.34/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)) )),
% 1.34/0.55    inference(cnf_transformation,[],[f19])).
% 1.34/0.55  fof(f19,plain,(
% 1.34/0.55    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.34/0.55    inference(ennf_transformation,[],[f2])).
% 1.34/0.55  fof(f2,axiom,(
% 1.34/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).
% 1.34/0.55  fof(f59,plain,(
% 1.34/0.55    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 1.34/0.55    inference(definition_unfolding,[],[f52,f53])).
% 1.34/0.55  fof(f52,plain,(
% 1.34/0.55    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.34/0.55    inference(cnf_transformation,[],[f1])).
% 1.34/0.55  fof(f1,axiom,(
% 1.34/0.55    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.34/0.55  fof(f403,plain,(
% 1.34/0.55    spl7_30),
% 1.34/0.55    inference(avatar_contradiction_clause,[],[f401])).
% 1.34/0.55  fof(f401,plain,(
% 1.34/0.55    $false | spl7_30),
% 1.34/0.55    inference(subsumption_resolution,[],[f39,f350])).
% 1.34/0.55  fof(f350,plain,(
% 1.34/0.55    ~m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl7_30),
% 1.34/0.55    inference(resolution,[],[f341,f125])).
% 1.34/0.55  fof(f125,plain,(
% 1.34/0.55    ( ! [X8] : (m1_subset_1(k1_tops_2(sK0,sK2,X8),k1_zfmisc_1(k1_zfmisc_1(sK2))) | ~m1_subset_1(X8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) )),
% 1.34/0.55    inference(global_subsumption,[],[f36,f38,f114])).
% 1.34/0.55  fof(f114,plain,(
% 1.34/0.55    ( ! [X8] : (m1_subset_1(k1_tops_2(sK0,sK2,X8),k1_zfmisc_1(k1_zfmisc_1(sK2))) | ~m1_subset_1(X8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 1.34/0.55    inference(superposition,[],[f57,f75])).
% 1.34/0.55  fof(f75,plain,(
% 1.34/0.55    sK2 = u1_struct_0(k1_pre_topc(sK0,sK2))),
% 1.34/0.55    inference(global_subsumption,[],[f36,f71])).
% 1.34/0.55  fof(f71,plain,(
% 1.34/0.55    sK2 = u1_struct_0(k1_pre_topc(sK0,sK2)) | ~l1_pre_topc(sK0)),
% 1.34/0.55    inference(resolution,[],[f38,f42])).
% 1.34/0.55  fof(f42,plain,(
% 1.34/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~l1_pre_topc(X0)) )),
% 1.34/0.55    inference(cnf_transformation,[],[f15])).
% 1.34/0.55  fof(f15,plain,(
% 1.34/0.55    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.34/0.55    inference(ennf_transformation,[],[f7])).
% 1.34/0.55  fof(f7,axiom,(
% 1.34/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).
% 1.34/0.55  fof(f57,plain,(
% 1.34/0.55    ( ! [X2,X0,X1] : (m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.34/0.55    inference(cnf_transformation,[],[f21])).
% 1.34/0.55  fof(f21,plain,(
% 1.34/0.55    ! [X0,X1,X2] : (m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.34/0.55    inference(flattening,[],[f20])).
% 1.34/0.55  fof(f20,plain,(
% 1.34/0.55    ! [X0,X1,X2] : (m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.34/0.55    inference(ennf_transformation,[],[f9])).
% 1.34/0.55  fof(f9,axiom,(
% 1.34/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))))),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_2)).
% 1.34/0.55  fof(f36,plain,(
% 1.34/0.55    l1_pre_topc(sK0)),
% 1.34/0.55    inference(cnf_transformation,[],[f28])).
% 1.34/0.55  fof(f341,plain,(
% 1.34/0.55    ~m1_subset_1(k1_tops_2(sK0,sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK2))) | spl7_30),
% 1.34/0.55    inference(avatar_component_clause,[],[f340])).
% 1.34/0.55  fof(f340,plain,(
% 1.34/0.55    spl7_30 <=> m1_subset_1(k1_tops_2(sK0,sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 1.34/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).
% 1.34/0.55  fof(f39,plain,(
% 1.34/0.55    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.34/0.55    inference(cnf_transformation,[],[f28])).
% 1.34/0.55  fof(f345,plain,(
% 1.34/0.55    ~spl7_30 | ~spl7_31),
% 1.34/0.55    inference(avatar_split_clause,[],[f338,f343,f340])).
% 1.34/0.55  fof(f338,plain,(
% 1.34/0.55    ~m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(sK2)) | ~m1_subset_1(k1_tops_2(sK0,sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 1.34/0.55    inference(global_subsumption,[],[f40,f37,f39,f335])).
% 1.34/0.55  fof(f335,plain,(
% 1.34/0.55    ~m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(sK2)) | ~m1_subset_1(k1_tops_2(sK0,sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK2))) | ~r2_hidden(sK1,sK3) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.34/0.55    inference(resolution,[],[f334,f145])).
% 1.34/0.55  fof(f145,plain,(
% 1.34/0.55    ~r2_hidden(k1_setfam_1(k2_tarski(sK1,sK2)),k1_tops_2(sK0,sK2,sK3))),
% 1.34/0.55    inference(backward_demodulation,[],[f41,f74])).
% 1.34/0.55  fof(f41,plain,(
% 1.34/0.55    ~r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_2(sK0,sK2,sK3))),
% 1.34/0.55    inference(cnf_transformation,[],[f28])).
% 1.34/0.55  fof(f334,plain,(
% 1.34/0.55    ( ! [X10,X9] : (r2_hidden(k1_setfam_1(k2_tarski(X10,sK2)),k1_tops_2(sK0,sK2,X9)) | ~m1_subset_1(k1_setfam_1(k2_tarski(X10,sK2)),k1_zfmisc_1(sK2)) | ~m1_subset_1(k1_tops_2(sK0,sK2,X9),k1_zfmisc_1(k1_zfmisc_1(sK2))) | ~r2_hidden(X10,X9) | ~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) )),
% 1.34/0.55    inference(forward_demodulation,[],[f333,f74])).
% 1.34/0.55  fof(f333,plain,(
% 1.34/0.55    ( ! [X10,X9] : (~m1_subset_1(k1_setfam_1(k2_tarski(X10,sK2)),k1_zfmisc_1(sK2)) | ~m1_subset_1(k1_tops_2(sK0,sK2,X9),k1_zfmisc_1(k1_zfmisc_1(sK2))) | ~r2_hidden(X10,X9) | ~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(k9_subset_1(u1_struct_0(sK0),X10,sK2),k1_tops_2(sK0,sK2,X9)) | ~m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) )),
% 1.34/0.55    inference(forward_demodulation,[],[f126,f74])).
% 1.34/0.55  fof(f126,plain,(
% 1.34/0.55    ( ! [X10,X9] : (~m1_subset_1(k1_tops_2(sK0,sK2,X9),k1_zfmisc_1(k1_zfmisc_1(sK2))) | ~r2_hidden(X10,X9) | ~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k9_subset_1(u1_struct_0(sK0),X10,sK2),k1_zfmisc_1(sK2)) | r2_hidden(k9_subset_1(u1_struct_0(sK0),X10,sK2),k1_tops_2(sK0,sK2,X9)) | ~m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) )),
% 1.34/0.55    inference(global_subsumption,[],[f36,f38,f115])).
% 1.34/0.55  fof(f115,plain,(
% 1.34/0.55    ( ! [X10,X9] : (~m1_subset_1(k1_tops_2(sK0,sK2,X9),k1_zfmisc_1(k1_zfmisc_1(sK2))) | ~r2_hidden(X10,X9) | ~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k9_subset_1(u1_struct_0(sK0),X10,sK2),k1_zfmisc_1(sK2)) | r2_hidden(k9_subset_1(u1_struct_0(sK0),X10,sK2),k1_tops_2(sK0,sK2,X9)) | ~m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 1.34/0.55    inference(superposition,[],[f62,f75])).
% 1.34/0.55  fof(f62,plain,(
% 1.34/0.55    ( ! [X2,X0,X8,X1] : (~m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | ~r2_hidden(X8,X2) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k9_subset_1(u1_struct_0(X0),X8,X1),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) | r2_hidden(k9_subset_1(u1_struct_0(X0),X8,X1),k1_tops_2(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.34/0.55    inference(equality_resolution,[],[f61])).
% 1.34/0.55  fof(f61,plain,(
% 1.34/0.55    ( ! [X2,X0,X8,X3,X1] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X8,X1),X3) | ~r2_hidden(X8,X2) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k9_subset_1(u1_struct_0(X0),X8,X1),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) | k1_tops_2(X0,X1,X2) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.34/0.55    inference(equality_resolution,[],[f46])).
% 1.34/0.55  fof(f46,plain,(
% 1.34/0.55    ( ! [X2,X0,X8,X7,X3,X1] : (r2_hidden(X7,X3) | k9_subset_1(u1_struct_0(X0),X8,X1) != X7 | ~r2_hidden(X8,X2) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) | k1_tops_2(X0,X1,X2) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.34/0.55    inference(cnf_transformation,[],[f35])).
% 1.34/0.55  fof(f35,plain,(
% 1.34/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tops_2(X0,X1,X2) = X3 | ((! [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) != sK4(X0,X1,X2,X3) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & ((sK4(X0,X1,X2,X3) = k9_subset_1(u1_struct_0(X0),sK5(X0,X1,X2,X3),X1) & r2_hidden(sK5(X0,X1,X2,X3),X2) & m1_subset_1(sK5(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(sK4(X0,X1,X2,X3),X3)) & m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))) & (! [X7] : (((r2_hidden(X7,X3) | ! [X8] : (k9_subset_1(u1_struct_0(X0),X8,X1) != X7 | ~r2_hidden(X8,X2) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0))))) & ((k9_subset_1(u1_struct_0(X0),sK6(X0,X1,X2,X7),X1) = X7 & r2_hidden(sK6(X0,X1,X2,X7),X2) & m1_subset_1(sK6(X0,X1,X2,X7),k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X7,X3))) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | k1_tops_2(X0,X1,X2) != X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.34/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f31,f34,f33,f32])).
% 1.34/0.55  fof(f32,plain,(
% 1.34/0.55    ! [X3,X2,X1,X0] : (? [X4] : ((! [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X3)) & (? [X6] : (k9_subset_1(u1_struct_0(X0),X6,X1) = X4 & r2_hidden(X6,X2) & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X4,X3)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) => ((! [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) != sK4(X0,X1,X2,X3) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (? [X6] : (k9_subset_1(u1_struct_0(X0),X6,X1) = sK4(X0,X1,X2,X3) & r2_hidden(X6,X2) & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(sK4(X0,X1,X2,X3),X3)) & m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))))),
% 1.34/0.55    introduced(choice_axiom,[])).
% 1.34/0.55  fof(f33,plain,(
% 1.34/0.55    ! [X3,X2,X1,X0] : (? [X6] : (k9_subset_1(u1_struct_0(X0),X6,X1) = sK4(X0,X1,X2,X3) & r2_hidden(X6,X2) & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))) => (sK4(X0,X1,X2,X3) = k9_subset_1(u1_struct_0(X0),sK5(X0,X1,X2,X3),X1) & r2_hidden(sK5(X0,X1,X2,X3),X2) & m1_subset_1(sK5(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.34/0.55    introduced(choice_axiom,[])).
% 1.34/0.55  fof(f34,plain,(
% 1.34/0.55    ! [X7,X2,X1,X0] : (? [X9] : (k9_subset_1(u1_struct_0(X0),X9,X1) = X7 & r2_hidden(X9,X2) & m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),sK6(X0,X1,X2,X7),X1) = X7 & r2_hidden(sK6(X0,X1,X2,X7),X2) & m1_subset_1(sK6(X0,X1,X2,X7),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.34/0.55    introduced(choice_axiom,[])).
% 1.34/0.55  fof(f31,plain,(
% 1.34/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tops_2(X0,X1,X2) = X3 | ? [X4] : ((! [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X3)) & (? [X6] : (k9_subset_1(u1_struct_0(X0),X6,X1) = X4 & r2_hidden(X6,X2) & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X4,X3)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))) & (! [X7] : (((r2_hidden(X7,X3) | ! [X8] : (k9_subset_1(u1_struct_0(X0),X8,X1) != X7 | ~r2_hidden(X8,X2) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X9] : (k9_subset_1(u1_struct_0(X0),X9,X1) = X7 & r2_hidden(X9,X2) & m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X7,X3))) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | k1_tops_2(X0,X1,X2) != X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.34/0.55    inference(rectify,[],[f30])).
% 1.34/0.55  fof(f30,plain,(
% 1.34/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tops_2(X0,X1,X2) = X3 | ? [X4] : ((! [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X3)) & (? [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) = X4 & r2_hidden(X5,X2) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X4,X3)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))) & (! [X4] : (((r2_hidden(X4,X3) | ! [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) = X4 & r2_hidden(X5,X2) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | k1_tops_2(X0,X1,X2) != X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.34/0.55    inference(flattening,[],[f29])).
% 1.34/0.55  fof(f29,plain,(
% 1.34/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tops_2(X0,X1,X2) = X3 | ? [X4] : (((! [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X3)) & (? [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) = X4 & r2_hidden(X5,X2) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))) & (! [X4] : (((r2_hidden(X4,X3) | ! [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) = X4 & r2_hidden(X5,X2) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | k1_tops_2(X0,X1,X2) != X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.34/0.55    inference(nnf_transformation,[],[f16])).
% 1.34/0.55  fof(f16,plain,(
% 1.34/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tops_2(X0,X1,X2) = X3 <=> ! [X4] : ((r2_hidden(X4,X3) <=> ? [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) = X4 & r2_hidden(X5,X2) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.34/0.55    inference(ennf_transformation,[],[f8])).
% 1.34/0.55  fof(f8,axiom,(
% 1.34/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) => (k1_tops_2(X0,X1,X2) = X3 <=> ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) => (r2_hidden(X4,X3) <=> ? [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) = X4 & r2_hidden(X5,X2) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))))))))))),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_2)).
% 1.34/0.55  fof(f40,plain,(
% 1.34/0.55    r2_hidden(sK1,sK3)),
% 1.34/0.55    inference(cnf_transformation,[],[f28])).
% 1.34/0.55  % SZS output end Proof for theBenchmark
% 1.34/0.55  % (26083)------------------------------
% 1.34/0.55  % (26083)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.55  % (26083)Termination reason: Refutation
% 1.34/0.55  
% 1.34/0.55  % (26083)Memory used [KB]: 11385
% 1.34/0.55  % (26083)Time elapsed: 0.137 s
% 1.34/0.55  % (26083)------------------------------
% 1.34/0.55  % (26083)------------------------------
% 1.34/0.55  % (26104)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.34/0.55  % (26097)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.34/0.55  % (26080)Success in time 0.185 s
%------------------------------------------------------------------------------
