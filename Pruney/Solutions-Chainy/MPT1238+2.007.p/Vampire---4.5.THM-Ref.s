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
% DateTime   : Thu Dec  3 13:11:05 EST 2020

% Result     : Theorem 1.40s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 263 expanded)
%              Number of leaves         :   18 (  96 expanded)
%              Depth                    :   10
%              Number of atoms          :  267 ( 909 expanded)
%              Number of equality atoms :    6 (  18 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1754,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f150,f161,f204,f682,f926,f1670,f1745])).

fof(f1745,plain,
    ( ~ spl3_20
    | spl3_28 ),
    inference(avatar_contradiction_clause,[],[f1744])).

fof(f1744,plain,
    ( $false
    | ~ spl3_20
    | spl3_28 ),
    inference(subsumption_resolution,[],[f1743,f29])).

fof(f29,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f24,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X2)))
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
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
               => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tops_1)).

fof(f1743,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_20
    | spl3_28 ),
    inference(subsumption_resolution,[],[f1742,f31])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f1742,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_20
    | spl3_28 ),
    inference(subsumption_resolution,[],[f1741,f672])).

fof(f672,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f671])).

fof(f671,plain,
    ( spl3_20
  <=> m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f1741,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_28 ),
    inference(subsumption_resolution,[],[f1735,f47])).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f35,f36])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f1735,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_28 ),
    inference(resolution,[],[f1722,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

fof(f1722,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | spl3_28 ),
    inference(resolution,[],[f921,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f921,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2))))
    | spl3_28 ),
    inference(avatar_component_clause,[],[f919])).

fof(f919,plain,
    ( spl3_28
  <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f1670,plain,
    ( ~ spl3_20
    | spl3_29 ),
    inference(avatar_contradiction_clause,[],[f1669])).

fof(f1669,plain,
    ( $false
    | ~ spl3_20
    | spl3_29 ),
    inference(subsumption_resolution,[],[f1668,f29])).

fof(f1668,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_20
    | spl3_29 ),
    inference(subsumption_resolution,[],[f1667,f30])).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f1667,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_20
    | spl3_29 ),
    inference(subsumption_resolution,[],[f1666,f672])).

fof(f1666,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_29 ),
    inference(subsumption_resolution,[],[f1660,f35])).

fof(f1660,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_29 ),
    inference(resolution,[],[f1647,f34])).

fof(f1647,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | spl3_29 ),
    inference(resolution,[],[f925,f41])).

fof(f925,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2))))
    | spl3_29 ),
    inference(avatar_component_clause,[],[f923])).

fof(f923,plain,
    ( spl3_29
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f926,plain,
    ( ~ spl3_28
    | ~ spl3_29
    | spl3_11 ),
    inference(avatar_split_clause,[],[f811,f147,f923,f919])).

fof(f147,plain,
    ( spl3_11
  <=> r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f811,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2))))
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2))))
    | spl3_11 ),
    inference(resolution,[],[f360,f244])).

fof(f244,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | spl3_11 ),
    inference(subsumption_resolution,[],[f243,f30])).

fof(f243,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_11 ),
    inference(subsumption_resolution,[],[f242,f31])).

fof(f242,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_11 ),
    inference(superposition,[],[f149,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f149,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f147])).

fof(f360,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f359])).

fof(f359,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f122,f44])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_subset_1(X1,X2,X0),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f43,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f682,plain,(
    spl3_20 ),
    inference(avatar_contradiction_clause,[],[f681])).

fof(f681,plain,
    ( $false
    | spl3_20 ),
    inference(subsumption_resolution,[],[f680,f30])).

fof(f680,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_20 ),
    inference(subsumption_resolution,[],[f679,f31])).

fof(f679,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_20 ),
    inference(resolution,[],[f673,f137])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f136])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f43,f44])).

fof(f673,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_20 ),
    inference(avatar_component_clause,[],[f671])).

fof(f204,plain,(
    spl3_10 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | spl3_10 ),
    inference(subsumption_resolution,[],[f197,f50])).

fof(f50,plain,(
    r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f40,f31])).

fof(f197,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | spl3_10 ),
    inference(resolution,[],[f184,f95])).

fof(f95,plain,(
    r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(subsumption_resolution,[],[f92,f29])).

fof(f92,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f33,f31])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f184,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_tops_1(sK0,sK2),X0)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | spl3_10 ),
    inference(resolution,[],[f183,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
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

fof(f183,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | spl3_10 ),
    inference(resolution,[],[f145,f41])).

fof(f145,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl3_10
  <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f161,plain,(
    spl3_9 ),
    inference(avatar_contradiction_clause,[],[f160])).

fof(f160,plain,
    ( $false
    | spl3_9 ),
    inference(subsumption_resolution,[],[f155,f49])).

fof(f49,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f40,f30])).

fof(f155,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | spl3_9 ),
    inference(resolution,[],[f154,f94])).

fof(f94,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f91,f29])).

fof(f91,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f33,f30])).

fof(f154,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_tops_1(sK0,sK1),X0)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | spl3_9 ),
    inference(resolution,[],[f153,f42])).

fof(f153,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | spl3_9 ),
    inference(resolution,[],[f141,f41])).

fof(f141,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl3_9
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f150,plain,
    ( ~ spl3_9
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f134,f147,f143,f139])).

fof(f134,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f32,f44])).

fof(f32,plain,(
    ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:24:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.47  % (19063)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.48  % (19064)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.49  % (19072)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.49  % (19068)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.49  % (19083)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.51  % (19065)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (19082)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (19078)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.52  % (19060)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.52  % (19075)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.22/0.53  % (19073)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.22/0.53  % (19066)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.22/0.54  % (19067)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.22/0.54  % (19062)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.22/0.54  % (19069)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.40/0.54  % (19061)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.40/0.54  % (19079)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.40/0.54  % (19076)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.40/0.55  % (19084)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.40/0.55  % (19077)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.40/0.55  % (19071)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.40/0.55  % (19074)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.40/0.55  % (19080)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.40/0.56  % (19081)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.40/0.56  % (19070)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.40/0.58  % (19085)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.40/0.62  % (19064)Refutation found. Thanks to Tanya!
% 1.40/0.62  % SZS status Theorem for theBenchmark
% 1.40/0.62  % SZS output start Proof for theBenchmark
% 1.40/0.62  fof(f1754,plain,(
% 1.40/0.62    $false),
% 1.40/0.62    inference(avatar_sat_refutation,[],[f150,f161,f204,f682,f926,f1670,f1745])).
% 1.40/0.62  fof(f1745,plain,(
% 1.40/0.62    ~spl3_20 | spl3_28),
% 1.40/0.62    inference(avatar_contradiction_clause,[],[f1744])).
% 1.40/0.62  fof(f1744,plain,(
% 1.40/0.62    $false | (~spl3_20 | spl3_28)),
% 1.40/0.62    inference(subsumption_resolution,[],[f1743,f29])).
% 1.40/0.62  fof(f29,plain,(
% 1.40/0.62    l1_pre_topc(sK0)),
% 1.40/0.62    inference(cnf_transformation,[],[f25])).
% 1.40/0.62  fof(f25,plain,(
% 1.40/0.62    ((~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 1.40/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f24,f23,f22])).
% 1.40/0.62  fof(f22,plain,(
% 1.40/0.62    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 1.40/0.62    introduced(choice_axiom,[])).
% 1.40/0.62  fof(f23,plain,(
% 1.40/0.62    ? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.40/0.62    introduced(choice_axiom,[])).
% 1.40/0.62  fof(f24,plain,(
% 1.40/0.62    ? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.40/0.62    introduced(choice_axiom,[])).
% 1.40/0.62  fof(f12,plain,(
% 1.40/0.62    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.40/0.62    inference(ennf_transformation,[],[f11])).
% 1.40/0.62  fof(f11,negated_conjecture,(
% 1.40/0.62    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 1.40/0.62    inference(negated_conjecture,[],[f10])).
% 1.40/0.62  fof(f10,conjecture,(
% 1.40/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 1.40/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tops_1)).
% 1.40/0.62  fof(f1743,plain,(
% 1.40/0.62    ~l1_pre_topc(sK0) | (~spl3_20 | spl3_28)),
% 1.40/0.62    inference(subsumption_resolution,[],[f1742,f31])).
% 1.40/0.62  fof(f31,plain,(
% 1.40/0.62    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.40/0.62    inference(cnf_transformation,[],[f25])).
% 1.40/0.62  fof(f1742,plain,(
% 1.40/0.62    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_20 | spl3_28)),
% 1.40/0.62    inference(subsumption_resolution,[],[f1741,f672])).
% 1.40/0.62  fof(f672,plain,(
% 1.40/0.62    m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_20),
% 1.40/0.62    inference(avatar_component_clause,[],[f671])).
% 1.40/0.62  fof(f671,plain,(
% 1.40/0.62    spl3_20 <=> m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.40/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 1.40/0.62  fof(f1741,plain,(
% 1.40/0.62    ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_28),
% 1.40/0.62    inference(subsumption_resolution,[],[f1735,f47])).
% 1.40/0.62  fof(f47,plain,(
% 1.40/0.62    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 1.40/0.62    inference(superposition,[],[f35,f36])).
% 1.40/0.62  fof(f36,plain,(
% 1.40/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.40/0.62    inference(cnf_transformation,[],[f1])).
% 1.40/0.62  fof(f1,axiom,(
% 1.40/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.40/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.40/0.62  fof(f35,plain,(
% 1.40/0.62    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.40/0.62    inference(cnf_transformation,[],[f4])).
% 1.40/0.62  fof(f4,axiom,(
% 1.40/0.62    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.40/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.40/0.62  fof(f1735,plain,(
% 1.40/0.62    ~r1_tarski(sK2,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_28),
% 1.40/0.62    inference(resolution,[],[f1722,f34])).
% 1.40/0.62  fof(f34,plain,(
% 1.40/0.62    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.40/0.62    inference(cnf_transformation,[],[f15])).
% 1.40/0.62  fof(f15,plain,(
% 1.40/0.62    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.40/0.62    inference(flattening,[],[f14])).
% 1.40/0.62  fof(f14,plain,(
% 1.40/0.62    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.40/0.62    inference(ennf_transformation,[],[f9])).
% 1.40/0.62  fof(f9,axiom,(
% 1.40/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 1.40/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).
% 1.40/0.62  fof(f1722,plain,(
% 1.40/0.62    ~r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | spl3_28),
% 1.40/0.62    inference(resolution,[],[f921,f41])).
% 1.40/0.62  fof(f41,plain,(
% 1.40/0.62    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.40/0.62    inference(cnf_transformation,[],[f28])).
% 1.40/0.62  fof(f28,plain,(
% 1.40/0.62    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.40/0.62    inference(nnf_transformation,[],[f7])).
% 1.40/0.62  fof(f7,axiom,(
% 1.40/0.62    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.40/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.40/0.62  fof(f921,plain,(
% 1.40/0.62    ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))) | spl3_28),
% 1.40/0.62    inference(avatar_component_clause,[],[f919])).
% 1.40/0.62  fof(f919,plain,(
% 1.40/0.62    spl3_28 <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2))))),
% 1.40/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 1.40/0.62  fof(f1670,plain,(
% 1.40/0.62    ~spl3_20 | spl3_29),
% 1.40/0.62    inference(avatar_contradiction_clause,[],[f1669])).
% 1.40/0.62  fof(f1669,plain,(
% 1.40/0.62    $false | (~spl3_20 | spl3_29)),
% 1.40/0.62    inference(subsumption_resolution,[],[f1668,f29])).
% 1.40/0.62  fof(f1668,plain,(
% 1.40/0.62    ~l1_pre_topc(sK0) | (~spl3_20 | spl3_29)),
% 1.40/0.62    inference(subsumption_resolution,[],[f1667,f30])).
% 1.40/0.62  fof(f30,plain,(
% 1.40/0.62    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.40/0.62    inference(cnf_transformation,[],[f25])).
% 1.40/0.62  fof(f1667,plain,(
% 1.40/0.62    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_20 | spl3_29)),
% 1.40/0.62    inference(subsumption_resolution,[],[f1666,f672])).
% 1.40/0.62  fof(f1666,plain,(
% 1.40/0.62    ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_29),
% 1.40/0.62    inference(subsumption_resolution,[],[f1660,f35])).
% 1.40/0.62  fof(f1660,plain,(
% 1.40/0.62    ~r1_tarski(sK1,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_29),
% 1.40/0.62    inference(resolution,[],[f1647,f34])).
% 1.40/0.62  fof(f1647,plain,(
% 1.40/0.62    ~r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | spl3_29),
% 1.40/0.62    inference(resolution,[],[f925,f41])).
% 1.40/0.62  fof(f925,plain,(
% 1.40/0.62    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))) | spl3_29),
% 1.40/0.62    inference(avatar_component_clause,[],[f923])).
% 1.40/0.62  fof(f923,plain,(
% 1.40/0.62    spl3_29 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2))))),
% 1.40/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 1.40/0.62  fof(f926,plain,(
% 1.40/0.62    ~spl3_28 | ~spl3_29 | spl3_11),
% 1.40/0.62    inference(avatar_split_clause,[],[f811,f147,f923,f919])).
% 1.40/0.62  fof(f147,plain,(
% 1.40/0.62    spl3_11 <=> r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 1.40/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.40/0.62  fof(f811,plain,(
% 1.40/0.62    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))) | ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))) | spl3_11),
% 1.40/0.62    inference(resolution,[],[f360,f244])).
% 1.40/0.62  fof(f244,plain,(
% 1.40/0.62    ~r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | spl3_11),
% 1.40/0.62    inference(subsumption_resolution,[],[f243,f30])).
% 1.40/0.62  fof(f243,plain,(
% 1.40/0.62    ~r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_11),
% 1.40/0.62    inference(subsumption_resolution,[],[f242,f31])).
% 1.40/0.62  fof(f242,plain,(
% 1.40/0.62    ~r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_11),
% 1.40/0.62    inference(superposition,[],[f149,f44])).
% 1.40/0.62  fof(f44,plain,(
% 1.40/0.62    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.40/0.62    inference(cnf_transformation,[],[f21])).
% 1.40/0.62  fof(f21,plain,(
% 1.40/0.62    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.40/0.62    inference(flattening,[],[f20])).
% 1.40/0.62  fof(f20,plain,(
% 1.40/0.62    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.40/0.62    inference(ennf_transformation,[],[f6])).
% 1.40/0.62  fof(f6,axiom,(
% 1.40/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.40/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.40/0.62  fof(f149,plain,(
% 1.40/0.62    ~r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | spl3_11),
% 1.40/0.62    inference(avatar_component_clause,[],[f147])).
% 1.40/0.62  fof(f360,plain,(
% 1.40/0.62    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.40/0.62    inference(duplicate_literal_removal,[],[f359])).
% 1.40/0.62  fof(f359,plain,(
% 1.40/0.62    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.40/0.62    inference(superposition,[],[f122,f44])).
% 1.40/0.62  fof(f122,plain,(
% 1.40/0.62    ( ! [X2,X0,X1] : (r1_tarski(k4_subset_1(X1,X2,X0),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.40/0.62    inference(resolution,[],[f43,f40])).
% 1.40/0.62  fof(f40,plain,(
% 1.40/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.40/0.62    inference(cnf_transformation,[],[f28])).
% 1.40/0.62  fof(f43,plain,(
% 1.40/0.62    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.40/0.62    inference(cnf_transformation,[],[f19])).
% 1.40/0.62  fof(f19,plain,(
% 1.40/0.62    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.40/0.62    inference(flattening,[],[f18])).
% 1.40/0.62  fof(f18,plain,(
% 1.40/0.62    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.40/0.62    inference(ennf_transformation,[],[f5])).
% 1.40/0.62  fof(f5,axiom,(
% 1.40/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.40/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 1.40/0.62  fof(f682,plain,(
% 1.40/0.62    spl3_20),
% 1.40/0.62    inference(avatar_contradiction_clause,[],[f681])).
% 1.40/0.62  fof(f681,plain,(
% 1.40/0.62    $false | spl3_20),
% 1.40/0.62    inference(subsumption_resolution,[],[f680,f30])).
% 1.40/0.62  fof(f680,plain,(
% 1.40/0.62    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_20),
% 1.40/0.62    inference(subsumption_resolution,[],[f679,f31])).
% 1.40/0.62  fof(f679,plain,(
% 1.40/0.62    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_20),
% 1.40/0.62    inference(resolution,[],[f673,f137])).
% 1.40/0.62  fof(f137,plain,(
% 1.40/0.62    ( ! [X2,X0,X1] : (m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.40/0.62    inference(duplicate_literal_removal,[],[f136])).
% 1.40/0.62  fof(f136,plain,(
% 1.40/0.62    ( ! [X2,X0,X1] : (m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.40/0.62    inference(superposition,[],[f43,f44])).
% 1.40/0.62  fof(f673,plain,(
% 1.40/0.62    ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_20),
% 1.40/0.62    inference(avatar_component_clause,[],[f671])).
% 1.40/0.62  fof(f204,plain,(
% 1.40/0.62    spl3_10),
% 1.40/0.62    inference(avatar_contradiction_clause,[],[f203])).
% 1.40/0.62  fof(f203,plain,(
% 1.40/0.62    $false | spl3_10),
% 1.40/0.62    inference(subsumption_resolution,[],[f197,f50])).
% 1.40/0.62  fof(f50,plain,(
% 1.40/0.62    r1_tarski(sK2,u1_struct_0(sK0))),
% 1.40/0.62    inference(resolution,[],[f40,f31])).
% 1.40/0.62  fof(f197,plain,(
% 1.40/0.62    ~r1_tarski(sK2,u1_struct_0(sK0)) | spl3_10),
% 1.40/0.62    inference(resolution,[],[f184,f95])).
% 1.40/0.62  fof(f95,plain,(
% 1.40/0.62    r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 1.40/0.62    inference(subsumption_resolution,[],[f92,f29])).
% 1.40/0.62  fof(f92,plain,(
% 1.40/0.62    r1_tarski(k1_tops_1(sK0,sK2),sK2) | ~l1_pre_topc(sK0)),
% 1.40/0.62    inference(resolution,[],[f33,f31])).
% 1.40/0.62  fof(f33,plain,(
% 1.40/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 1.40/0.62    inference(cnf_transformation,[],[f13])).
% 1.40/0.62  fof(f13,plain,(
% 1.40/0.62    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.40/0.62    inference(ennf_transformation,[],[f8])).
% 1.40/0.62  fof(f8,axiom,(
% 1.40/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 1.40/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 1.40/0.62  fof(f184,plain,(
% 1.40/0.62    ( ! [X0] : (~r1_tarski(k1_tops_1(sK0,sK2),X0) | ~r1_tarski(X0,u1_struct_0(sK0))) ) | spl3_10),
% 1.40/0.62    inference(resolution,[],[f183,f42])).
% 1.40/0.62  fof(f42,plain,(
% 1.40/0.62    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.40/0.62    inference(cnf_transformation,[],[f17])).
% 1.40/0.62  fof(f17,plain,(
% 1.40/0.62    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.40/0.62    inference(flattening,[],[f16])).
% 1.40/0.62  fof(f16,plain,(
% 1.40/0.62    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.40/0.62    inference(ennf_transformation,[],[f3])).
% 1.40/0.62  fof(f3,axiom,(
% 1.40/0.62    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.40/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.40/0.62  fof(f183,plain,(
% 1.40/0.62    ~r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) | spl3_10),
% 1.40/0.62    inference(resolution,[],[f145,f41])).
% 1.40/0.62  fof(f145,plain,(
% 1.40/0.62    ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_10),
% 1.40/0.62    inference(avatar_component_clause,[],[f143])).
% 1.40/0.62  fof(f143,plain,(
% 1.40/0.62    spl3_10 <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.40/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.40/0.62  fof(f161,plain,(
% 1.40/0.62    spl3_9),
% 1.40/0.62    inference(avatar_contradiction_clause,[],[f160])).
% 1.40/0.62  fof(f160,plain,(
% 1.40/0.62    $false | spl3_9),
% 1.40/0.62    inference(subsumption_resolution,[],[f155,f49])).
% 1.40/0.62  fof(f49,plain,(
% 1.40/0.62    r1_tarski(sK1,u1_struct_0(sK0))),
% 1.40/0.62    inference(resolution,[],[f40,f30])).
% 1.40/0.62  fof(f155,plain,(
% 1.40/0.62    ~r1_tarski(sK1,u1_struct_0(sK0)) | spl3_9),
% 1.40/0.62    inference(resolution,[],[f154,f94])).
% 1.40/0.62  fof(f94,plain,(
% 1.40/0.62    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 1.40/0.62    inference(subsumption_resolution,[],[f91,f29])).
% 1.40/0.62  fof(f91,plain,(
% 1.40/0.62    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0)),
% 1.40/0.62    inference(resolution,[],[f33,f30])).
% 1.40/0.62  fof(f154,plain,(
% 1.40/0.62    ( ! [X0] : (~r1_tarski(k1_tops_1(sK0,sK1),X0) | ~r1_tarski(X0,u1_struct_0(sK0))) ) | spl3_9),
% 1.40/0.62    inference(resolution,[],[f153,f42])).
% 1.40/0.62  fof(f153,plain,(
% 1.40/0.62    ~r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | spl3_9),
% 1.40/0.62    inference(resolution,[],[f141,f41])).
% 1.40/0.62  fof(f141,plain,(
% 1.40/0.62    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_9),
% 1.40/0.62    inference(avatar_component_clause,[],[f139])).
% 1.40/0.62  fof(f139,plain,(
% 1.40/0.62    spl3_9 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.40/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.40/0.62  fof(f150,plain,(
% 1.40/0.62    ~spl3_9 | ~spl3_10 | ~spl3_11),
% 1.40/0.62    inference(avatar_split_clause,[],[f134,f147,f143,f139])).
% 1.40/0.62  fof(f134,plain,(
% 1.40/0.62    ~r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.40/0.62    inference(superposition,[],[f32,f44])).
% 1.40/0.62  fof(f32,plain,(
% 1.40/0.62    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 1.40/0.62    inference(cnf_transformation,[],[f25])).
% 1.40/0.62  % SZS output end Proof for theBenchmark
% 1.40/0.62  % (19064)------------------------------
% 1.40/0.62  % (19064)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.62  % (19064)Termination reason: Refutation
% 1.40/0.62  
% 1.40/0.62  % (19064)Memory used [KB]: 6908
% 1.40/0.62  % (19064)Time elapsed: 0.216 s
% 1.40/0.62  % (19064)------------------------------
% 1.40/0.62  % (19064)------------------------------
% 2.09/0.64  % (19059)Success in time 0.271 s
%------------------------------------------------------------------------------
