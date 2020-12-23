%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:35 EST 2020

% Result     : Theorem 2.51s
% Output     : Refutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :  126 (1077 expanded)
%              Number of leaves         :   19 ( 325 expanded)
%              Depth                    :   24
%              Number of atoms          :  443 (6641 expanded)
%              Number of equality atoms :   24 ( 514 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3554,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2676,f2681,f3395,f3553])).

fof(f3553,plain,(
    ~ spl5_25 ),
    inference(avatar_contradiction_clause,[],[f3552])).

fof(f3552,plain,
    ( $false
    | ~ spl5_25 ),
    inference(subsumption_resolution,[],[f3551,f2606])).

fof(f2606,plain,(
    r1_tarski(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f2541,f170])).

fof(f170,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(subsumption_resolution,[],[f169,f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1,X1),X0)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(subsumption_resolution,[],[f130,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & ~ r2_hidden(sK4(X0,X1,X2),X0) )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( r2_hidden(sK4(X0,X1,X2),X1)
            | r2_hidden(sK4(X0,X1,X2),X0)
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & ~ r2_hidden(sK4(X0,X1,X2),X0) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( r2_hidden(sK4(X0,X1,X2),X1)
          | r2_hidden(sK4(X0,X1,X2),X0)
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f130,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1,X1),X1)
      | r2_hidden(sK4(X0,X1,X1),X0)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(factoring,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X2)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f169,plain,(
    ! [X0] :
      ( k2_xboole_0(X0,X0) = X0
      | ~ r2_hidden(sK4(X0,X0,X0),X0) ) ),
    inference(duplicate_literal_removal,[],[f165])).

fof(f165,plain,(
    ! [X0] :
      ( k2_xboole_0(X0,X0) = X0
      | ~ r2_hidden(sK4(X0,X0,X0),X0)
      | k2_xboole_0(X0,X0) = X0 ) ),
    inference(resolution,[],[f134,f61])).

fof(f2541,plain,(
    ! [X0] : r1_tarski(k2_xboole_0(sK1,sK2),k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f1645,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f1645,plain,(
    ! [X7] : r1_tarski(k4_xboole_0(k2_xboole_0(sK1,sK2),X7),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f1612,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1612,plain,(
    ! [X7] : r1_tarski(k4_xboole_0(k2_xboole_0(sK2,sK1),X7),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f93,f1042])).

fof(f1042,plain,(
    ! [X1] :
      ( ~ r1_tarski(k4_xboole_0(X1,sK2),sK1)
      | r1_tarski(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f530,f515])).

fof(f515,plain,(
    ! [X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK0))),X1)
      | ~ r1_tarski(k4_xboole_0(X0,X1),sK1) ) ),
    inference(resolution,[],[f117,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k2_xboole_0(X1,X0))
      | r1_tarski(k4_xboole_0(X2,X0),X1) ) ),
    inference(superposition,[],[f53,f50])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f117,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ r1_tarski(k4_xboole_0(X0,X1),sK1) ) ),
    inference(resolution,[],[f110,f54])).

fof(f110,plain,(
    ! [X4] :
      ( r1_tarski(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X4,sK1) ) ),
    inference(resolution,[],[f103,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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

fof(f103,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ r1_tarski(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f100,f65])).

fof(f65,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f44,f37])).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    & v2_tops_2(sK2,sK0)
    & v2_tops_2(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f25,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
                & v2_tops_2(X2,X0)
                & v2_tops_2(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0)
              & v2_tops_2(X2,sK0)
              & v2_tops_2(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0)
            & v2_tops_2(X2,sK0)
            & v2_tops_2(X1,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ? [X2] :
          ( ~ v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0)
          & v2_tops_2(X2,sK0)
          & v2_tops_2(sK1,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X2] :
        ( ~ v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0)
        & v2_tops_2(X2,sK0)
        & v2_tops_2(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ~ v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
      & v2_tops_2(sK2,sK0)
      & v2_tops_2(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v2_tops_2(X2,X0)
              & v2_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v2_tops_2(X2,X0)
              & v2_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( ( v2_tops_2(X2,X0)
                    & v2_tops_2(X1,X0) )
                 => v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( ( v2_tops_2(X2,X0)
                  & v2_tops_2(X1,X0) )
               => v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tops_2)).

fof(f44,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f100,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ l1_struct_0(sK0) ) ),
    inference(resolution,[],[f43,f38])).

fof(f38,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f26])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r1_tarski(X2,X1)
      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              | ~ r1_tarski(X2,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( r1_tarski(X2,X1)
             => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_tops_2)).

fof(f530,plain,(
    ! [X4] :
      ( ~ r1_tarski(k4_xboole_0(X4,k1_zfmisc_1(u1_struct_0(sK0))),sK2)
      | r1_tarski(X4,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f151,f170])).

fof(f151,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ r1_tarski(k4_xboole_0(X0,X1),sK2) ) ),
    inference(resolution,[],[f140,f54])).

fof(f140,plain,(
    ! [X6] :
      ( r1_tarski(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X6,sK2) ) ),
    inference(resolution,[],[f104,f51])).

fof(f104,plain,(
    ! [X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ r1_tarski(X1,sK2) ) ),
    inference(subsumption_resolution,[],[f101,f65])).

fof(f101,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,sK2)
      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ l1_struct_0(sK0) ) ),
    inference(resolution,[],[f43,f39])).

fof(f39,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f26])).

fof(f93,plain,(
    ! [X4,X2,X3] : r1_tarski(k4_xboole_0(k4_xboole_0(k2_xboole_0(X2,X3),X4),X2),X3) ),
    inference(resolution,[],[f78,f53])).

fof(f78,plain,(
    ! [X2,X3] : r1_tarski(k4_xboole_0(X2,X3),X2) ),
    inference(resolution,[],[f53,f66])).

fof(f66,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f49,f50])).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f3551,plain,
    ( ~ r1_tarski(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_25 ),
    inference(subsumption_resolution,[],[f3550,f37])).

fof(f3550,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ r1_tarski(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_25 ),
    inference(subsumption_resolution,[],[f3541,f99])).

fof(f99,plain,(
    ~ v2_tops_2(k2_xboole_0(sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f98,f38])).

fof(f98,plain,
    ( ~ v2_tops_2(k2_xboole_0(sK1,sK2),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f97,f39])).

fof(f97,plain,
    ( ~ v2_tops_2(k2_xboole_0(sK1,sK2),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(superposition,[],[f42,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f42,plain,(
    ~ v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f3541,plain,
    ( v2_tops_2(k2_xboole_0(sK1,sK2),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ r1_tarski(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_25 ),
    inference(resolution,[],[f2672,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(sK3(X0,X1),X0)
      | v2_tops_2(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(resolution,[],[f48,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v4_pre_topc(sK3(X0,X1),X0)
      | v2_tops_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ( ~ v4_pre_topc(sK3(X0,X1),X0)
                & r2_hidden(sK3(X0,X1),X1)
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v4_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v4_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK3(X0,X1),X0)
        & r2_hidden(sK3(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v4_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v4_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v4_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v4_pre_topc(X2,X0)
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v4_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_2)).

fof(f2672,plain,
    ( v4_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0)
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f2671])).

fof(f2671,plain,
    ( spl5_25
  <=> v4_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f3395,plain,
    ( spl5_26
    | spl5_27 ),
    inference(avatar_contradiction_clause,[],[f3394])).

fof(f3394,plain,
    ( $false
    | spl5_26
    | spl5_27 ),
    inference(subsumption_resolution,[],[f3393,f2680])).

fof(f2680,plain,
    ( ~ r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2)
    | spl5_27 ),
    inference(avatar_component_clause,[],[f2679])).

fof(f2679,plain,
    ( spl5_27
  <=> r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f3393,plain,
    ( r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2)
    | spl5_26 ),
    inference(subsumption_resolution,[],[f3392,f2675])).

fof(f2675,plain,
    ( ~ r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1)
    | spl5_26 ),
    inference(avatar_component_clause,[],[f2674])).

fof(f2674,plain,
    ( spl5_26
  <=> r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f3392,plain,
    ( r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1)
    | r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2) ),
    inference(resolution,[],[f2685,f64])).

fof(f64,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_xboole_0(X0,X1))
      | r2_hidden(X4,X0)
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f2685,plain,(
    r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f2684,f37])).

fof(f2684,plain,
    ( ~ l1_pre_topc(sK0)
    | r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f2668,f99])).

fof(f2668,plain,
    ( v2_tops_2(k2_xboole_0(sK1,sK2),sK0)
    | ~ l1_pre_topc(sK0)
    | r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f2606,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tops_2(X1,X0)
      | ~ l1_pre_topc(X0)
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(resolution,[],[f47,f52])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | r2_hidden(sK3(X0,X1),X1)
      | v2_tops_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2681,plain,
    ( spl5_25
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f2677,f2679,f2671])).

fof(f2677,plain,
    ( ~ r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2)
    | v4_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0) ),
    inference(subsumption_resolution,[],[f2657,f99])).

fof(f2657,plain,
    ( v2_tops_2(k2_xboole_0(sK1,sK2),sK0)
    | ~ r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2)
    | v4_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0) ),
    inference(resolution,[],[f2606,f356])).

fof(f356,plain,(
    ! [X8] :
      ( ~ r1_tarski(X8,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tops_2(X8,sK0)
      | ~ r2_hidden(sK3(sK0,X8),sK2)
      | v4_pre_topc(sK3(sK0,X8),sK0) ) ),
    inference(resolution,[],[f150,f52])).

fof(f150,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | v4_pre_topc(sK3(sK0,X0),sK0)
      | v2_tops_2(X0,sK0)
      | ~ r2_hidden(sK3(sK0,X0),sK2) ) ),
    inference(subsumption_resolution,[],[f148,f37])).

fof(f148,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(sK0,X0),sK2)
      | v4_pre_topc(sK3(sK0,X0),sK0)
      | v2_tops_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f125,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f125,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X1,sK2)
      | v4_pre_topc(X1,sK0) ) ),
    inference(subsumption_resolution,[],[f124,f37])).

fof(f124,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_pre_topc(X1,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f119,f41])).

fof(f41,plain,(
    v2_tops_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f119,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tops_2(sK2,sK0)
      | v4_pre_topc(X1,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f45,f39])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_2(X1,X0)
      | v4_pre_topc(X3,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2676,plain,
    ( spl5_25
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f2669,f2674,f2671])).

fof(f2669,plain,
    ( ~ r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1)
    | v4_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0) ),
    inference(subsumption_resolution,[],[f2655,f99])).

fof(f2655,plain,
    ( v2_tops_2(k2_xboole_0(sK1,sK2),sK0)
    | ~ r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1)
    | v4_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0) ),
    inference(resolution,[],[f2606,f345])).

fof(f345,plain,(
    ! [X8] :
      ( ~ r1_tarski(X8,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tops_2(X8,sK0)
      | ~ r2_hidden(sK3(sK0,X8),sK1)
      | v4_pre_topc(sK3(sK0,X8),sK0) ) ),
    inference(resolution,[],[f147,f52])).

fof(f147,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | v4_pre_topc(sK3(sK0,X0),sK0)
      | v2_tops_2(X0,sK0)
      | ~ r2_hidden(sK3(sK0,X0),sK1) ) ),
    inference(subsumption_resolution,[],[f145,f37])).

fof(f145,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(sK0,X0),sK1)
      | v4_pre_topc(sK3(sK0,X0),sK0)
      | v2_tops_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f123,f46])).

fof(f123,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,sK1)
      | v4_pre_topc(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f122,f37])).

fof(f122,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f118,f40])).

fof(f40,plain,(
    v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f118,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tops_2(sK1,sK0)
      | v4_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f45,f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:52:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (20922)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (20929)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.47  % (20923)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.47  % (20925)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (20931)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.48  % (20924)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (20931)Refutation not found, incomplete strategy% (20931)------------------------------
% 0.21/0.48  % (20931)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (20931)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (20931)Memory used [KB]: 6140
% 0.21/0.48  % (20931)Time elapsed: 0.076 s
% 0.21/0.48  % (20931)------------------------------
% 0.21/0.48  % (20931)------------------------------
% 0.21/0.48  % (20937)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  % (20921)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (20921)Refutation not found, incomplete strategy% (20921)------------------------------
% 0.21/0.49  % (20921)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (20921)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (20921)Memory used [KB]: 6140
% 0.21/0.49  % (20921)Time elapsed: 0.082 s
% 0.21/0.49  % (20921)------------------------------
% 0.21/0.49  % (20921)------------------------------
% 0.21/0.49  % (20926)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (20928)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (20933)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (20932)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.49  % (20927)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (20932)Refutation not found, incomplete strategy% (20932)------------------------------
% 0.21/0.50  % (20932)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (20932)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (20932)Memory used [KB]: 10618
% 0.21/0.50  % (20932)Time elapsed: 0.090 s
% 0.21/0.50  % (20932)------------------------------
% 0.21/0.50  % (20932)------------------------------
% 0.21/0.50  % (20930)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.50  % (20934)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.50  % (20941)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.50  % (20942)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (20940)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.51  % (20938)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.51  % (20939)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.52  % (20935)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 2.51/0.69  % (20923)Refutation found. Thanks to Tanya!
% 2.51/0.69  % SZS status Theorem for theBenchmark
% 2.51/0.69  % SZS output start Proof for theBenchmark
% 2.51/0.69  fof(f3554,plain,(
% 2.51/0.69    $false),
% 2.51/0.69    inference(avatar_sat_refutation,[],[f2676,f2681,f3395,f3553])).
% 2.51/0.69  fof(f3553,plain,(
% 2.51/0.69    ~spl5_25),
% 2.51/0.69    inference(avatar_contradiction_clause,[],[f3552])).
% 2.51/0.69  fof(f3552,plain,(
% 2.51/0.69    $false | ~spl5_25),
% 2.51/0.69    inference(subsumption_resolution,[],[f3551,f2606])).
% 2.51/0.69  fof(f2606,plain,(
% 2.51/0.69    r1_tarski(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.51/0.69    inference(superposition,[],[f2541,f170])).
% 2.51/0.69  fof(f170,plain,(
% 2.51/0.69    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.51/0.69    inference(subsumption_resolution,[],[f169,f134])).
% 2.51/0.69  fof(f134,plain,(
% 2.51/0.69    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1,X1),X0) | k2_xboole_0(X0,X1) = X1) )),
% 2.51/0.69    inference(subsumption_resolution,[],[f130,f61])).
% 2.51/0.69  fof(f61,plain,(
% 2.51/0.69    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X2) | ~r2_hidden(sK4(X0,X1,X2),X1) | k2_xboole_0(X0,X1) = X2) )),
% 2.51/0.69    inference(cnf_transformation,[],[f36])).
% 2.51/0.69  fof(f36,plain,(
% 2.51/0.69    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.51/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).
% 2.51/0.69  fof(f35,plain,(
% 2.51/0.69    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 2.51/0.69    introduced(choice_axiom,[])).
% 2.51/0.69  fof(f34,plain,(
% 2.51/0.69    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.51/0.69    inference(rectify,[],[f33])).
% 2.51/0.69  fof(f33,plain,(
% 2.51/0.69    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.51/0.69    inference(flattening,[],[f32])).
% 2.51/0.69  fof(f32,plain,(
% 2.51/0.69    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.51/0.69    inference(nnf_transformation,[],[f2])).
% 2.51/0.69  fof(f2,axiom,(
% 2.51/0.69    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 2.51/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 2.51/0.69  fof(f130,plain,(
% 2.51/0.69    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1,X1),X1) | r2_hidden(sK4(X0,X1,X1),X0) | k2_xboole_0(X0,X1) = X1) )),
% 2.51/0.69    inference(factoring,[],[f59])).
% 2.51/0.69  fof(f59,plain,(
% 2.51/0.69    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X2) | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | k2_xboole_0(X0,X1) = X2) )),
% 2.51/0.69    inference(cnf_transformation,[],[f36])).
% 2.51/0.69  fof(f169,plain,(
% 2.51/0.69    ( ! [X0] : (k2_xboole_0(X0,X0) = X0 | ~r2_hidden(sK4(X0,X0,X0),X0)) )),
% 2.51/0.69    inference(duplicate_literal_removal,[],[f165])).
% 2.51/0.69  fof(f165,plain,(
% 2.51/0.69    ( ! [X0] : (k2_xboole_0(X0,X0) = X0 | ~r2_hidden(sK4(X0,X0,X0),X0) | k2_xboole_0(X0,X0) = X0) )),
% 2.51/0.69    inference(resolution,[],[f134,f61])).
% 2.51/0.69  fof(f2541,plain,(
% 2.51/0.69    ( ! [X0] : (r1_tarski(k2_xboole_0(sK1,sK2),k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK0))))) )),
% 2.51/0.69    inference(resolution,[],[f1645,f54])).
% 2.51/0.69  fof(f54,plain,(
% 2.51/0.69    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 2.51/0.69    inference(cnf_transformation,[],[f20])).
% 2.51/0.69  fof(f20,plain,(
% 2.51/0.69    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.51/0.69    inference(ennf_transformation,[],[f4])).
% 2.51/0.69  fof(f4,axiom,(
% 2.51/0.69    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.51/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 2.51/0.69  fof(f1645,plain,(
% 2.51/0.69    ( ! [X7] : (r1_tarski(k4_xboole_0(k2_xboole_0(sK1,sK2),X7),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.51/0.69    inference(forward_demodulation,[],[f1612,f50])).
% 2.51/0.69  fof(f50,plain,(
% 2.51/0.69    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.51/0.69    inference(cnf_transformation,[],[f1])).
% 2.51/0.69  fof(f1,axiom,(
% 2.51/0.69    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.51/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.51/0.69  fof(f1612,plain,(
% 2.51/0.69    ( ! [X7] : (r1_tarski(k4_xboole_0(k2_xboole_0(sK2,sK1),X7),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.51/0.69    inference(resolution,[],[f93,f1042])).
% 2.51/0.69  fof(f1042,plain,(
% 2.51/0.69    ( ! [X1] : (~r1_tarski(k4_xboole_0(X1,sK2),sK1) | r1_tarski(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.51/0.69    inference(resolution,[],[f530,f515])).
% 2.51/0.69  fof(f515,plain,(
% 2.51/0.69    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK0))),X1) | ~r1_tarski(k4_xboole_0(X0,X1),sK1)) )),
% 2.51/0.69    inference(resolution,[],[f117,f79])).
% 2.51/0.69  fof(f79,plain,(
% 2.51/0.69    ( ! [X2,X0,X1] : (~r1_tarski(X2,k2_xboole_0(X1,X0)) | r1_tarski(k4_xboole_0(X2,X0),X1)) )),
% 2.51/0.69    inference(superposition,[],[f53,f50])).
% 2.51/0.69  fof(f53,plain,(
% 2.51/0.69    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 2.51/0.69    inference(cnf_transformation,[],[f19])).
% 2.51/0.69  fof(f19,plain,(
% 2.51/0.69    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.51/0.69    inference(ennf_transformation,[],[f3])).
% 2.51/0.69  fof(f3,axiom,(
% 2.51/0.69    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.51/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 2.51/0.69  fof(f117,plain,(
% 2.51/0.69    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(k4_xboole_0(X0,X1),sK1)) )),
% 2.51/0.69    inference(resolution,[],[f110,f54])).
% 2.51/0.69  fof(f110,plain,(
% 2.51/0.69    ( ! [X4] : (r1_tarski(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X4,sK1)) )),
% 2.51/0.69    inference(resolution,[],[f103,f51])).
% 2.51/0.69  fof(f51,plain,(
% 2.51/0.69    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.51/0.69    inference(cnf_transformation,[],[f31])).
% 2.51/0.69  fof(f31,plain,(
% 2.51/0.69    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.51/0.69    inference(nnf_transformation,[],[f7])).
% 2.51/0.69  fof(f7,axiom,(
% 2.51/0.69    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.51/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.51/0.69  fof(f103,plain,(
% 2.51/0.69    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(X0,sK1)) )),
% 2.51/0.69    inference(subsumption_resolution,[],[f100,f65])).
% 2.51/0.69  fof(f65,plain,(
% 2.51/0.69    l1_struct_0(sK0)),
% 2.51/0.69    inference(resolution,[],[f44,f37])).
% 2.51/0.69  fof(f37,plain,(
% 2.51/0.69    l1_pre_topc(sK0)),
% 2.51/0.69    inference(cnf_transformation,[],[f26])).
% 2.51/0.69  fof(f26,plain,(
% 2.51/0.69    ((~v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) & v2_tops_2(sK2,sK0) & v2_tops_2(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0)),
% 2.51/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f25,f24,f23])).
% 2.51/0.69  fof(f23,plain,(
% 2.51/0.69    ? [X0] : (? [X1] : (? [X2] : (~v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X2,X0) & v2_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0) & v2_tops_2(X2,sK0) & v2_tops_2(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0))),
% 2.51/0.69    introduced(choice_axiom,[])).
% 2.51/0.69  fof(f24,plain,(
% 2.51/0.69    ? [X1] : (? [X2] : (~v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0) & v2_tops_2(X2,sK0) & v2_tops_2(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (? [X2] : (~v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0) & v2_tops_2(X2,sK0) & v2_tops_2(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 2.51/0.69    introduced(choice_axiom,[])).
% 2.51/0.69  fof(f25,plain,(
% 2.51/0.69    ? [X2] : (~v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0) & v2_tops_2(X2,sK0) & v2_tops_2(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (~v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) & v2_tops_2(sK2,sK0) & v2_tops_2(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 2.51/0.69    introduced(choice_axiom,[])).
% 2.51/0.69  fof(f14,plain,(
% 2.51/0.69    ? [X0] : (? [X1] : (? [X2] : (~v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X2,X0) & v2_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 2.51/0.69    inference(flattening,[],[f13])).
% 2.51/0.69  fof(f13,plain,(
% 2.51/0.69    ? [X0] : (? [X1] : (? [X2] : ((~v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & (v2_tops_2(X2,X0) & v2_tops_2(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 2.51/0.69    inference(ennf_transformation,[],[f12])).
% 2.51/0.69  fof(f12,negated_conjecture,(
% 2.51/0.69    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v2_tops_2(X2,X0) & v2_tops_2(X1,X0)) => v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 2.51/0.69    inference(negated_conjecture,[],[f11])).
% 2.51/0.69  fof(f11,conjecture,(
% 2.51/0.69    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v2_tops_2(X2,X0) & v2_tops_2(X1,X0)) => v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 2.51/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tops_2)).
% 2.51/0.69  fof(f44,plain,(
% 2.51/0.69    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 2.51/0.69    inference(cnf_transformation,[],[f16])).
% 2.51/0.69  fof(f16,plain,(
% 2.51/0.69    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.51/0.69    inference(ennf_transformation,[],[f8])).
% 2.51/0.69  fof(f8,axiom,(
% 2.51/0.69    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.51/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 2.51/0.69  fof(f100,plain,(
% 2.51/0.69    ( ! [X0] : (~r1_tarski(X0,sK1) | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_struct_0(sK0)) )),
% 2.51/0.69    inference(resolution,[],[f43,f38])).
% 2.51/0.69  fof(f38,plain,(
% 2.51/0.69    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.51/0.69    inference(cnf_transformation,[],[f26])).
% 2.51/0.69  fof(f43,plain,(
% 2.51/0.69    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0)) )),
% 2.51/0.69    inference(cnf_transformation,[],[f15])).
% 2.51/0.69  fof(f15,plain,(
% 2.51/0.69    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_struct_0(X0))),
% 2.51/0.69    inference(ennf_transformation,[],[f10])).
% 2.51/0.69  fof(f10,axiom,(
% 2.51/0.69    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (r1_tarski(X2,X1) => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))))),
% 2.51/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_tops_2)).
% 2.51/0.69  fof(f530,plain,(
% 2.51/0.69    ( ! [X4] : (~r1_tarski(k4_xboole_0(X4,k1_zfmisc_1(u1_struct_0(sK0))),sK2) | r1_tarski(X4,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.51/0.69    inference(superposition,[],[f151,f170])).
% 2.51/0.69  fof(f151,plain,(
% 2.51/0.69    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(k4_xboole_0(X0,X1),sK2)) )),
% 2.51/0.69    inference(resolution,[],[f140,f54])).
% 2.51/0.69  fof(f140,plain,(
% 2.51/0.69    ( ! [X6] : (r1_tarski(X6,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X6,sK2)) )),
% 2.51/0.69    inference(resolution,[],[f104,f51])).
% 2.51/0.69  fof(f104,plain,(
% 2.51/0.69    ( ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(X1,sK2)) )),
% 2.51/0.69    inference(subsumption_resolution,[],[f101,f65])).
% 2.51/0.69  fof(f101,plain,(
% 2.51/0.69    ( ! [X1] : (~r1_tarski(X1,sK2) | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_struct_0(sK0)) )),
% 2.51/0.69    inference(resolution,[],[f43,f39])).
% 2.51/0.69  fof(f39,plain,(
% 2.51/0.69    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.51/0.69    inference(cnf_transformation,[],[f26])).
% 2.51/0.69  fof(f93,plain,(
% 2.51/0.69    ( ! [X4,X2,X3] : (r1_tarski(k4_xboole_0(k4_xboole_0(k2_xboole_0(X2,X3),X4),X2),X3)) )),
% 2.51/0.69    inference(resolution,[],[f78,f53])).
% 2.51/0.69  fof(f78,plain,(
% 2.51/0.69    ( ! [X2,X3] : (r1_tarski(k4_xboole_0(X2,X3),X2)) )),
% 2.51/0.69    inference(resolution,[],[f53,f66])).
% 2.51/0.69  fof(f66,plain,(
% 2.51/0.69    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 2.51/0.69    inference(superposition,[],[f49,f50])).
% 2.51/0.69  fof(f49,plain,(
% 2.51/0.69    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.51/0.69    inference(cnf_transformation,[],[f5])).
% 2.51/0.69  fof(f5,axiom,(
% 2.51/0.69    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.51/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.51/0.69  fof(f3551,plain,(
% 2.51/0.69    ~r1_tarski(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_25),
% 2.51/0.69    inference(subsumption_resolution,[],[f3550,f37])).
% 2.51/0.69  fof(f3550,plain,(
% 2.51/0.69    ~l1_pre_topc(sK0) | ~r1_tarski(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_25),
% 2.51/0.69    inference(subsumption_resolution,[],[f3541,f99])).
% 2.51/0.69  fof(f99,plain,(
% 2.51/0.69    ~v2_tops_2(k2_xboole_0(sK1,sK2),sK0)),
% 2.51/0.69    inference(subsumption_resolution,[],[f98,f38])).
% 2.51/0.69  fof(f98,plain,(
% 2.51/0.69    ~v2_tops_2(k2_xboole_0(sK1,sK2),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.51/0.69    inference(subsumption_resolution,[],[f97,f39])).
% 2.51/0.69  fof(f97,plain,(
% 2.51/0.69    ~v2_tops_2(k2_xboole_0(sK1,sK2),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.51/0.69    inference(superposition,[],[f42,f55])).
% 2.51/0.69  fof(f55,plain,(
% 2.51/0.69    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.51/0.69    inference(cnf_transformation,[],[f22])).
% 2.51/0.69  fof(f22,plain,(
% 2.51/0.69    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.51/0.69    inference(flattening,[],[f21])).
% 2.51/0.69  fof(f21,plain,(
% 2.51/0.69    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.51/0.69    inference(ennf_transformation,[],[f6])).
% 2.51/0.69  fof(f6,axiom,(
% 2.51/0.69    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 2.51/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.51/0.69  fof(f42,plain,(
% 2.51/0.69    ~v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)),
% 2.51/0.69    inference(cnf_transformation,[],[f26])).
% 2.51/0.69  fof(f3541,plain,(
% 2.51/0.69    v2_tops_2(k2_xboole_0(sK1,sK2),sK0) | ~l1_pre_topc(sK0) | ~r1_tarski(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_25),
% 2.51/0.69    inference(resolution,[],[f2672,f96])).
% 2.51/0.69  fof(f96,plain,(
% 2.51/0.69    ( ! [X0,X1] : (~v4_pre_topc(sK3(X0,X1),X0) | v2_tops_2(X1,X0) | ~l1_pre_topc(X0) | ~r1_tarski(X1,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 2.51/0.69    inference(resolution,[],[f48,f52])).
% 2.51/0.69  fof(f52,plain,(
% 2.51/0.69    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.51/0.69    inference(cnf_transformation,[],[f31])).
% 2.51/0.69  fof(f48,plain,(
% 2.51/0.69    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_pre_topc(sK3(X0,X1),X0) | v2_tops_2(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.51/0.69    inference(cnf_transformation,[],[f30])).
% 2.51/0.69  fof(f30,plain,(
% 2.51/0.69    ! [X0] : (! [X1] : (((v2_tops_2(X1,X0) | (~v4_pre_topc(sK3(X0,X1),X0) & r2_hidden(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v4_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 2.51/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f29])).
% 2.51/0.69  fof(f29,plain,(
% 2.51/0.69    ! [X1,X0] : (? [X2] : (~v4_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v4_pre_topc(sK3(X0,X1),X0) & r2_hidden(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.51/0.69    introduced(choice_axiom,[])).
% 2.51/0.69  fof(f28,plain,(
% 2.51/0.69    ! [X0] : (! [X1] : (((v2_tops_2(X1,X0) | ? [X2] : (~v4_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v4_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 2.51/0.69    inference(rectify,[],[f27])).
% 2.51/0.69  fof(f27,plain,(
% 2.51/0.69    ! [X0] : (! [X1] : (((v2_tops_2(X1,X0) | ? [X2] : (~v4_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v4_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 2.51/0.69    inference(nnf_transformation,[],[f18])).
% 2.51/0.69  fof(f18,plain,(
% 2.51/0.69    ! [X0] : (! [X1] : ((v2_tops_2(X1,X0) <=> ! [X2] : (v4_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 2.51/0.69    inference(flattening,[],[f17])).
% 2.51/0.69  fof(f17,plain,(
% 2.51/0.69    ! [X0] : (! [X1] : ((v2_tops_2(X1,X0) <=> ! [X2] : ((v4_pre_topc(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 2.51/0.69    inference(ennf_transformation,[],[f9])).
% 2.51/0.69  fof(f9,axiom,(
% 2.51/0.69    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,X1) => v4_pre_topc(X2,X0))))))),
% 2.51/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_2)).
% 2.51/0.69  fof(f2672,plain,(
% 2.51/0.69    v4_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0) | ~spl5_25),
% 2.51/0.69    inference(avatar_component_clause,[],[f2671])).
% 2.51/0.69  fof(f2671,plain,(
% 2.51/0.69    spl5_25 <=> v4_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0)),
% 2.51/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 2.51/0.69  fof(f3395,plain,(
% 2.51/0.69    spl5_26 | spl5_27),
% 2.51/0.69    inference(avatar_contradiction_clause,[],[f3394])).
% 2.51/0.69  fof(f3394,plain,(
% 2.51/0.69    $false | (spl5_26 | spl5_27)),
% 2.51/0.69    inference(subsumption_resolution,[],[f3393,f2680])).
% 2.51/0.69  fof(f2680,plain,(
% 2.51/0.69    ~r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2) | spl5_27),
% 2.51/0.69    inference(avatar_component_clause,[],[f2679])).
% 2.51/0.69  fof(f2679,plain,(
% 2.51/0.69    spl5_27 <=> r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2)),
% 2.51/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 2.51/0.69  fof(f3393,plain,(
% 2.51/0.69    r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2) | spl5_26),
% 2.51/0.69    inference(subsumption_resolution,[],[f3392,f2675])).
% 2.51/0.69  fof(f2675,plain,(
% 2.51/0.69    ~r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1) | spl5_26),
% 2.51/0.69    inference(avatar_component_clause,[],[f2674])).
% 2.51/0.69  fof(f2674,plain,(
% 2.51/0.69    spl5_26 <=> r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1)),
% 2.51/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 2.51/0.69  fof(f3392,plain,(
% 2.51/0.69    r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1) | r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2)),
% 2.51/0.69    inference(resolution,[],[f2685,f64])).
% 2.51/0.69  fof(f64,plain,(
% 2.51/0.69    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_xboole_0(X0,X1)) | r2_hidden(X4,X0) | r2_hidden(X4,X1)) )),
% 2.51/0.69    inference(equality_resolution,[],[f56])).
% 2.51/0.69  fof(f56,plain,(
% 2.51/0.69    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 2.51/0.69    inference(cnf_transformation,[],[f36])).
% 2.51/0.69  fof(f2685,plain,(
% 2.51/0.69    r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2))),
% 2.51/0.69    inference(subsumption_resolution,[],[f2684,f37])).
% 2.51/0.69  fof(f2684,plain,(
% 2.51/0.69    ~l1_pre_topc(sK0) | r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2))),
% 2.51/0.69    inference(subsumption_resolution,[],[f2668,f99])).
% 2.51/0.69  fof(f2668,plain,(
% 2.51/0.69    v2_tops_2(k2_xboole_0(sK1,sK2),sK0) | ~l1_pre_topc(sK0) | r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2))),
% 2.51/0.69    inference(resolution,[],[f2606,f91])).
% 2.51/0.69  fof(f91,plain,(
% 2.51/0.69    ( ! [X0,X1] : (~r1_tarski(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tops_2(X1,X0) | ~l1_pre_topc(X0) | r2_hidden(sK3(X0,X1),X1)) )),
% 2.51/0.69    inference(resolution,[],[f47,f52])).
% 2.51/0.69  fof(f47,plain,(
% 2.51/0.69    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(sK3(X0,X1),X1) | v2_tops_2(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.51/0.69    inference(cnf_transformation,[],[f30])).
% 2.51/0.69  fof(f2681,plain,(
% 2.51/0.69    spl5_25 | ~spl5_27),
% 2.51/0.69    inference(avatar_split_clause,[],[f2677,f2679,f2671])).
% 2.51/0.69  fof(f2677,plain,(
% 2.51/0.69    ~r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2) | v4_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0)),
% 2.51/0.69    inference(subsumption_resolution,[],[f2657,f99])).
% 2.51/0.69  fof(f2657,plain,(
% 2.51/0.69    v2_tops_2(k2_xboole_0(sK1,sK2),sK0) | ~r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2) | v4_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0)),
% 2.51/0.69    inference(resolution,[],[f2606,f356])).
% 2.51/0.69  fof(f356,plain,(
% 2.51/0.69    ( ! [X8] : (~r1_tarski(X8,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_2(X8,sK0) | ~r2_hidden(sK3(sK0,X8),sK2) | v4_pre_topc(sK3(sK0,X8),sK0)) )),
% 2.51/0.69    inference(resolution,[],[f150,f52])).
% 2.51/0.69  fof(f150,plain,(
% 2.51/0.69    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v4_pre_topc(sK3(sK0,X0),sK0) | v2_tops_2(X0,sK0) | ~r2_hidden(sK3(sK0,X0),sK2)) )),
% 2.51/0.69    inference(subsumption_resolution,[],[f148,f37])).
% 2.51/0.69  fof(f148,plain,(
% 2.51/0.69    ( ! [X0] : (~r2_hidden(sK3(sK0,X0),sK2) | v4_pre_topc(sK3(sK0,X0),sK0) | v2_tops_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0)) )),
% 2.51/0.69    inference(resolution,[],[f125,f46])).
% 2.51/0.69  fof(f46,plain,(
% 2.51/0.69    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v2_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.51/0.69    inference(cnf_transformation,[],[f30])).
% 2.51/0.69  fof(f125,plain,(
% 2.51/0.69    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X1,sK2) | v4_pre_topc(X1,sK0)) )),
% 2.51/0.69    inference(subsumption_resolution,[],[f124,f37])).
% 2.51/0.69  fof(f124,plain,(
% 2.51/0.69    ( ! [X1] : (~r2_hidden(X1,sK2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X1,sK0) | ~l1_pre_topc(sK0)) )),
% 2.51/0.69    inference(subsumption_resolution,[],[f119,f41])).
% 2.51/0.69  fof(f41,plain,(
% 2.51/0.69    v2_tops_2(sK2,sK0)),
% 2.51/0.69    inference(cnf_transformation,[],[f26])).
% 2.51/0.69  fof(f119,plain,(
% 2.51/0.69    ( ! [X1] : (~r2_hidden(X1,sK2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tops_2(sK2,sK0) | v4_pre_topc(X1,sK0) | ~l1_pre_topc(sK0)) )),
% 2.51/0.69    inference(resolution,[],[f45,f39])).
% 2.51/0.69  fof(f45,plain,(
% 2.51/0.69    ( ! [X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tops_2(X1,X0) | v4_pre_topc(X3,X0) | ~l1_pre_topc(X0)) )),
% 2.51/0.69    inference(cnf_transformation,[],[f30])).
% 2.51/0.69  fof(f2676,plain,(
% 2.51/0.69    spl5_25 | ~spl5_26),
% 2.51/0.69    inference(avatar_split_clause,[],[f2669,f2674,f2671])).
% 2.51/0.69  fof(f2669,plain,(
% 2.51/0.69    ~r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1) | v4_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0)),
% 2.51/0.69    inference(subsumption_resolution,[],[f2655,f99])).
% 2.51/0.69  fof(f2655,plain,(
% 2.51/0.69    v2_tops_2(k2_xboole_0(sK1,sK2),sK0) | ~r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1) | v4_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0)),
% 2.51/0.69    inference(resolution,[],[f2606,f345])).
% 2.51/0.69  fof(f345,plain,(
% 2.51/0.69    ( ! [X8] : (~r1_tarski(X8,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_2(X8,sK0) | ~r2_hidden(sK3(sK0,X8),sK1) | v4_pre_topc(sK3(sK0,X8),sK0)) )),
% 2.51/0.69    inference(resolution,[],[f147,f52])).
% 2.51/0.69  fof(f147,plain,(
% 2.51/0.69    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v4_pre_topc(sK3(sK0,X0),sK0) | v2_tops_2(X0,sK0) | ~r2_hidden(sK3(sK0,X0),sK1)) )),
% 2.51/0.69    inference(subsumption_resolution,[],[f145,f37])).
% 2.51/0.69  fof(f145,plain,(
% 2.51/0.69    ( ! [X0] : (~r2_hidden(sK3(sK0,X0),sK1) | v4_pre_topc(sK3(sK0,X0),sK0) | v2_tops_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0)) )),
% 2.51/0.69    inference(resolution,[],[f123,f46])).
% 2.51/0.69  fof(f123,plain,(
% 2.51/0.69    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,sK1) | v4_pre_topc(X0,sK0)) )),
% 2.51/0.69    inference(subsumption_resolution,[],[f122,f37])).
% 2.51/0.69  fof(f122,plain,(
% 2.51/0.69    ( ! [X0] : (~r2_hidden(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X0,sK0) | ~l1_pre_topc(sK0)) )),
% 2.51/0.69    inference(subsumption_resolution,[],[f118,f40])).
% 2.51/0.69  fof(f40,plain,(
% 2.51/0.69    v2_tops_2(sK1,sK0)),
% 2.51/0.69    inference(cnf_transformation,[],[f26])).
% 2.51/0.69  fof(f118,plain,(
% 2.51/0.69    ( ! [X0] : (~r2_hidden(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tops_2(sK1,sK0) | v4_pre_topc(X0,sK0) | ~l1_pre_topc(sK0)) )),
% 2.51/0.69    inference(resolution,[],[f45,f38])).
% 2.51/0.69  % SZS output end Proof for theBenchmark
% 2.51/0.69  % (20923)------------------------------
% 2.51/0.69  % (20923)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.51/0.69  % (20923)Termination reason: Refutation
% 2.51/0.69  
% 2.51/0.69  % (20923)Memory used [KB]: 13944
% 2.51/0.69  % (20923)Time elapsed: 0.283 s
% 2.51/0.69  % (20923)------------------------------
% 2.51/0.69  % (20923)------------------------------
% 2.51/0.70  % (20917)Success in time 0.338 s
%------------------------------------------------------------------------------
