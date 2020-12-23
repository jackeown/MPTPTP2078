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
% DateTime   : Thu Dec  3 13:11:06 EST 2020

% Result     : Theorem 6.79s
% Output     : Refutation 6.79s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 451 expanded)
%              Number of leaves         :   28 ( 158 expanded)
%              Depth                    :   16
%              Number of atoms          :  401 (1275 expanded)
%              Number of equality atoms :   40 ( 160 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9690,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1275,f2201,f2583,f2819,f4765,f5110,f5224,f9679])).

fof(f9679,plain,
    ( ~ spl4_28
    | spl4_55 ),
    inference(avatar_contradiction_clause,[],[f9678])).

fof(f9678,plain,
    ( $false
    | ~ spl4_28
    | spl4_55 ),
    inference(subsumption_resolution,[],[f9677,f94])).

fof(f94,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f9677,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ spl4_28
    | spl4_55 ),
    inference(subsumption_resolution,[],[f9568,f58])).

fof(f58,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f9568,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | ~ r1_tarski(sK1,sK1)
    | ~ spl4_28
    | spl4_55 ),
    inference(superposition,[],[f3970,f8549])).

fof(f8549,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,X1) ),
    inference(forward_demodulation,[],[f8522,f6804])).

fof(f6804,plain,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(subsumption_resolution,[],[f6792,f63])).

fof(f63,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f6792,plain,(
    ! [X1] :
      ( k4_xboole_0(X1,k1_xboole_0) = X1
      | ~ r1_tarski(k4_xboole_0(X1,k1_xboole_0),X1) ) ),
    inference(resolution,[],[f2065,f648])).

fof(f648,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(forward_demodulation,[],[f608,f89])).

fof(f89,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f68,f85])).

fof(f85,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f65,f67])).

fof(f67,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f65,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f68,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f608,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k1_enumset1(X1,X1,X0)),X0) ),
    inference(superposition,[],[f63,f162])).

fof(f162,plain,(
    ! [X2,X3] : k1_setfam_1(k1_enumset1(X3,X3,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f89,f88])).

fof(f88,plain,(
    ! [X0,X1] : k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_setfam_1(k1_enumset1(X1,X1,X0)) ),
    inference(definition_unfolding,[],[f64,f85,f85])).

fof(f64,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f2065,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X1,X0),k1_xboole_0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f270,f87])).

fof(f87,plain,(
    ! [X0] : k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f59,f86])).

fof(f86,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f66,f67])).

fof(f66,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f59,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f270,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(k3_tarski(k1_enumset1(X4,X4,X5)),X3)
      | k3_tarski(k1_enumset1(X4,X4,X5)) = X3
      | ~ r1_tarski(k4_xboole_0(X3,X4),X5) ) ),
    inference(resolution,[],[f91,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2)))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f80,f86])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f8522,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) ),
    inference(resolution,[],[f654,f58])).

fof(f654,plain,(
    ! [X10,X9] :
      ( ~ r1_tarski(X9,k4_xboole_0(X10,k4_xboole_0(X10,X9)))
      | k4_xboole_0(X10,k4_xboole_0(X10,X9)) = X9 ) ),
    inference(forward_demodulation,[],[f653,f89])).

fof(f653,plain,(
    ! [X10,X9] :
      ( ~ r1_tarski(X9,k4_xboole_0(X10,k4_xboole_0(X10,X9)))
      | k1_setfam_1(k1_enumset1(X10,X10,X9)) = X9 ) ),
    inference(forward_demodulation,[],[f612,f89])).

fof(f612,plain,(
    ! [X10,X9] :
      ( ~ r1_tarski(X9,k1_setfam_1(k1_enumset1(X10,X10,X9)))
      | k1_setfam_1(k1_enumset1(X10,X10,X9)) = X9 ) ),
    inference(superposition,[],[f114,f162])).

fof(f114,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,k4_xboole_0(X2,X3))
      | k4_xboole_0(X2,X3) = X2 ) ),
    inference(resolution,[],[f72,f63])).

fof(f3970,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k4_xboole_0(X0,sK1),sK2)
        | ~ r1_tarski(sK1,X0) )
    | ~ spl4_28
    | spl4_55 ),
    inference(subsumption_resolution,[],[f3969,f55])).

fof(f55,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f45,f44,f43])).

fof(f43,plain,
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

fof(f44,plain,
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

fof(f45,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X2)))
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tops_1)).

fof(f3969,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | ~ r1_tarski(k4_xboole_0(X0,sK1),sK2)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_28
    | spl4_55 ),
    inference(subsumption_resolution,[],[f3953,f56])).

fof(f56,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f3953,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | ~ r1_tarski(k4_xboole_0(X0,sK1),sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_28
    | spl4_55 ),
    inference(resolution,[],[f2918,f393])).

fof(f393,plain,(
    ! [X17,X15,X18,X16] :
      ( r1_tarski(X18,k4_subset_1(X17,X15,X16))
      | ~ r1_tarski(k4_xboole_0(X18,X15),X16)
      | ~ m1_subset_1(X16,k1_zfmisc_1(X17))
      | ~ m1_subset_1(X15,k1_zfmisc_1(X17)) ) ),
    inference(superposition,[],[f91,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k3_tarski(k1_enumset1(X1,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f84,f86])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f2918,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
        | ~ r1_tarski(sK1,X0) )
    | ~ spl4_28
    | spl4_55 ),
    inference(resolution,[],[f2912,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f2912,plain,
    ( ~ r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ spl4_28
    | spl4_55 ),
    inference(subsumption_resolution,[],[f2911,f54])).

fof(f54,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f2911,plain,
    ( ~ r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_28
    | spl4_55 ),
    inference(subsumption_resolution,[],[f2910,f55])).

fof(f2910,plain,
    ( ~ r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_28
    | spl4_55 ),
    inference(subsumption_resolution,[],[f2906,f1217])).

fof(f1217,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f1216])).

fof(f1216,plain,
    ( spl4_28
  <=> m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f2906,plain,
    ( ~ r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl4_55 ),
    inference(resolution,[],[f2401,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

fof(f2401,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | spl4_55 ),
    inference(avatar_component_clause,[],[f2399])).

fof(f2399,plain,
    ( spl4_55
  <=> r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).

fof(f5224,plain,
    ( spl4_57
    | ~ spl4_39
    | ~ spl4_54 ),
    inference(avatar_split_clause,[],[f5223,f2395,f1793,f2408])).

fof(f2408,plain,
    ( spl4_57
  <=> ! [X1] :
        ( ~ r1_tarski(k1_tops_1(sK0,sK2),X1)
        | ~ r1_tarski(X1,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
        | ~ r1_tarski(k1_tops_1(sK0,sK1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).

fof(f1793,plain,
    ( spl4_39
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f2395,plain,
    ( spl4_54
  <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f5223,plain,
    ( ! [X3] :
        ( ~ r1_tarski(X3,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
        | ~ r1_tarski(k1_tops_1(sK0,sK2),X3)
        | ~ r1_tarski(k1_tops_1(sK0,sK1),X3) )
    | ~ spl4_39
    | ~ spl4_54 ),
    inference(subsumption_resolution,[],[f5222,f1794])).

fof(f1794,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f1793])).

fof(f5222,plain,
    ( ! [X3] :
        ( ~ r1_tarski(X3,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
        | ~ r1_tarski(k1_tops_1(sK0,sK2),X3)
        | ~ r1_tarski(k1_tops_1(sK0,sK1),X3)
        | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_54 ),
    inference(subsumption_resolution,[],[f5216,f2396])).

fof(f2396,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_54 ),
    inference(avatar_component_clause,[],[f2395])).

fof(f5216,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
      | ~ r1_tarski(k1_tops_1(sK0,sK2),X3)
      | ~ r1_tarski(k1_tops_1(sK0,sK1),X3)
      | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f141,f392])).

fof(f392,plain,(
    ! [X14,X12,X13,X11] :
      ( r1_tarski(k4_subset_1(X13,X11,X12),X14)
      | ~ r1_tarski(X12,X14)
      | ~ r1_tarski(X11,X14)
      | ~ m1_subset_1(X12,k1_zfmisc_1(X13))
      | ~ m1_subset_1(X11,k1_zfmisc_1(X13)) ) ),
    inference(superposition,[],[f92,f93])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f82,f86])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f141,plain,(
    ! [X8] :
      ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),X8)
      | ~ r1_tarski(X8,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ) ),
    inference(resolution,[],[f81,f57])).

fof(f57,plain,(
    ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f46])).

fof(f5110,plain,
    ( ~ spl4_28
    | ~ spl4_45
    | spl4_56 ),
    inference(avatar_contradiction_clause,[],[f5109])).

fof(f5109,plain,
    ( $false
    | ~ spl4_28
    | ~ spl4_45
    | spl4_56 ),
    inference(subsumption_resolution,[],[f5108,f54])).

fof(f5108,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_28
    | ~ spl4_45
    | spl4_56 ),
    inference(subsumption_resolution,[],[f5107,f56])).

fof(f5107,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_28
    | ~ spl4_45
    | spl4_56 ),
    inference(subsumption_resolution,[],[f5106,f1217])).

fof(f5106,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_45
    | spl4_56 ),
    inference(subsumption_resolution,[],[f5101,f2025])).

fof(f2025,plain,
    ( r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ spl4_45 ),
    inference(avatar_component_clause,[],[f2024])).

fof(f2024,plain,
    ( spl4_45
  <=> r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f5101,plain,
    ( ~ r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl4_56 ),
    inference(resolution,[],[f2405,f61])).

fof(f2405,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | spl4_56 ),
    inference(avatar_component_clause,[],[f2403])).

fof(f2403,plain,
    ( spl4_56
  <=> r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f4765,plain,
    ( ~ spl4_55
    | ~ spl4_56
    | ~ spl4_57 ),
    inference(avatar_split_clause,[],[f3348,f2408,f2403,f2399])).

fof(f3348,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ spl4_57 ),
    inference(resolution,[],[f2409,f94])).

fof(f2409,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
        | ~ r1_tarski(k1_tops_1(sK0,sK2),X1)
        | ~ r1_tarski(k1_tops_1(sK0,sK1),X1) )
    | ~ spl4_57 ),
    inference(avatar_component_clause,[],[f2408])).

fof(f2819,plain,(
    spl4_54 ),
    inference(avatar_contradiction_clause,[],[f2818])).

fof(f2818,plain,
    ( $false
    | spl4_54 ),
    inference(subsumption_resolution,[],[f2811,f101])).

fof(f101,plain,(
    r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f76,f56])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f2811,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | spl4_54 ),
    inference(resolution,[],[f2603,f200])).

fof(f200,plain,(
    r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(subsumption_resolution,[],[f197,f54])).

fof(f197,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f60,f56])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f2603,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_tops_1(sK0,sK2),X0)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | spl4_54 ),
    inference(resolution,[],[f2602,f81])).

fof(f2602,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | spl4_54 ),
    inference(resolution,[],[f2397,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f2397,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_54 ),
    inference(avatar_component_clause,[],[f2395])).

fof(f2583,plain,(
    spl4_39 ),
    inference(avatar_contradiction_clause,[],[f2582])).

fof(f2582,plain,
    ( $false
    | spl4_39 ),
    inference(subsumption_resolution,[],[f2575,f100])).

fof(f100,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f76,f55])).

fof(f2575,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | spl4_39 ),
    inference(resolution,[],[f2415,f199])).

fof(f199,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f196,f54])).

fof(f196,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f60,f55])).

fof(f2415,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_tops_1(sK0,sK1),X0)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | spl4_39 ),
    inference(resolution,[],[f2414,f81])).

fof(f2414,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | spl4_39 ),
    inference(resolution,[],[f1795,f77])).

fof(f1795,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_39 ),
    inference(avatar_component_clause,[],[f1793])).

fof(f2201,plain,(
    spl4_45 ),
    inference(avatar_contradiction_clause,[],[f2200])).

fof(f2200,plain,
    ( $false
    | spl4_45 ),
    inference(subsumption_resolution,[],[f2199,f55])).

fof(f2199,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_45 ),
    inference(subsumption_resolution,[],[f2198,f56])).

fof(f2198,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_45 ),
    inference(subsumption_resolution,[],[f2159,f63])).

fof(f2159,plain,
    ( ~ r1_tarski(k4_xboole_0(sK2,sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_45 ),
    inference(resolution,[],[f393,f2026])).

fof(f2026,plain,
    ( ~ r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | spl4_45 ),
    inference(avatar_component_clause,[],[f2024])).

fof(f1275,plain,(
    spl4_28 ),
    inference(avatar_contradiction_clause,[],[f1274])).

fof(f1274,plain,
    ( $false
    | spl4_28 ),
    inference(subsumption_resolution,[],[f1273,f55])).

fof(f1273,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_28 ),
    inference(subsumption_resolution,[],[f1272,f56])).

fof(f1272,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_28 ),
    inference(resolution,[],[f1218,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f1218,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_28 ),
    inference(avatar_component_clause,[],[f1216])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:51:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.52  % (20094)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (20087)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (20098)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.53  % (20111)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (20086)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.54  % (20084)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (20095)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.54  % (20090)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.55  % (20085)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.55  % (20106)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.55  % (20093)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.55  % (20091)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.55  % (20102)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.55  % (20092)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.56  % (20083)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.56  % (20107)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.56  % (20110)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.56  % (20109)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.57  % (20104)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.57  % (20097)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.57  % (20101)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.57  % (20096)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.57  % (20105)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.64/0.58  % (20108)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.64/0.58  % (20082)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.64/0.58  % (20103)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.64/0.58  % (20088)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.64/0.58  % (20100)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.80/0.60  % (20099)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.80/0.61  % (20089)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 3.17/0.84  % (20087)Time limit reached!
% 3.17/0.84  % (20087)------------------------------
% 3.17/0.84  % (20087)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.17/0.84  % (20087)Termination reason: Time limit
% 3.17/0.84  % (20087)Termination phase: Saturation
% 3.17/0.84  
% 3.17/0.84  % (20087)Memory used [KB]: 9083
% 3.17/0.84  % (20087)Time elapsed: 0.400 s
% 3.17/0.84  % (20087)------------------------------
% 3.17/0.84  % (20087)------------------------------
% 4.09/0.92  % (20082)Time limit reached!
% 4.09/0.92  % (20082)------------------------------
% 4.09/0.92  % (20082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.39/0.93  % (20083)Time limit reached!
% 4.39/0.93  % (20083)------------------------------
% 4.39/0.93  % (20083)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.39/0.93  % (20083)Termination reason: Time limit
% 4.39/0.93  
% 4.39/0.93  % (20083)Memory used [KB]: 7931
% 4.39/0.93  % (20083)Time elapsed: 0.511 s
% 4.39/0.93  % (20083)------------------------------
% 4.39/0.93  % (20083)------------------------------
% 4.39/0.93  % (20094)Time limit reached!
% 4.39/0.93  % (20094)------------------------------
% 4.39/0.93  % (20094)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.39/0.93  % (20094)Termination reason: Time limit
% 4.39/0.93  
% 4.39/0.93  % (20094)Memory used [KB]: 9594
% 4.39/0.93  % (20094)Time elapsed: 0.506 s
% 4.39/0.93  % (20094)------------------------------
% 4.39/0.93  % (20094)------------------------------
% 4.46/0.93  % (20092)Time limit reached!
% 4.46/0.93  % (20092)------------------------------
% 4.46/0.93  % (20092)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.46/0.93  % (20092)Termination reason: Time limit
% 4.46/0.93  
% 4.46/0.93  % (20092)Memory used [KB]: 16758
% 4.46/0.93  % (20092)Time elapsed: 0.516 s
% 4.46/0.93  % (20092)------------------------------
% 4.46/0.93  % (20092)------------------------------
% 4.46/0.93  % (20082)Termination reason: Time limit
% 4.46/0.93  % (20082)Termination phase: Saturation
% 4.46/0.93  
% 4.46/0.93  % (20082)Memory used [KB]: 3582
% 4.46/0.93  % (20082)Time elapsed: 0.500 s
% 4.46/0.93  % (20082)------------------------------
% 4.46/0.93  % (20082)------------------------------
% 4.46/0.94  % (20099)Time limit reached!
% 4.46/0.94  % (20099)------------------------------
% 4.46/0.94  % (20099)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.46/0.94  % (20099)Termination reason: Time limit
% 4.46/0.94  % (20099)Termination phase: Saturation
% 4.46/0.94  
% 4.46/0.94  % (20099)Memory used [KB]: 12537
% 4.46/0.94  % (20099)Time elapsed: 0.500 s
% 4.46/0.94  % (20099)------------------------------
% 4.46/0.94  % (20099)------------------------------
% 4.46/0.98  % (20144)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 4.92/1.01  % (20147)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 4.92/1.01  % (20110)Time limit reached!
% 4.92/1.01  % (20110)------------------------------
% 4.92/1.01  % (20110)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.92/1.01  % (20110)Termination reason: Time limit
% 4.92/1.01  
% 4.92/1.01  % (20110)Memory used [KB]: 8315
% 4.92/1.01  % (20110)Time elapsed: 0.609 s
% 4.92/1.01  % (20110)------------------------------
% 4.92/1.01  % (20110)------------------------------
% 4.92/1.02  % (20089)Time limit reached!
% 4.92/1.02  % (20089)------------------------------
% 4.92/1.02  % (20089)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.92/1.02  % (20089)Termination reason: Time limit
% 4.92/1.02  % (20089)Termination phase: Saturation
% 4.92/1.02  
% 4.92/1.02  % (20089)Memory used [KB]: 11257
% 4.92/1.02  % (20089)Time elapsed: 0.600 s
% 4.92/1.02  % (20089)------------------------------
% 4.92/1.02  % (20089)------------------------------
% 4.92/1.03  % (20098)Time limit reached!
% 4.92/1.03  % (20098)------------------------------
% 4.92/1.03  % (20098)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.92/1.03  % (20098)Termination reason: Time limit
% 4.92/1.03  
% 4.92/1.03  % (20098)Memory used [KB]: 17654
% 4.92/1.03  % (20098)Time elapsed: 0.617 s
% 4.92/1.03  % (20098)------------------------------
% 4.92/1.03  % (20098)------------------------------
% 4.92/1.05  % (20149)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 4.92/1.07  % (20145)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 4.92/1.07  % (20146)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 4.92/1.07  % (20148)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 5.65/1.12  % (20183)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 5.65/1.13  % (20186)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 5.65/1.16  % (20192)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 6.79/1.26  % (20103)Time limit reached!
% 6.79/1.26  % (20103)------------------------------
% 6.79/1.26  % (20103)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.79/1.26  % (20103)Termination reason: Time limit
% 6.79/1.26  % (20103)Termination phase: Saturation
% 6.79/1.26  
% 6.79/1.26  % (20103)Memory used [KB]: 3965
% 6.79/1.26  % (20103)Time elapsed: 0.800 s
% 6.79/1.26  % (20103)------------------------------
% 6.79/1.26  % (20103)------------------------------
% 6.79/1.28  % (20109)Refutation found. Thanks to Tanya!
% 6.79/1.28  % SZS status Theorem for theBenchmark
% 6.79/1.28  % SZS output start Proof for theBenchmark
% 6.79/1.28  fof(f9690,plain,(
% 6.79/1.28    $false),
% 6.79/1.28    inference(avatar_sat_refutation,[],[f1275,f2201,f2583,f2819,f4765,f5110,f5224,f9679])).
% 6.79/1.28  fof(f9679,plain,(
% 6.79/1.28    ~spl4_28 | spl4_55),
% 6.79/1.28    inference(avatar_contradiction_clause,[],[f9678])).
% 6.79/1.28  fof(f9678,plain,(
% 6.79/1.28    $false | (~spl4_28 | spl4_55)),
% 6.79/1.28    inference(subsumption_resolution,[],[f9677,f94])).
% 6.79/1.28  fof(f94,plain,(
% 6.79/1.28    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 6.79/1.28    inference(equality_resolution,[],[f71])).
% 6.79/1.28  fof(f71,plain,(
% 6.79/1.28    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 6.79/1.28    inference(cnf_transformation,[],[f48])).
% 6.79/1.28  fof(f48,plain,(
% 6.79/1.28    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.79/1.28    inference(flattening,[],[f47])).
% 6.79/1.28  fof(f47,plain,(
% 6.79/1.28    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.79/1.28    inference(nnf_transformation,[],[f3])).
% 6.79/1.28  fof(f3,axiom,(
% 6.79/1.28    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 6.79/1.28    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 6.79/1.28  fof(f9677,plain,(
% 6.79/1.28    ~r1_tarski(sK1,sK1) | (~spl4_28 | spl4_55)),
% 6.79/1.28    inference(subsumption_resolution,[],[f9568,f58])).
% 6.79/1.28  fof(f58,plain,(
% 6.79/1.28    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 6.79/1.28    inference(cnf_transformation,[],[f7])).
% 6.79/1.28  fof(f7,axiom,(
% 6.79/1.28    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 6.79/1.28    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 6.79/1.28  fof(f9568,plain,(
% 6.79/1.28    ~r1_tarski(k1_xboole_0,sK2) | ~r1_tarski(sK1,sK1) | (~spl4_28 | spl4_55)),
% 6.79/1.28    inference(superposition,[],[f3970,f8549])).
% 6.79/1.28  fof(f8549,plain,(
% 6.79/1.28    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,X1)) )),
% 6.79/1.28    inference(forward_demodulation,[],[f8522,f6804])).
% 6.79/1.28  fof(f6804,plain,(
% 6.79/1.28    ( ! [X1] : (k4_xboole_0(X1,k1_xboole_0) = X1) )),
% 6.79/1.28    inference(subsumption_resolution,[],[f6792,f63])).
% 6.79/1.28  fof(f63,plain,(
% 6.79/1.28    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 6.79/1.28    inference(cnf_transformation,[],[f8])).
% 6.79/1.28  fof(f8,axiom,(
% 6.79/1.28    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 6.79/1.28    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 6.79/1.28  fof(f6792,plain,(
% 6.79/1.28    ( ! [X1] : (k4_xboole_0(X1,k1_xboole_0) = X1 | ~r1_tarski(k4_xboole_0(X1,k1_xboole_0),X1)) )),
% 6.79/1.28    inference(resolution,[],[f2065,f648])).
% 6.79/1.28  fof(f648,plain,(
% 6.79/1.28    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) )),
% 6.79/1.28    inference(forward_demodulation,[],[f608,f89])).
% 6.79/1.28  fof(f89,plain,(
% 6.79/1.28    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 6.79/1.28    inference(definition_unfolding,[],[f68,f85])).
% 6.79/1.28  fof(f85,plain,(
% 6.79/1.28    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 6.79/1.28    inference(definition_unfolding,[],[f65,f67])).
% 6.79/1.28  fof(f67,plain,(
% 6.79/1.28    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 6.79/1.28    inference(cnf_transformation,[],[f14])).
% 6.79/1.28  fof(f14,axiom,(
% 6.79/1.28    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 6.79/1.28    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 6.79/1.28  fof(f65,plain,(
% 6.79/1.28    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 6.79/1.28    inference(cnf_transformation,[],[f18])).
% 6.79/1.28  fof(f18,axiom,(
% 6.79/1.28    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 6.79/1.28    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 6.79/1.28  fof(f68,plain,(
% 6.79/1.28    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 6.79/1.28    inference(cnf_transformation,[],[f12])).
% 6.79/1.28  fof(f12,axiom,(
% 6.79/1.28    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 6.79/1.28    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 6.79/1.28  fof(f608,plain,(
% 6.79/1.28    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k1_enumset1(X1,X1,X0)),X0)) )),
% 6.79/1.28    inference(superposition,[],[f63,f162])).
% 6.79/1.28  fof(f162,plain,(
% 6.79/1.28    ( ! [X2,X3] : (k1_setfam_1(k1_enumset1(X3,X3,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X3))) )),
% 6.79/1.28    inference(superposition,[],[f89,f88])).
% 6.79/1.28  fof(f88,plain,(
% 6.79/1.28    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_setfam_1(k1_enumset1(X1,X1,X0))) )),
% 6.79/1.28    inference(definition_unfolding,[],[f64,f85,f85])).
% 6.79/1.28  fof(f64,plain,(
% 6.79/1.28    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 6.79/1.28    inference(cnf_transformation,[],[f1])).
% 6.79/1.28  fof(f1,axiom,(
% 6.79/1.28    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 6.79/1.28    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 6.79/1.28  fof(f2065,plain,(
% 6.79/1.28    ( ! [X0,X1] : (~r1_tarski(k4_xboole_0(X1,X0),k1_xboole_0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 6.79/1.28    inference(superposition,[],[f270,f87])).
% 6.79/1.28  fof(f87,plain,(
% 6.79/1.28    ( ! [X0] : (k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0) )),
% 6.79/1.28    inference(definition_unfolding,[],[f59,f86])).
% 6.79/1.28  fof(f86,plain,(
% 6.79/1.28    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 6.79/1.28    inference(definition_unfolding,[],[f66,f67])).
% 6.79/1.28  fof(f66,plain,(
% 6.79/1.28    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 6.79/1.28    inference(cnf_transformation,[],[f15])).
% 6.79/1.28  fof(f15,axiom,(
% 6.79/1.28    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 6.79/1.28    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 6.79/1.28  fof(f59,plain,(
% 6.79/1.28    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 6.79/1.28    inference(cnf_transformation,[],[f5])).
% 6.79/1.28  fof(f5,axiom,(
% 6.79/1.28    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 6.79/1.28    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 6.79/1.28  fof(f270,plain,(
% 6.79/1.28    ( ! [X4,X5,X3] : (~r1_tarski(k3_tarski(k1_enumset1(X4,X4,X5)),X3) | k3_tarski(k1_enumset1(X4,X4,X5)) = X3 | ~r1_tarski(k4_xboole_0(X3,X4),X5)) )),
% 6.79/1.28    inference(resolution,[],[f91,f72])).
% 6.79/1.28  fof(f72,plain,(
% 6.79/1.28    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 6.79/1.28    inference(cnf_transformation,[],[f48])).
% 6.79/1.28  fof(f91,plain,(
% 6.79/1.28    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 6.79/1.28    inference(definition_unfolding,[],[f80,f86])).
% 6.79/1.28  fof(f80,plain,(
% 6.79/1.28    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 6.79/1.28    inference(cnf_transformation,[],[f34])).
% 6.79/1.28  fof(f34,plain,(
% 6.79/1.28    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 6.79/1.28    inference(ennf_transformation,[],[f10])).
% 6.79/1.28  fof(f10,axiom,(
% 6.79/1.28    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 6.79/1.28    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 6.79/1.28  fof(f8522,plain,(
% 6.79/1.28    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) )),
% 6.79/1.28    inference(resolution,[],[f654,f58])).
% 6.79/1.28  fof(f654,plain,(
% 6.79/1.28    ( ! [X10,X9] : (~r1_tarski(X9,k4_xboole_0(X10,k4_xboole_0(X10,X9))) | k4_xboole_0(X10,k4_xboole_0(X10,X9)) = X9) )),
% 6.79/1.28    inference(forward_demodulation,[],[f653,f89])).
% 6.79/1.28  fof(f653,plain,(
% 6.79/1.28    ( ! [X10,X9] : (~r1_tarski(X9,k4_xboole_0(X10,k4_xboole_0(X10,X9))) | k1_setfam_1(k1_enumset1(X10,X10,X9)) = X9) )),
% 6.79/1.28    inference(forward_demodulation,[],[f612,f89])).
% 6.79/1.28  fof(f612,plain,(
% 6.79/1.28    ( ! [X10,X9] : (~r1_tarski(X9,k1_setfam_1(k1_enumset1(X10,X10,X9))) | k1_setfam_1(k1_enumset1(X10,X10,X9)) = X9) )),
% 6.79/1.28    inference(superposition,[],[f114,f162])).
% 6.79/1.28  fof(f114,plain,(
% 6.79/1.28    ( ! [X2,X3] : (~r1_tarski(X2,k4_xboole_0(X2,X3)) | k4_xboole_0(X2,X3) = X2) )),
% 6.79/1.28    inference(resolution,[],[f72,f63])).
% 6.79/1.28  fof(f3970,plain,(
% 6.79/1.28    ( ! [X0] : (~r1_tarski(k4_xboole_0(X0,sK1),sK2) | ~r1_tarski(sK1,X0)) ) | (~spl4_28 | spl4_55)),
% 6.79/1.28    inference(subsumption_resolution,[],[f3969,f55])).
% 6.79/1.28  fof(f55,plain,(
% 6.79/1.28    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 6.79/1.28    inference(cnf_transformation,[],[f46])).
% 6.79/1.28  fof(f46,plain,(
% 6.79/1.28    ((~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 6.79/1.28    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f45,f44,f43])).
% 6.79/1.28  fof(f43,plain,(
% 6.79/1.28    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 6.79/1.28    introduced(choice_axiom,[])).
% 6.79/1.28  fof(f44,plain,(
% 6.79/1.28    ? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 6.79/1.28    introduced(choice_axiom,[])).
% 6.79/1.28  fof(f45,plain,(
% 6.79/1.28    ? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 6.79/1.28    introduced(choice_axiom,[])).
% 6.79/1.28  fof(f25,plain,(
% 6.79/1.28    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 6.79/1.28    inference(ennf_transformation,[],[f24])).
% 6.79/1.28  fof(f24,negated_conjecture,(
% 6.79/1.28    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 6.79/1.28    inference(negated_conjecture,[],[f23])).
% 6.79/1.28  fof(f23,conjecture,(
% 6.79/1.28    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 6.79/1.28    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tops_1)).
% 6.79/1.28  fof(f3969,plain,(
% 6.79/1.28    ( ! [X0] : (~r1_tarski(sK1,X0) | ~r1_tarski(k4_xboole_0(X0,sK1),sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl4_28 | spl4_55)),
% 6.79/1.28    inference(subsumption_resolution,[],[f3953,f56])).
% 6.79/1.28  fof(f56,plain,(
% 6.79/1.28    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 6.79/1.28    inference(cnf_transformation,[],[f46])).
% 6.79/1.28  fof(f3953,plain,(
% 6.79/1.28    ( ! [X0] : (~r1_tarski(sK1,X0) | ~r1_tarski(k4_xboole_0(X0,sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl4_28 | spl4_55)),
% 6.79/1.28    inference(resolution,[],[f2918,f393])).
% 6.79/1.28  fof(f393,plain,(
% 6.79/1.28    ( ! [X17,X15,X18,X16] : (r1_tarski(X18,k4_subset_1(X17,X15,X16)) | ~r1_tarski(k4_xboole_0(X18,X15),X16) | ~m1_subset_1(X16,k1_zfmisc_1(X17)) | ~m1_subset_1(X15,k1_zfmisc_1(X17))) )),
% 6.79/1.28    inference(superposition,[],[f91,f93])).
% 6.79/1.28  fof(f93,plain,(
% 6.79/1.28    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k3_tarski(k1_enumset1(X1,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.79/1.28    inference(definition_unfolding,[],[f84,f86])).
% 6.79/1.28  fof(f84,plain,(
% 6.79/1.28    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.79/1.28    inference(cnf_transformation,[],[f42])).
% 6.79/1.28  fof(f42,plain,(
% 6.79/1.28    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.79/1.28    inference(flattening,[],[f41])).
% 6.79/1.28  fof(f41,plain,(
% 6.79/1.28    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 6.79/1.28    inference(ennf_transformation,[],[f17])).
% 6.79/1.28  fof(f17,axiom,(
% 6.79/1.28    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 6.79/1.28    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 6.79/1.28  fof(f2918,plain,(
% 6.79/1.28    ( ! [X0] : (~r1_tarski(X0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) | ~r1_tarski(sK1,X0)) ) | (~spl4_28 | spl4_55)),
% 6.79/1.28    inference(resolution,[],[f2912,f81])).
% 6.79/1.28  fof(f81,plain,(
% 6.79/1.28    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 6.79/1.28    inference(cnf_transformation,[],[f36])).
% 6.79/1.28  fof(f36,plain,(
% 6.79/1.28    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 6.79/1.28    inference(flattening,[],[f35])).
% 6.79/1.28  fof(f35,plain,(
% 6.79/1.28    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 6.79/1.28    inference(ennf_transformation,[],[f6])).
% 6.79/1.28  fof(f6,axiom,(
% 6.79/1.28    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 6.79/1.28    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 6.79/1.28  fof(f2912,plain,(
% 6.79/1.28    ~r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) | (~spl4_28 | spl4_55)),
% 6.79/1.28    inference(subsumption_resolution,[],[f2911,f54])).
% 6.79/1.28  fof(f54,plain,(
% 6.79/1.28    l1_pre_topc(sK0)),
% 6.79/1.28    inference(cnf_transformation,[],[f46])).
% 6.79/1.28  fof(f2911,plain,(
% 6.79/1.28    ~r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) | ~l1_pre_topc(sK0) | (~spl4_28 | spl4_55)),
% 6.79/1.28    inference(subsumption_resolution,[],[f2910,f55])).
% 6.79/1.28  fof(f2910,plain,(
% 6.79/1.28    ~r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl4_28 | spl4_55)),
% 6.79/1.28    inference(subsumption_resolution,[],[f2906,f1217])).
% 6.79/1.28  fof(f1217,plain,(
% 6.79/1.28    m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_28),
% 6.79/1.28    inference(avatar_component_clause,[],[f1216])).
% 6.79/1.28  fof(f1216,plain,(
% 6.79/1.28    spl4_28 <=> m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 6.79/1.28    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 6.79/1.28  fof(f2906,plain,(
% 6.79/1.28    ~r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) | ~m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl4_55),
% 6.79/1.28    inference(resolution,[],[f2401,f61])).
% 6.79/1.28  fof(f61,plain,(
% 6.79/1.28    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 6.79/1.28    inference(cnf_transformation,[],[f28])).
% 6.79/1.28  fof(f28,plain,(
% 6.79/1.28    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.79/1.28    inference(flattening,[],[f27])).
% 6.79/1.28  fof(f27,plain,(
% 6.79/1.28    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.79/1.28    inference(ennf_transformation,[],[f22])).
% 6.79/1.28  fof(f22,axiom,(
% 6.79/1.28    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 6.79/1.28    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).
% 6.79/1.28  fof(f2401,plain,(
% 6.79/1.28    ~r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | spl4_55),
% 6.79/1.28    inference(avatar_component_clause,[],[f2399])).
% 6.79/1.28  fof(f2399,plain,(
% 6.79/1.28    spl4_55 <=> r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 6.79/1.28    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).
% 6.79/1.28  fof(f5224,plain,(
% 6.79/1.28    spl4_57 | ~spl4_39 | ~spl4_54),
% 6.79/1.28    inference(avatar_split_clause,[],[f5223,f2395,f1793,f2408])).
% 6.79/1.28  fof(f2408,plain,(
% 6.79/1.28    spl4_57 <=> ! [X1] : (~r1_tarski(k1_tops_1(sK0,sK2),X1) | ~r1_tarski(X1,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | ~r1_tarski(k1_tops_1(sK0,sK1),X1))),
% 6.79/1.28    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).
% 6.79/1.28  fof(f1793,plain,(
% 6.79/1.28    spl4_39 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 6.79/1.28    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 6.79/1.28  fof(f2395,plain,(
% 6.79/1.28    spl4_54 <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 6.79/1.28    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).
% 6.79/1.28  fof(f5223,plain,(
% 6.79/1.28    ( ! [X3] : (~r1_tarski(X3,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | ~r1_tarski(k1_tops_1(sK0,sK2),X3) | ~r1_tarski(k1_tops_1(sK0,sK1),X3)) ) | (~spl4_39 | ~spl4_54)),
% 6.79/1.28    inference(subsumption_resolution,[],[f5222,f1794])).
% 6.79/1.28  fof(f1794,plain,(
% 6.79/1.28    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_39),
% 6.79/1.28    inference(avatar_component_clause,[],[f1793])).
% 6.79/1.28  fof(f5222,plain,(
% 6.79/1.28    ( ! [X3] : (~r1_tarski(X3,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | ~r1_tarski(k1_tops_1(sK0,sK2),X3) | ~r1_tarski(k1_tops_1(sK0,sK1),X3) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl4_54),
% 6.79/1.28    inference(subsumption_resolution,[],[f5216,f2396])).
% 6.79/1.28  fof(f2396,plain,(
% 6.79/1.28    m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_54),
% 6.79/1.28    inference(avatar_component_clause,[],[f2395])).
% 6.79/1.28  fof(f5216,plain,(
% 6.79/1.28    ( ! [X3] : (~r1_tarski(X3,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | ~r1_tarski(k1_tops_1(sK0,sK2),X3) | ~r1_tarski(k1_tops_1(sK0,sK1),X3) | ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 6.79/1.28    inference(resolution,[],[f141,f392])).
% 6.79/1.28  fof(f392,plain,(
% 6.79/1.28    ( ! [X14,X12,X13,X11] : (r1_tarski(k4_subset_1(X13,X11,X12),X14) | ~r1_tarski(X12,X14) | ~r1_tarski(X11,X14) | ~m1_subset_1(X12,k1_zfmisc_1(X13)) | ~m1_subset_1(X11,k1_zfmisc_1(X13))) )),
% 6.79/1.28    inference(superposition,[],[f92,f93])).
% 6.79/1.28  fof(f92,plain,(
% 6.79/1.28    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 6.79/1.28    inference(definition_unfolding,[],[f82,f86])).
% 6.79/1.28  fof(f82,plain,(
% 6.79/1.28    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 6.79/1.28    inference(cnf_transformation,[],[f38])).
% 6.79/1.28  fof(f38,plain,(
% 6.79/1.28    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 6.79/1.28    inference(flattening,[],[f37])).
% 6.79/1.28  fof(f37,plain,(
% 6.79/1.28    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 6.79/1.28    inference(ennf_transformation,[],[f13])).
% 6.79/1.28  fof(f13,axiom,(
% 6.79/1.28    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 6.79/1.28    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 6.79/1.28  fof(f141,plain,(
% 6.79/1.28    ( ! [X8] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),X8) | ~r1_tarski(X8,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))) )),
% 6.79/1.28    inference(resolution,[],[f81,f57])).
% 6.79/1.28  fof(f57,plain,(
% 6.79/1.28    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 6.79/1.28    inference(cnf_transformation,[],[f46])).
% 6.79/1.28  fof(f5110,plain,(
% 6.79/1.28    ~spl4_28 | ~spl4_45 | spl4_56),
% 6.79/1.28    inference(avatar_contradiction_clause,[],[f5109])).
% 6.79/1.28  fof(f5109,plain,(
% 6.79/1.28    $false | (~spl4_28 | ~spl4_45 | spl4_56)),
% 6.79/1.28    inference(subsumption_resolution,[],[f5108,f54])).
% 6.79/1.28  fof(f5108,plain,(
% 6.79/1.28    ~l1_pre_topc(sK0) | (~spl4_28 | ~spl4_45 | spl4_56)),
% 6.79/1.28    inference(subsumption_resolution,[],[f5107,f56])).
% 6.79/1.28  fof(f5107,plain,(
% 6.79/1.28    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl4_28 | ~spl4_45 | spl4_56)),
% 6.79/1.28    inference(subsumption_resolution,[],[f5106,f1217])).
% 6.79/1.28  fof(f5106,plain,(
% 6.79/1.28    ~m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl4_45 | spl4_56)),
% 6.79/1.28    inference(subsumption_resolution,[],[f5101,f2025])).
% 6.79/1.28  fof(f2025,plain,(
% 6.79/1.28    r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) | ~spl4_45),
% 6.79/1.28    inference(avatar_component_clause,[],[f2024])).
% 6.79/1.28  fof(f2024,plain,(
% 6.79/1.28    spl4_45 <=> r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))),
% 6.79/1.28    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 6.79/1.28  fof(f5101,plain,(
% 6.79/1.28    ~r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) | ~m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl4_56),
% 6.79/1.28    inference(resolution,[],[f2405,f61])).
% 6.79/1.28  fof(f2405,plain,(
% 6.79/1.28    ~r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | spl4_56),
% 6.79/1.28    inference(avatar_component_clause,[],[f2403])).
% 6.79/1.28  fof(f2403,plain,(
% 6.79/1.28    spl4_56 <=> r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 6.79/1.28    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).
% 6.79/1.28  fof(f4765,plain,(
% 6.79/1.28    ~spl4_55 | ~spl4_56 | ~spl4_57),
% 6.79/1.28    inference(avatar_split_clause,[],[f3348,f2408,f2403,f2399])).
% 6.79/1.28  fof(f3348,plain,(
% 6.79/1.28    ~r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | ~r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | ~spl4_57),
% 6.79/1.28    inference(resolution,[],[f2409,f94])).
% 6.79/1.28  fof(f2409,plain,(
% 6.79/1.28    ( ! [X1] : (~r1_tarski(X1,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | ~r1_tarski(k1_tops_1(sK0,sK2),X1) | ~r1_tarski(k1_tops_1(sK0,sK1),X1)) ) | ~spl4_57),
% 6.79/1.28    inference(avatar_component_clause,[],[f2408])).
% 6.79/1.28  fof(f2819,plain,(
% 6.79/1.28    spl4_54),
% 6.79/1.28    inference(avatar_contradiction_clause,[],[f2818])).
% 6.79/1.28  fof(f2818,plain,(
% 6.79/1.28    $false | spl4_54),
% 6.79/1.28    inference(subsumption_resolution,[],[f2811,f101])).
% 6.79/1.28  fof(f101,plain,(
% 6.79/1.28    r1_tarski(sK2,u1_struct_0(sK0))),
% 6.79/1.28    inference(resolution,[],[f76,f56])).
% 6.79/1.28  fof(f76,plain,(
% 6.79/1.28    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 6.79/1.28    inference(cnf_transformation,[],[f53])).
% 6.79/1.28  fof(f53,plain,(
% 6.79/1.28    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 6.79/1.28    inference(nnf_transformation,[],[f19])).
% 6.79/1.28  fof(f19,axiom,(
% 6.79/1.28    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 6.79/1.28    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 6.79/1.28  fof(f2811,plain,(
% 6.79/1.28    ~r1_tarski(sK2,u1_struct_0(sK0)) | spl4_54),
% 6.79/1.28    inference(resolution,[],[f2603,f200])).
% 6.79/1.28  fof(f200,plain,(
% 6.79/1.28    r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 6.79/1.28    inference(subsumption_resolution,[],[f197,f54])).
% 6.79/1.28  fof(f197,plain,(
% 6.79/1.28    r1_tarski(k1_tops_1(sK0,sK2),sK2) | ~l1_pre_topc(sK0)),
% 6.79/1.28    inference(resolution,[],[f60,f56])).
% 6.79/1.28  fof(f60,plain,(
% 6.79/1.28    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 6.79/1.28    inference(cnf_transformation,[],[f26])).
% 6.79/1.28  fof(f26,plain,(
% 6.79/1.28    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.79/1.28    inference(ennf_transformation,[],[f21])).
% 6.79/1.28  fof(f21,axiom,(
% 6.79/1.28    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 6.79/1.28    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 6.79/1.28  fof(f2603,plain,(
% 6.79/1.28    ( ! [X0] : (~r1_tarski(k1_tops_1(sK0,sK2),X0) | ~r1_tarski(X0,u1_struct_0(sK0))) ) | spl4_54),
% 6.79/1.28    inference(resolution,[],[f2602,f81])).
% 6.79/1.28  fof(f2602,plain,(
% 6.79/1.28    ~r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) | spl4_54),
% 6.79/1.28    inference(resolution,[],[f2397,f77])).
% 6.79/1.28  fof(f77,plain,(
% 6.79/1.28    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 6.79/1.28    inference(cnf_transformation,[],[f53])).
% 6.79/1.28  fof(f2397,plain,(
% 6.79/1.28    ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_54),
% 6.79/1.28    inference(avatar_component_clause,[],[f2395])).
% 6.79/1.28  fof(f2583,plain,(
% 6.79/1.28    spl4_39),
% 6.79/1.28    inference(avatar_contradiction_clause,[],[f2582])).
% 6.79/1.28  fof(f2582,plain,(
% 6.79/1.28    $false | spl4_39),
% 6.79/1.28    inference(subsumption_resolution,[],[f2575,f100])).
% 6.79/1.28  fof(f100,plain,(
% 6.79/1.28    r1_tarski(sK1,u1_struct_0(sK0))),
% 6.79/1.28    inference(resolution,[],[f76,f55])).
% 6.79/1.28  fof(f2575,plain,(
% 6.79/1.28    ~r1_tarski(sK1,u1_struct_0(sK0)) | spl4_39),
% 6.79/1.28    inference(resolution,[],[f2415,f199])).
% 6.79/1.28  fof(f199,plain,(
% 6.79/1.28    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 6.79/1.28    inference(subsumption_resolution,[],[f196,f54])).
% 6.79/1.28  fof(f196,plain,(
% 6.79/1.28    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0)),
% 6.79/1.28    inference(resolution,[],[f60,f55])).
% 6.79/1.28  fof(f2415,plain,(
% 6.79/1.28    ( ! [X0] : (~r1_tarski(k1_tops_1(sK0,sK1),X0) | ~r1_tarski(X0,u1_struct_0(sK0))) ) | spl4_39),
% 6.79/1.28    inference(resolution,[],[f2414,f81])).
% 6.79/1.28  fof(f2414,plain,(
% 6.79/1.28    ~r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | spl4_39),
% 6.79/1.28    inference(resolution,[],[f1795,f77])).
% 6.79/1.28  fof(f1795,plain,(
% 6.79/1.28    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_39),
% 6.79/1.28    inference(avatar_component_clause,[],[f1793])).
% 6.79/1.28  fof(f2201,plain,(
% 6.79/1.28    spl4_45),
% 6.79/1.28    inference(avatar_contradiction_clause,[],[f2200])).
% 6.79/1.28  fof(f2200,plain,(
% 6.79/1.28    $false | spl4_45),
% 6.79/1.28    inference(subsumption_resolution,[],[f2199,f55])).
% 6.79/1.28  fof(f2199,plain,(
% 6.79/1.28    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl4_45),
% 6.79/1.28    inference(subsumption_resolution,[],[f2198,f56])).
% 6.79/1.28  fof(f2198,plain,(
% 6.79/1.28    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl4_45),
% 6.79/1.28    inference(subsumption_resolution,[],[f2159,f63])).
% 6.79/1.28  fof(f2159,plain,(
% 6.79/1.28    ~r1_tarski(k4_xboole_0(sK2,sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl4_45),
% 6.79/1.28    inference(resolution,[],[f393,f2026])).
% 6.79/1.28  fof(f2026,plain,(
% 6.79/1.28    ~r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) | spl4_45),
% 6.79/1.28    inference(avatar_component_clause,[],[f2024])).
% 6.79/1.28  fof(f1275,plain,(
% 6.79/1.28    spl4_28),
% 6.79/1.28    inference(avatar_contradiction_clause,[],[f1274])).
% 6.79/1.28  fof(f1274,plain,(
% 6.79/1.28    $false | spl4_28),
% 6.79/1.28    inference(subsumption_resolution,[],[f1273,f55])).
% 6.79/1.28  fof(f1273,plain,(
% 6.79/1.28    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl4_28),
% 6.79/1.28    inference(subsumption_resolution,[],[f1272,f56])).
% 6.79/1.28  fof(f1272,plain,(
% 6.79/1.28    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl4_28),
% 6.79/1.28    inference(resolution,[],[f1218,f83])).
% 6.79/1.28  fof(f83,plain,(
% 6.79/1.28    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.79/1.28    inference(cnf_transformation,[],[f40])).
% 6.79/1.28  fof(f40,plain,(
% 6.79/1.28    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.79/1.28    inference(flattening,[],[f39])).
% 6.79/1.28  fof(f39,plain,(
% 6.79/1.28    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 6.79/1.28    inference(ennf_transformation,[],[f16])).
% 6.79/1.28  fof(f16,axiom,(
% 6.79/1.28    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 6.79/1.28    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 6.79/1.28  fof(f1218,plain,(
% 6.79/1.28    ~m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_28),
% 6.79/1.28    inference(avatar_component_clause,[],[f1216])).
% 6.79/1.28  % SZS output end Proof for theBenchmark
% 6.79/1.28  % (20109)------------------------------
% 6.79/1.28  % (20109)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.79/1.28  % (20109)Termination reason: Refutation
% 6.79/1.28  
% 6.79/1.28  % (20109)Memory used [KB]: 9722
% 6.79/1.28  % (20109)Time elapsed: 0.865 s
% 6.79/1.28  % (20109)------------------------------
% 6.79/1.28  % (20109)------------------------------
% 6.79/1.28  % (20081)Success in time 0.914 s
%------------------------------------------------------------------------------
