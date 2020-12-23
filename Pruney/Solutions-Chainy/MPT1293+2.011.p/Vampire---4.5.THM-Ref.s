%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 180 expanded)
%              Number of leaves         :   18 (  61 expanded)
%              Depth                    :   24
%              Number of atoms          :  198 ( 516 expanded)
%              Number of equality atoms :   22 (  43 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f423,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f228,f244,f422])).

fof(f422,plain,
    ( ~ spl3_5
    | ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f421])).

fof(f421,plain,
    ( $false
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f419,f48])).

fof(f48,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f419,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(resolution,[],[f412,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

fof(f412,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1)
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(resolution,[],[f91,f357])).

fof(f357,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK1,sK2))
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(resolution,[],[f344,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(f344,plain,
    ( ~ r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK1,sK2)))
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f343,f123])).

fof(f123,plain,(
    ! [X2,X3] : k3_tarski(k2_xboole_0(X2,X3)) = k3_tarski(k2_xboole_0(X3,X2)) ),
    inference(superposition,[],[f85,f36])).

fof(f36,plain,(
    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_zfmisc_1)).

fof(f85,plain,(
    ! [X2,X3] : k2_xboole_0(k3_tarski(X3),k3_tarski(X2)) = k3_tarski(k2_xboole_0(X2,X3)) ),
    inference(superposition,[],[f36,f34])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f343,plain,
    ( ~ r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK2,sK1)))
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f342,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f342,plain,
    ( ~ r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))))
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f339,f36])).

fof(f339,plain,
    ( ~ r1_tarski(k3_tarski(sK1),k2_xboole_0(k3_tarski(sK2),k3_tarski(k4_xboole_0(sK1,sK2))))
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(resolution,[],[f320,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f320,plain,
    ( ~ r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2)))
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f319,f281])).

fof(f281,plain,
    ( m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f280,f30])).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f24,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2)))
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),X1),k5_setfam_1(u1_struct_0(sK0),X2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),X1),k5_setfam_1(u1_struct_0(sK0),X2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),X2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),X2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2)))
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tops_2)).

fof(f280,plain,
    ( m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_5 ),
    inference(superposition,[],[f167,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f167,plain,
    ( m1_subset_1(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl3_5
  <=> m1_subset_1(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f319,plain,
    ( ~ r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_9 ),
    inference(superposition,[],[f315,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(f315,plain,
    ( ~ r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2)))
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f313,f202])).

fof(f202,plain,
    ( m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl3_9
  <=> m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f313,plain,
    ( ~ r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f220,f45])).

fof(f220,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f186,f30])).

fof(f186,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(superposition,[],[f177,f45])).

fof(f177,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) ),
    inference(subsumption_resolution,[],[f175,f31])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f25])).

fof(f175,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(superposition,[],[f163,f38])).

fof(f163,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) ),
    inference(subsumption_resolution,[],[f160,f30])).

fof(f160,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(superposition,[],[f32,f38])).

fof(f32,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) ),
    inference(cnf_transformation,[],[f25])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k2_xboole_0(X1,X0))
      | ~ r1_tarski(k4_xboole_0(X2,X0),X1) ) ),
    inference(superposition,[],[f47,f34])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f244,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f243])).

fof(f243,plain,
    ( $false
    | spl3_5 ),
    inference(subsumption_resolution,[],[f242,f50])).

fof(f50,plain,(
    r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f42,f30])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f242,plain,
    ( ~ r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_5 ),
    inference(resolution,[],[f222,f44])).

fof(f222,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_5 ),
    inference(subsumption_resolution,[],[f188,f30])).

fof(f188,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl3_5 ),
    inference(superposition,[],[f174,f45])).

fof(f174,plain,
    ( ~ r1_tarski(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_5 ),
    inference(resolution,[],[f168,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f168,plain,
    ( ~ m1_subset_1(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f166])).

fof(f228,plain,(
    spl3_9 ),
    inference(avatar_contradiction_clause,[],[f227])).

fof(f227,plain,
    ( $false
    | spl3_9 ),
    inference(subsumption_resolution,[],[f226,f50])).

fof(f226,plain,
    ( ~ r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_9 ),
    inference(resolution,[],[f225,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X1),X0)
      | ~ r1_tarski(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f37,f33])).

fof(f33,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f225,plain,
    ( ~ r1_tarski(k3_tarski(sK1),u1_struct_0(sK0))
    | spl3_9 ),
    inference(resolution,[],[f203,f43])).

fof(f203,plain,
    ( ~ m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f201])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:10:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (26407)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.49  % (26415)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.51  % (26400)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.53  % (26405)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.53  % (26406)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.53  % (26401)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.54  % (26413)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.54  % (26417)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.54  % (26414)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.55  % (26416)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.55  % (26409)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.55  % (26421)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.55  % (26422)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.55  % (26408)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.56  % (26401)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f423,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(avatar_sat_refutation,[],[f228,f244,f422])).
% 0.21/0.56  fof(f422,plain,(
% 0.21/0.56    ~spl3_5 | ~spl3_9),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f421])).
% 0.21/0.56  fof(f421,plain,(
% 0.21/0.56    $false | (~spl3_5 | ~spl3_9)),
% 0.21/0.56    inference(subsumption_resolution,[],[f419,f48])).
% 0.21/0.56  fof(f48,plain,(
% 0.21/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.56    inference(equality_resolution,[],[f40])).
% 0.21/0.56  fof(f40,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.56    inference(cnf_transformation,[],[f27])).
% 0.21/0.56  fof(f27,plain,(
% 0.21/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.56    inference(flattening,[],[f26])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.56    inference(nnf_transformation,[],[f2])).
% 0.21/0.56  fof(f2,axiom,(
% 0.21/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.56  fof(f419,plain,(
% 0.21/0.56    ~r1_tarski(sK1,sK1) | (~spl3_5 | ~spl3_9)),
% 0.21/0.56    inference(resolution,[],[f412,f44])).
% 0.21/0.56  fof(f44,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f18])).
% 0.21/0.56  fof(f18,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f3])).
% 0.21/0.56  fof(f3,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),X1))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).
% 0.21/0.56  fof(f412,plain,(
% 0.21/0.56    ~r1_tarski(k4_xboole_0(sK1,sK2),sK1) | (~spl3_5 | ~spl3_9)),
% 0.21/0.56    inference(resolution,[],[f91,f357])).
% 0.21/0.56  fof(f357,plain,(
% 0.21/0.56    ~r1_tarski(sK1,k2_xboole_0(sK1,sK2)) | (~spl3_5 | ~spl3_9)),
% 0.21/0.56    inference(resolution,[],[f344,f37])).
% 0.21/0.56  fof(f37,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f16])).
% 0.21/0.56  fof(f16,plain,(
% 0.21/0.56    ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f7])).
% 0.21/0.56  fof(f7,axiom,(
% 0.21/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).
% 0.21/0.56  fof(f344,plain,(
% 0.21/0.56    ~r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK1,sK2))) | (~spl3_5 | ~spl3_9)),
% 0.21/0.56    inference(forward_demodulation,[],[f343,f123])).
% 0.21/0.56  fof(f123,plain,(
% 0.21/0.56    ( ! [X2,X3] : (k3_tarski(k2_xboole_0(X2,X3)) = k3_tarski(k2_xboole_0(X3,X2))) )),
% 0.21/0.56    inference(superposition,[],[f85,f36])).
% 0.21/0.56  fof(f36,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f8])).
% 0.21/0.56  fof(f8,axiom,(
% 0.21/0.56    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_zfmisc_1)).
% 0.21/0.56  fof(f85,plain,(
% 0.21/0.56    ( ! [X2,X3] : (k2_xboole_0(k3_tarski(X3),k3_tarski(X2)) = k3_tarski(k2_xboole_0(X2,X3))) )),
% 0.21/0.56    inference(superposition,[],[f36,f34])).
% 0.21/0.56  fof(f34,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.56  fof(f343,plain,(
% 0.21/0.56    ~r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK2,sK1))) | (~spl3_5 | ~spl3_9)),
% 0.21/0.56    inference(forward_demodulation,[],[f342,f35])).
% 0.21/0.56  fof(f35,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f4])).
% 0.21/0.56  fof(f4,axiom,(
% 0.21/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.56  fof(f342,plain,(
% 0.21/0.56    ~r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)))) | (~spl3_5 | ~spl3_9)),
% 0.21/0.56    inference(forward_demodulation,[],[f339,f36])).
% 0.21/0.56  fof(f339,plain,(
% 0.21/0.56    ~r1_tarski(k3_tarski(sK1),k2_xboole_0(k3_tarski(sK2),k3_tarski(k4_xboole_0(sK1,sK2)))) | (~spl3_5 | ~spl3_9)),
% 0.21/0.56    inference(resolution,[],[f320,f46])).
% 0.21/0.56  fof(f46,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f20])).
% 0.21/0.56  fof(f20,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.21/0.56    inference(ennf_transformation,[],[f5])).
% 0.21/0.56  fof(f5,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 0.21/0.56  fof(f320,plain,(
% 0.21/0.56    ~r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2))) | (~spl3_5 | ~spl3_9)),
% 0.21/0.56    inference(subsumption_resolution,[],[f319,f281])).
% 0.21/0.56  fof(f281,plain,(
% 0.21/0.56    m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_5),
% 0.21/0.56    inference(subsumption_resolution,[],[f280,f30])).
% 0.21/0.56  fof(f30,plain,(
% 0.21/0.56    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.56    inference(cnf_transformation,[],[f25])).
% 0.21/0.56  fof(f25,plain,(
% 0.21/0.56    ((~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_struct_0(sK0)),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f24,f23,f22])).
% 0.21/0.56  fof(f22,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),X1),k5_setfam_1(u1_struct_0(sK0),X2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_struct_0(sK0))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f23,plain,(
% 0.21/0.56    ? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),X1),k5_setfam_1(u1_struct_0(sK0),X2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),X2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f24,plain,(
% 0.21/0.56    ? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),X2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f15,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_struct_0(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f14])).
% 0.21/0.56  fof(f14,negated_conjecture,(
% 0.21/0.56    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))))))),
% 0.21/0.56    inference(negated_conjecture,[],[f13])).
% 0.21/0.56  fof(f13,conjecture,(
% 0.21/0.56    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tops_2)).
% 0.21/0.56  fof(f280,plain,(
% 0.21/0.56    m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_5),
% 0.21/0.56    inference(superposition,[],[f167,f45])).
% 0.21/0.56  fof(f45,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f19])).
% 0.21/0.56  fof(f19,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f10])).
% 0.21/0.56  fof(f10,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.21/0.56  fof(f167,plain,(
% 0.21/0.56    m1_subset_1(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_5),
% 0.21/0.56    inference(avatar_component_clause,[],[f166])).
% 0.21/0.56  fof(f166,plain,(
% 0.21/0.56    spl3_5 <=> m1_subset_1(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.56  fof(f319,plain,(
% 0.21/0.56    ~r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2))) | ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_9),
% 0.21/0.56    inference(superposition,[],[f315,f38])).
% 0.21/0.56  fof(f38,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f17])).
% 0.21/0.56  fof(f17,plain,(
% 0.21/0.56    ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.56    inference(ennf_transformation,[],[f11])).
% 0.21/0.56  fof(f11,axiom,(
% 0.21/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k3_tarski(X1) = k5_setfam_1(X0,X1))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).
% 0.21/0.56  fof(f315,plain,(
% 0.21/0.56    ~r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) | ~spl3_9),
% 0.21/0.56    inference(subsumption_resolution,[],[f313,f202])).
% 0.21/0.56  fof(f202,plain,(
% 0.21/0.56    m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_9),
% 0.21/0.56    inference(avatar_component_clause,[],[f201])).
% 0.21/0.56  fof(f201,plain,(
% 0.21/0.56    spl3_9 <=> m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.56  fof(f313,plain,(
% 0.21/0.56    ~r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) | ~m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.56    inference(superposition,[],[f220,f45])).
% 0.21/0.56  fof(f220,plain,(
% 0.21/0.56    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2)))),
% 0.21/0.56    inference(subsumption_resolution,[],[f186,f30])).
% 0.21/0.56  fof(f186,plain,(
% 0.21/0.56    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.56    inference(superposition,[],[f177,f45])).
% 0.21/0.56  fof(f177,plain,(
% 0.21/0.56    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))),
% 0.21/0.56    inference(subsumption_resolution,[],[f175,f31])).
% 0.21/0.56  fof(f31,plain,(
% 0.21/0.56    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.56    inference(cnf_transformation,[],[f25])).
% 0.21/0.56  fof(f175,plain,(
% 0.21/0.56    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.56    inference(superposition,[],[f163,f38])).
% 0.21/0.56  fof(f163,plain,(
% 0.21/0.56    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))),
% 0.21/0.56    inference(subsumption_resolution,[],[f160,f30])).
% 0.21/0.56  fof(f160,plain,(
% 0.21/0.56    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.56    inference(superposition,[],[f32,f38])).
% 0.21/0.56  fof(f32,plain,(
% 0.21/0.56    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))),
% 0.21/0.56    inference(cnf_transformation,[],[f25])).
% 0.21/0.56  fof(f91,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (r1_tarski(X2,k2_xboole_0(X1,X0)) | ~r1_tarski(k4_xboole_0(X2,X0),X1)) )),
% 0.21/0.56    inference(superposition,[],[f47,f34])).
% 0.21/0.56  fof(f47,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f21])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.21/0.56    inference(ennf_transformation,[],[f6])).
% 0.21/0.56  fof(f6,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 0.21/0.56  fof(f244,plain,(
% 0.21/0.56    spl3_5),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f243])).
% 0.21/0.56  fof(f243,plain,(
% 0.21/0.56    $false | spl3_5),
% 0.21/0.56    inference(subsumption_resolution,[],[f242,f50])).
% 0.21/0.56  fof(f50,plain,(
% 0.21/0.56    r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.56    inference(resolution,[],[f42,f30])).
% 0.21/0.56  fof(f42,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f28])).
% 0.21/0.56  fof(f28,plain,(
% 0.21/0.56    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.56    inference(nnf_transformation,[],[f12])).
% 0.21/0.56  fof(f12,axiom,(
% 0.21/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.56  fof(f242,plain,(
% 0.21/0.56    ~r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_5),
% 0.21/0.56    inference(resolution,[],[f222,f44])).
% 0.21/0.56  fof(f222,plain,(
% 0.21/0.56    ~r1_tarski(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_5),
% 0.21/0.56    inference(subsumption_resolution,[],[f188,f30])).
% 0.21/0.56  fof(f188,plain,(
% 0.21/0.56    ~r1_tarski(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl3_5),
% 0.21/0.56    inference(superposition,[],[f174,f45])).
% 0.21/0.56  fof(f174,plain,(
% 0.21/0.56    ~r1_tarski(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_5),
% 0.21/0.56    inference(resolution,[],[f168,f43])).
% 0.21/0.56  fof(f43,plain,(
% 0.21/0.56    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f28])).
% 0.21/0.56  fof(f168,plain,(
% 0.21/0.56    ~m1_subset_1(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl3_5),
% 0.21/0.56    inference(avatar_component_clause,[],[f166])).
% 0.21/0.56  fof(f228,plain,(
% 0.21/0.56    spl3_9),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f227])).
% 0.21/0.56  fof(f227,plain,(
% 0.21/0.56    $false | spl3_9),
% 0.21/0.56    inference(subsumption_resolution,[],[f226,f50])).
% 0.21/0.56  fof(f226,plain,(
% 0.21/0.56    ~r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_9),
% 0.21/0.56    inference(resolution,[],[f225,f54])).
% 0.21/0.56  fof(f54,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_tarski(k3_tarski(X1),X0) | ~r1_tarski(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.56    inference(superposition,[],[f37,f33])).
% 0.21/0.56  fof(f33,plain,(
% 0.21/0.56    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f9])).
% 0.21/0.56  fof(f9,axiom,(
% 0.21/0.56    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 0.21/0.56  fof(f225,plain,(
% 0.21/0.56    ~r1_tarski(k3_tarski(sK1),u1_struct_0(sK0)) | spl3_9),
% 0.21/0.56    inference(resolution,[],[f203,f43])).
% 0.21/0.56  fof(f203,plain,(
% 0.21/0.56    ~m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_9),
% 0.21/0.56    inference(avatar_component_clause,[],[f201])).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (26401)------------------------------
% 0.21/0.56  % (26401)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (26401)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (26401)Memory used [KB]: 6396
% 0.21/0.56  % (26401)Time elapsed: 0.134 s
% 0.21/0.56  % (26401)------------------------------
% 0.21/0.56  % (26401)------------------------------
% 1.49/0.56  % (26396)Success in time 0.195 s
%------------------------------------------------------------------------------
