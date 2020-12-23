%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:17 EST 2020

% Result     : Theorem 12.99s
% Output     : Refutation 12.99s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 235 expanded)
%              Number of leaves         :   21 (  79 expanded)
%              Depth                    :   15
%              Number of atoms          :  190 ( 589 expanded)
%              Number of equality atoms :   40 ( 107 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6147,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f118,f1745,f6144])).

fof(f6144,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f6131])).

fof(f6131,plain,
    ( $false
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f61,f60,f2850,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f2850,plain,
    ( ! [X0] : ~ r1_tarski(k3_tarski(k3_tarski(k2_tarski(sK1,X0))),k3_tarski(k3_tarski(k2_tarski(sK1,sK2))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f2849,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f2849,plain,
    ( ! [X0] : ~ r1_tarski(k3_tarski(k3_tarski(k2_tarski(sK1,X0))),k3_tarski(k3_tarski(k2_tarski(sK2,sK1))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f2848,f57])).

fof(f57,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f42,f41,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f2848,plain,
    ( ! [X0] : ~ r1_tarski(k3_tarski(k3_tarski(k2_tarski(sK1,X0))),k3_tarski(k3_tarski(k2_tarski(sK2,k4_xboole_0(sK1,sK2)))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f2847,f58])).

fof(f58,plain,(
    ! [X0,X1] : k3_tarski(k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(k3_tarski(X0),k3_tarski(X1))) ),
    inference(definition_unfolding,[],[f43,f41,f41])).

fof(f43,plain,(
    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_zfmisc_1)).

fof(f2847,plain,
    ( ! [X0] : ~ r1_tarski(k3_tarski(k3_tarski(k2_tarski(sK1,X0))),k3_tarski(k2_tarski(k3_tarski(sK2),k3_tarski(k4_xboole_0(sK1,sK2)))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f2817,f1391])).

fof(f1391,plain,(
    ! [X0] : k3_tarski(k4_xboole_0(sK1,X0)) = k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f407,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(f407,plain,(
    ! [X0] : m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f70,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f70,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f39,f64,f54])).

fof(f64,plain,(
    r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f33,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f26,f25,f24])).

fof(f24,plain,
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

fof(f25,plain,
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

fof(f26,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),X2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2)))
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tops_2)).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f2817,plain,
    ( ! [X0] : ~ r1_tarski(k3_tarski(k3_tarski(k2_tarski(sK1,X0))),k3_tarski(k2_tarski(k3_tarski(sK2),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2)))))
    | spl3_1 ),
    inference(superposition,[],[f761,f58])).

fof(f761,plain,
    ( ! [X0] : ~ r1_tarski(k3_tarski(k2_tarski(k3_tarski(sK1),X0)),k3_tarski(k2_tarski(k3_tarski(sK2),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2)))))
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f56,f217,f54])).

fof(f217,plain,
    ( ~ r1_tarski(k3_tarski(sK1),k3_tarski(k2_tarski(k3_tarski(sK2),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2)))))
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f113,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) ) ),
    inference(definition_unfolding,[],[f53,f41])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f113,plain,
    ( ~ r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2)))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl3_1
  <=> r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f56,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f38,f41])).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f60,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f61,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1745,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f1737])).

fof(f1737,plain,
    ( $false
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f61,f60,f1716,f54])).

fof(f1716,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))
    | spl3_2 ),
    inference(forward_demodulation,[],[f1706,f36])).

fof(f36,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f1706,plain,
    ( ~ r1_tarski(k3_tarski(k1_zfmisc_1(u1_struct_0(sK0))),u1_struct_0(sK0))
    | spl3_2 ),
    inference(superposition,[],[f1324,f449])).

fof(f449,plain,(
    k1_zfmisc_1(u1_struct_0(sK0)) = k3_tarski(k2_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f448,f40])).

fof(f448,plain,(
    k1_zfmisc_1(u1_struct_0(sK0)) = k3_tarski(k2_tarski(k1_zfmisc_1(u1_struct_0(sK0)),sK1)) ),
    inference(forward_demodulation,[],[f442,f55])).

fof(f55,plain,(
    ! [X0] : k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f37,f41])).

fof(f37,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f442,plain,(
    k3_tarski(k2_tarski(k1_zfmisc_1(u1_struct_0(sK0)),sK1)) = k3_tarski(k2_tarski(k1_zfmisc_1(u1_struct_0(sK0)),k1_xboole_0)) ),
    inference(superposition,[],[f57,f71])).

fof(f71,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f64,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f1324,plain,
    ( ! [X0] : ~ r1_tarski(k3_tarski(k3_tarski(k2_tarski(sK1,X0))),u1_struct_0(sK0))
    | spl3_2 ),
    inference(superposition,[],[f146,f58])).

fof(f146,plain,
    ( ! [X0] : ~ r1_tarski(k3_tarski(k2_tarski(k3_tarski(sK1),X0)),u1_struct_0(sK0))
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f56,f142,f54])).

fof(f142,plain,
    ( ~ r1_tarski(k3_tarski(sK1),u1_struct_0(sK0))
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f117,f49])).

fof(f117,plain,
    ( ~ m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl3_2
  <=> m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f118,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f109,f115,f111])).

fof(f109,plain,
    ( ~ m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f108,f62])).

fof(f62,plain,(
    k5_setfam_1(u1_struct_0(sK0),sK1) = k3_tarski(sK1) ),
    inference(unit_resulting_resolution,[],[f33,f44])).

fof(f108,plain,
    ( ~ r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f107,f62])).

fof(f107,plain,
    ( ~ r1_tarski(k4_xboole_0(k5_setfam_1(u1_struct_0(sK0),sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f106,f73])).

fof(f73,plain,(
    k5_setfam_1(u1_struct_0(sK0),sK2) = k3_tarski(sK2) ),
    inference(unit_resulting_resolution,[],[f34,f44])).

fof(f34,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f27])).

fof(f106,plain,
    ( ~ r1_tarski(k4_xboole_0(k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f86,f63])).

fof(f63,plain,(
    ! [X0] : k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(unit_resulting_resolution,[],[f33,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f86,plain,
    ( ~ r1_tarski(k4_xboole_0(k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))
    | ~ m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f35,f52])).

fof(f35,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:28:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (27905)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.51  % (27898)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.51  % (27888)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (27896)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (27887)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (27886)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (27892)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.53  % (27885)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (27884)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (27906)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (27890)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (27882)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (27911)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (27910)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (27909)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (27912)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (27903)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (27899)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (27902)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (27901)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (27889)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.55  % (27895)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.55  % (27894)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.56  % (27904)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.56  % (27893)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.56  % (27883)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.56  % (27907)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.57  % (27897)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.57  % (27900)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.81/0.60  % (27908)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 2.62/0.70  % (27885)Refutation not found, incomplete strategy% (27885)------------------------------
% 2.62/0.70  % (27885)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.62/0.70  % (27885)Termination reason: Refutation not found, incomplete strategy
% 2.62/0.70  
% 2.62/0.70  % (27885)Memory used [KB]: 6268
% 2.62/0.70  % (27885)Time elapsed: 0.273 s
% 2.62/0.70  % (27885)------------------------------
% 2.62/0.70  % (27885)------------------------------
% 2.94/0.84  % (27884)Time limit reached!
% 2.94/0.84  % (27884)------------------------------
% 2.94/0.84  % (27884)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.94/0.84  % (27884)Termination reason: Time limit
% 2.94/0.84  
% 2.94/0.84  % (27884)Memory used [KB]: 6780
% 2.94/0.84  % (27884)Time elapsed: 0.428 s
% 2.94/0.84  % (27884)------------------------------
% 2.94/0.84  % (27884)------------------------------
% 3.74/0.84  % (27907)Time limit reached!
% 3.74/0.84  % (27907)------------------------------
% 3.74/0.84  % (27907)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.74/0.84  % (27907)Termination reason: Time limit
% 3.74/0.84  % (27907)Termination phase: Saturation
% 3.74/0.84  
% 3.74/0.84  % (27907)Memory used [KB]: 12153
% 3.74/0.84  % (27907)Time elapsed: 0.400 s
% 3.74/0.84  % (27907)------------------------------
% 3.74/0.84  % (27907)------------------------------
% 3.74/0.84  % (27931)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 4.07/0.91  % (27912)Time limit reached!
% 4.07/0.91  % (27912)------------------------------
% 4.07/0.91  % (27912)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.07/0.91  % (27912)Termination reason: Time limit
% 4.07/0.91  
% 4.07/0.91  % (27912)Memory used [KB]: 2174
% 4.07/0.91  % (27912)Time elapsed: 0.501 s
% 4.07/0.91  % (27912)------------------------------
% 4.07/0.91  % (27912)------------------------------
% 4.07/0.94  % (27897)Time limit reached!
% 4.07/0.94  % (27897)------------------------------
% 4.07/0.94  % (27897)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.07/0.94  % (27897)Termination reason: Time limit
% 4.07/0.94  
% 4.07/0.94  % (27897)Memory used [KB]: 3454
% 4.07/0.94  % (27897)Time elapsed: 0.529 s
% 4.07/0.94  % (27897)------------------------------
% 4.07/0.94  % (27897)------------------------------
% 4.50/0.97  % (27932)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 4.50/0.97  % (27888)Time limit reached!
% 4.50/0.97  % (27888)------------------------------
% 4.50/0.97  % (27888)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.50/0.97  % (27888)Termination reason: Time limit
% 4.50/0.97  % (27888)Termination phase: Saturation
% 4.50/0.97  
% 4.50/0.97  % (27888)Memory used [KB]: 17398
% 4.50/0.97  % (27888)Time elapsed: 0.500 s
% 4.50/0.97  % (27888)------------------------------
% 4.50/0.97  % (27888)------------------------------
% 4.85/1.00  % (27933)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 4.85/1.01  % (27933)Refutation not found, incomplete strategy% (27933)------------------------------
% 4.85/1.01  % (27933)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.85/1.01  % (27933)Termination reason: Refutation not found, incomplete strategy
% 4.85/1.01  
% 4.85/1.01  % (27933)Memory used [KB]: 6268
% 4.85/1.01  % (27933)Time elapsed: 0.088 s
% 4.85/1.01  % (27933)------------------------------
% 4.85/1.01  % (27933)------------------------------
% 4.85/1.03  % (27889)Time limit reached!
% 4.85/1.03  % (27889)------------------------------
% 4.85/1.03  % (27889)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.85/1.03  % (27889)Termination reason: Time limit
% 4.85/1.03  
% 4.85/1.03  % (27889)Memory used [KB]: 5628
% 4.85/1.03  % (27889)Time elapsed: 0.602 s
% 4.85/1.03  % (27889)------------------------------
% 4.85/1.03  % (27889)------------------------------
% 4.85/1.05  % (27934)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 5.43/1.07  % (27935)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 5.43/1.10  % (27937)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 5.43/1.14  % (27936)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 6.19/1.19  % (27938)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 6.96/1.26  % (27883)Time limit reached!
% 6.96/1.26  % (27883)------------------------------
% 6.96/1.26  % (27883)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.96/1.26  % (27883)Termination reason: Time limit
% 6.96/1.26  % (27883)Termination phase: Saturation
% 6.96/1.26  
% 6.96/1.26  % (27883)Memory used [KB]: 3070
% 6.96/1.26  % (27883)Time elapsed: 0.800 s
% 6.96/1.26  % (27883)------------------------------
% 6.96/1.26  % (27883)------------------------------
% 8.04/1.42  % (27895)Time limit reached!
% 8.04/1.42  % (27895)------------------------------
% 8.04/1.42  % (27895)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.04/1.42  % (27895)Termination reason: Time limit
% 8.04/1.42  % (27895)Termination phase: Saturation
% 8.04/1.42  
% 8.04/1.42  % (27895)Memory used [KB]: 13560
% 8.04/1.42  % (27895)Time elapsed: 1.0000 s
% 8.04/1.42  % (27895)------------------------------
% 8.04/1.42  % (27895)------------------------------
% 8.04/1.44  % (27939)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 8.04/1.45  % (27910)Time limit reached!
% 8.04/1.45  % (27910)------------------------------
% 8.04/1.45  % (27910)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.04/1.45  % (27910)Termination reason: Time limit
% 8.04/1.45  % (27910)Termination phase: Saturation
% 8.04/1.45  
% 8.04/1.45  % (27910)Memory used [KB]: 8571
% 8.04/1.45  % (27910)Time elapsed: 1.0000 s
% 8.04/1.45  % (27910)------------------------------
% 8.04/1.45  % (27910)------------------------------
% 8.96/1.52  % (27940)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 9.26/1.59  % (27941)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 9.26/1.64  % (27882)Time limit reached!
% 9.26/1.64  % (27882)------------------------------
% 9.26/1.64  % (27882)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.26/1.64  % (27882)Termination reason: Time limit
% 9.26/1.64  % (27882)Termination phase: Saturation
% 9.26/1.64  
% 9.26/1.64  % (27882)Memory used [KB]: 7675
% 9.26/1.64  % (27882)Time elapsed: 1.225 s
% 9.26/1.64  % (27882)------------------------------
% 9.26/1.64  % (27882)------------------------------
% 9.95/1.69  % (27937)Time limit reached!
% 9.95/1.69  % (27937)------------------------------
% 9.95/1.69  % (27937)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.95/1.69  % (27937)Termination reason: Time limit
% 9.95/1.69  % (27937)Termination phase: Saturation
% 9.95/1.69  
% 9.95/1.69  % (27937)Memory used [KB]: 18293
% 9.95/1.69  % (27937)Time elapsed: 0.600 s
% 9.95/1.69  % (27937)------------------------------
% 9.95/1.69  % (27937)------------------------------
% 10.57/1.70  % (27899)Time limit reached!
% 10.57/1.70  % (27899)------------------------------
% 10.57/1.70  % (27899)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.57/1.70  % (27899)Termination reason: Time limit
% 10.57/1.70  % (27899)Termination phase: Saturation
% 10.57/1.70  
% 10.57/1.70  % (27899)Memory used [KB]: 12025
% 10.57/1.70  % (27899)Time elapsed: 1.300 s
% 10.57/1.70  % (27899)------------------------------
% 10.57/1.70  % (27899)------------------------------
% 10.57/1.72  % (27887)Time limit reached!
% 10.57/1.72  % (27887)------------------------------
% 10.57/1.72  % (27887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.57/1.72  % (27887)Termination reason: Time limit
% 10.57/1.72  
% 10.57/1.72  % (27887)Memory used [KB]: 11897
% 10.57/1.72  % (27887)Time elapsed: 1.308 s
% 10.57/1.72  % (27887)------------------------------
% 10.57/1.72  % (27887)------------------------------
% 11.06/1.79  % (27942)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 11.32/1.81  % (27944)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 11.32/1.82  % (27945)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 11.54/1.84  % (27943)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 12.54/2.02  % (27909)Time limit reached!
% 12.54/2.02  % (27909)------------------------------
% 12.54/2.02  % (27909)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.54/2.02  % (27909)Termination reason: Time limit
% 12.54/2.02  
% 12.54/2.02  % (27909)Memory used [KB]: 20340
% 12.54/2.02  % (27909)Time elapsed: 1.609 s
% 12.54/2.02  % (27909)------------------------------
% 12.54/2.02  % (27909)------------------------------
% 12.99/2.09  % (27942)Refutation found. Thanks to Tanya!
% 12.99/2.09  % SZS status Theorem for theBenchmark
% 12.99/2.09  % SZS output start Proof for theBenchmark
% 12.99/2.09  fof(f6147,plain,(
% 12.99/2.09    $false),
% 12.99/2.09    inference(avatar_sat_refutation,[],[f118,f1745,f6144])).
% 12.99/2.09  fof(f6144,plain,(
% 12.99/2.09    spl3_1),
% 12.99/2.09    inference(avatar_contradiction_clause,[],[f6131])).
% 12.99/2.09  fof(f6131,plain,(
% 12.99/2.09    $false | spl3_1),
% 12.99/2.09    inference(unit_resulting_resolution,[],[f61,f60,f2850,f54])).
% 12.99/2.09  fof(f54,plain,(
% 12.99/2.09    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 12.99/2.09    inference(cnf_transformation,[],[f23])).
% 12.99/2.09  fof(f23,plain,(
% 12.99/2.09    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 12.99/2.09    inference(flattening,[],[f22])).
% 12.99/2.09  fof(f22,plain,(
% 12.99/2.09    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 12.99/2.09    inference(ennf_transformation,[],[f4])).
% 12.99/2.09  fof(f4,axiom,(
% 12.99/2.09    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 12.99/2.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 12.99/2.09  fof(f2850,plain,(
% 12.99/2.09    ( ! [X0] : (~r1_tarski(k3_tarski(k3_tarski(k2_tarski(sK1,X0))),k3_tarski(k3_tarski(k2_tarski(sK1,sK2))))) ) | spl3_1),
% 12.99/2.09    inference(forward_demodulation,[],[f2849,f40])).
% 12.99/2.09  fof(f40,plain,(
% 12.99/2.09    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 12.99/2.09    inference(cnf_transformation,[],[f9])).
% 12.99/2.09  fof(f9,axiom,(
% 12.99/2.09    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 12.99/2.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 12.99/2.09  fof(f2849,plain,(
% 12.99/2.09    ( ! [X0] : (~r1_tarski(k3_tarski(k3_tarski(k2_tarski(sK1,X0))),k3_tarski(k3_tarski(k2_tarski(sK2,sK1))))) ) | spl3_1),
% 12.99/2.09    inference(forward_demodulation,[],[f2848,f57])).
% 12.99/2.09  fof(f57,plain,(
% 12.99/2.09    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k4_xboole_0(X1,X0)))) )),
% 12.99/2.09    inference(definition_unfolding,[],[f42,f41,f41])).
% 12.99/2.09  fof(f41,plain,(
% 12.99/2.09    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 12.99/2.09    inference(cnf_transformation,[],[f10])).
% 12.99/2.09  fof(f10,axiom,(
% 12.99/2.09    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 12.99/2.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 12.99/2.09  fof(f42,plain,(
% 12.99/2.09    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 12.99/2.09    inference(cnf_transformation,[],[f6])).
% 12.99/2.09  fof(f6,axiom,(
% 12.99/2.09    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 12.99/2.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 12.99/2.09  fof(f2848,plain,(
% 12.99/2.09    ( ! [X0] : (~r1_tarski(k3_tarski(k3_tarski(k2_tarski(sK1,X0))),k3_tarski(k3_tarski(k2_tarski(sK2,k4_xboole_0(sK1,sK2)))))) ) | spl3_1),
% 12.99/2.09    inference(forward_demodulation,[],[f2847,f58])).
% 12.99/2.09  fof(f58,plain,(
% 12.99/2.09    ( ! [X0,X1] : (k3_tarski(k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(k3_tarski(X0),k3_tarski(X1)))) )),
% 12.99/2.09    inference(definition_unfolding,[],[f43,f41,f41])).
% 12.99/2.09  fof(f43,plain,(
% 12.99/2.09    ( ! [X0,X1] : (k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1))) )),
% 12.99/2.09    inference(cnf_transformation,[],[f11])).
% 12.99/2.09  fof(f11,axiom,(
% 12.99/2.09    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1))),
% 12.99/2.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_zfmisc_1)).
% 12.99/2.09  fof(f2847,plain,(
% 12.99/2.09    ( ! [X0] : (~r1_tarski(k3_tarski(k3_tarski(k2_tarski(sK1,X0))),k3_tarski(k2_tarski(k3_tarski(sK2),k3_tarski(k4_xboole_0(sK1,sK2)))))) ) | spl3_1),
% 12.99/2.09    inference(forward_demodulation,[],[f2817,f1391])).
% 12.99/2.09  fof(f1391,plain,(
% 12.99/2.09    ( ! [X0] : (k3_tarski(k4_xboole_0(sK1,X0)) = k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,X0))) )),
% 12.99/2.09    inference(unit_resulting_resolution,[],[f407,f44])).
% 12.99/2.09  fof(f44,plain,(
% 12.99/2.09    ( ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 12.99/2.09    inference(cnf_transformation,[],[f19])).
% 12.99/2.09  fof(f19,plain,(
% 12.99/2.09    ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 12.99/2.09    inference(ennf_transformation,[],[f14])).
% 12.99/2.09  fof(f14,axiom,(
% 12.99/2.09    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k3_tarski(X1) = k5_setfam_1(X0,X1))),
% 12.99/2.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).
% 12.99/2.09  fof(f407,plain,(
% 12.99/2.09    ( ! [X0] : (m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) )),
% 12.99/2.09    inference(unit_resulting_resolution,[],[f70,f49])).
% 12.99/2.09  fof(f49,plain,(
% 12.99/2.09    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 12.99/2.09    inference(cnf_transformation,[],[f30])).
% 12.99/2.09  fof(f30,plain,(
% 12.99/2.09    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 12.99/2.09    inference(nnf_transformation,[],[f15])).
% 12.99/2.09  fof(f15,axiom,(
% 12.99/2.09    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 12.99/2.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 12.99/2.09  fof(f70,plain,(
% 12.99/2.09    ( ! [X0] : (r1_tarski(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 12.99/2.09    inference(unit_resulting_resolution,[],[f39,f64,f54])).
% 12.99/2.09  fof(f64,plain,(
% 12.99/2.09    r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 12.99/2.09    inference(unit_resulting_resolution,[],[f33,f48])).
% 12.99/2.09  fof(f48,plain,(
% 12.99/2.09    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 12.99/2.09    inference(cnf_transformation,[],[f30])).
% 12.99/2.09  fof(f33,plain,(
% 12.99/2.09    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 12.99/2.09    inference(cnf_transformation,[],[f27])).
% 12.99/2.09  fof(f27,plain,(
% 12.99/2.09    ((~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_struct_0(sK0)),
% 12.99/2.09    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f26,f25,f24])).
% 12.99/2.09  fof(f24,plain,(
% 12.99/2.09    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),X1),k5_setfam_1(u1_struct_0(sK0),X2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_struct_0(sK0))),
% 12.99/2.09    introduced(choice_axiom,[])).
% 12.99/2.09  fof(f25,plain,(
% 12.99/2.09    ? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),X1),k5_setfam_1(u1_struct_0(sK0),X2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),X2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 12.99/2.09    introduced(choice_axiom,[])).
% 12.99/2.09  fof(f26,plain,(
% 12.99/2.09    ? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),X2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 12.99/2.09    introduced(choice_axiom,[])).
% 12.99/2.09  fof(f18,plain,(
% 12.99/2.09    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_struct_0(X0))),
% 12.99/2.09    inference(ennf_transformation,[],[f17])).
% 12.99/2.09  fof(f17,negated_conjecture,(
% 12.99/2.09    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))))))),
% 12.99/2.09    inference(negated_conjecture,[],[f16])).
% 12.99/2.09  fof(f16,conjecture,(
% 12.99/2.09    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))))))),
% 12.99/2.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tops_2)).
% 12.99/2.09  fof(f39,plain,(
% 12.99/2.09    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 12.99/2.09    inference(cnf_transformation,[],[f5])).
% 12.99/2.09  fof(f5,axiom,(
% 12.99/2.09    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 12.99/2.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 12.99/2.09  fof(f2817,plain,(
% 12.99/2.09    ( ! [X0] : (~r1_tarski(k3_tarski(k3_tarski(k2_tarski(sK1,X0))),k3_tarski(k2_tarski(k3_tarski(sK2),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2)))))) ) | spl3_1),
% 12.99/2.09    inference(superposition,[],[f761,f58])).
% 12.99/2.09  fof(f761,plain,(
% 12.99/2.09    ( ! [X0] : (~r1_tarski(k3_tarski(k2_tarski(k3_tarski(sK1),X0)),k3_tarski(k2_tarski(k3_tarski(sK2),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2)))))) ) | spl3_1),
% 12.99/2.09    inference(unit_resulting_resolution,[],[f56,f217,f54])).
% 12.99/2.09  fof(f217,plain,(
% 12.99/2.09    ~r1_tarski(k3_tarski(sK1),k3_tarski(k2_tarski(k3_tarski(sK2),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))))) | spl3_1),
% 12.99/2.09    inference(unit_resulting_resolution,[],[f113,f59])).
% 12.99/2.09  fof(f59,plain,(
% 12.99/2.09    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))) )),
% 12.99/2.09    inference(definition_unfolding,[],[f53,f41])).
% 12.99/2.09  fof(f53,plain,(
% 12.99/2.09    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 12.99/2.09    inference(cnf_transformation,[],[f21])).
% 12.99/2.09  fof(f21,plain,(
% 12.99/2.09    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 12.99/2.09    inference(ennf_transformation,[],[f7])).
% 12.99/2.09  fof(f7,axiom,(
% 12.99/2.09    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 12.99/2.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 12.99/2.09  fof(f113,plain,(
% 12.99/2.09    ~r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) | spl3_1),
% 12.99/2.09    inference(avatar_component_clause,[],[f111])).
% 12.99/2.09  fof(f111,plain,(
% 12.99/2.09    spl3_1 <=> r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2)))),
% 12.99/2.09    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 12.99/2.09  fof(f56,plain,(
% 12.99/2.09    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 12.99/2.09    inference(definition_unfolding,[],[f38,f41])).
% 12.99/2.09  fof(f38,plain,(
% 12.99/2.09    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 12.99/2.09    inference(cnf_transformation,[],[f8])).
% 12.99/2.09  fof(f8,axiom,(
% 12.99/2.09    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 12.99/2.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 12.99/2.09  fof(f60,plain,(
% 12.99/2.09    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 12.99/2.09    inference(equality_resolution,[],[f46])).
% 12.99/2.09  fof(f46,plain,(
% 12.99/2.09    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 12.99/2.09    inference(cnf_transformation,[],[f29])).
% 12.99/2.09  fof(f29,plain,(
% 12.99/2.09    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 12.99/2.09    inference(flattening,[],[f28])).
% 12.99/2.09  fof(f28,plain,(
% 12.99/2.09    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 12.99/2.09    inference(nnf_transformation,[],[f1])).
% 12.99/2.09  fof(f1,axiom,(
% 12.99/2.09    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 12.99/2.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 12.99/2.09  fof(f61,plain,(
% 12.99/2.09    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 12.99/2.09    inference(equality_resolution,[],[f45])).
% 12.99/2.09  fof(f45,plain,(
% 12.99/2.09    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 12.99/2.09    inference(cnf_transformation,[],[f29])).
% 12.99/2.09  fof(f1745,plain,(
% 12.99/2.09    spl3_2),
% 12.99/2.09    inference(avatar_contradiction_clause,[],[f1737])).
% 12.99/2.09  fof(f1737,plain,(
% 12.99/2.09    $false | spl3_2),
% 12.99/2.09    inference(unit_resulting_resolution,[],[f61,f60,f1716,f54])).
% 12.99/2.09  fof(f1716,plain,(
% 12.99/2.09    ~r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) | spl3_2),
% 12.99/2.09    inference(forward_demodulation,[],[f1706,f36])).
% 12.99/2.09  fof(f36,plain,(
% 12.99/2.09    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 12.99/2.09    inference(cnf_transformation,[],[f12])).
% 12.99/2.09  fof(f12,axiom,(
% 12.99/2.09    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 12.99/2.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 12.99/2.09  fof(f1706,plain,(
% 12.99/2.09    ~r1_tarski(k3_tarski(k1_zfmisc_1(u1_struct_0(sK0))),u1_struct_0(sK0)) | spl3_2),
% 12.99/2.09    inference(superposition,[],[f1324,f449])).
% 12.99/2.09  fof(f449,plain,(
% 12.99/2.09    k1_zfmisc_1(u1_struct_0(sK0)) = k3_tarski(k2_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 12.99/2.09    inference(forward_demodulation,[],[f448,f40])).
% 12.99/2.09  fof(f448,plain,(
% 12.99/2.09    k1_zfmisc_1(u1_struct_0(sK0)) = k3_tarski(k2_tarski(k1_zfmisc_1(u1_struct_0(sK0)),sK1))),
% 12.99/2.09    inference(forward_demodulation,[],[f442,f55])).
% 12.99/2.09  fof(f55,plain,(
% 12.99/2.09    ( ! [X0] : (k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0) )),
% 12.99/2.09    inference(definition_unfolding,[],[f37,f41])).
% 12.99/2.09  fof(f37,plain,(
% 12.99/2.09    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 12.99/2.09    inference(cnf_transformation,[],[f3])).
% 12.99/2.09  fof(f3,axiom,(
% 12.99/2.09    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 12.99/2.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 12.99/2.09  fof(f442,plain,(
% 12.99/2.09    k3_tarski(k2_tarski(k1_zfmisc_1(u1_struct_0(sK0)),sK1)) = k3_tarski(k2_tarski(k1_zfmisc_1(u1_struct_0(sK0)),k1_xboole_0))),
% 12.99/2.09    inference(superposition,[],[f57,f71])).
% 12.99/2.09  fof(f71,plain,(
% 12.99/2.09    k1_xboole_0 = k4_xboole_0(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 12.99/2.09    inference(unit_resulting_resolution,[],[f64,f51])).
% 12.99/2.09  fof(f51,plain,(
% 12.99/2.09    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 12.99/2.09    inference(cnf_transformation,[],[f31])).
% 12.99/2.09  fof(f31,plain,(
% 12.99/2.09    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 12.99/2.09    inference(nnf_transformation,[],[f2])).
% 12.99/2.09  fof(f2,axiom,(
% 12.99/2.09    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 12.99/2.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 12.99/2.09  fof(f1324,plain,(
% 12.99/2.09    ( ! [X0] : (~r1_tarski(k3_tarski(k3_tarski(k2_tarski(sK1,X0))),u1_struct_0(sK0))) ) | spl3_2),
% 12.99/2.09    inference(superposition,[],[f146,f58])).
% 12.99/2.09  fof(f146,plain,(
% 12.99/2.09    ( ! [X0] : (~r1_tarski(k3_tarski(k2_tarski(k3_tarski(sK1),X0)),u1_struct_0(sK0))) ) | spl3_2),
% 12.99/2.09    inference(unit_resulting_resolution,[],[f56,f142,f54])).
% 12.99/2.09  fof(f142,plain,(
% 12.99/2.09    ~r1_tarski(k3_tarski(sK1),u1_struct_0(sK0)) | spl3_2),
% 12.99/2.09    inference(unit_resulting_resolution,[],[f117,f49])).
% 12.99/2.09  fof(f117,plain,(
% 12.99/2.09    ~m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_2),
% 12.99/2.09    inference(avatar_component_clause,[],[f115])).
% 12.99/2.09  fof(f115,plain,(
% 12.99/2.09    spl3_2 <=> m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 12.99/2.09    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 12.99/2.09  fof(f118,plain,(
% 12.99/2.09    ~spl3_1 | ~spl3_2),
% 12.99/2.09    inference(avatar_split_clause,[],[f109,f115,f111])).
% 12.99/2.09  fof(f109,plain,(
% 12.99/2.09    ~m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2)))),
% 12.99/2.09    inference(forward_demodulation,[],[f108,f62])).
% 12.99/2.09  fof(f62,plain,(
% 12.99/2.09    k5_setfam_1(u1_struct_0(sK0),sK1) = k3_tarski(sK1)),
% 12.99/2.09    inference(unit_resulting_resolution,[],[f33,f44])).
% 12.99/2.09  fof(f108,plain,(
% 12.99/2.09    ~r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) | ~m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 12.99/2.09    inference(forward_demodulation,[],[f107,f62])).
% 12.99/2.09  fof(f107,plain,(
% 12.99/2.09    ~r1_tarski(k4_xboole_0(k5_setfam_1(u1_struct_0(sK0),sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) | ~m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 12.99/2.09    inference(forward_demodulation,[],[f106,f73])).
% 12.99/2.09  fof(f73,plain,(
% 12.99/2.09    k5_setfam_1(u1_struct_0(sK0),sK2) = k3_tarski(sK2)),
% 12.99/2.09    inference(unit_resulting_resolution,[],[f34,f44])).
% 12.99/2.09  fof(f34,plain,(
% 12.99/2.09    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 12.99/2.09    inference(cnf_transformation,[],[f27])).
% 12.99/2.09  fof(f106,plain,(
% 12.99/2.09    ~r1_tarski(k4_xboole_0(k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) | ~m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 12.99/2.09    inference(forward_demodulation,[],[f86,f63])).
% 12.99/2.09  fof(f63,plain,(
% 12.99/2.09    ( ! [X0] : (k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0) = k4_xboole_0(sK1,X0)) )),
% 12.99/2.09    inference(unit_resulting_resolution,[],[f33,f52])).
% 12.99/2.09  fof(f52,plain,(
% 12.99/2.09    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 12.99/2.09    inference(cnf_transformation,[],[f20])).
% 12.99/2.09  fof(f20,plain,(
% 12.99/2.09    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 12.99/2.09    inference(ennf_transformation,[],[f13])).
% 12.99/2.09  fof(f13,axiom,(
% 12.99/2.09    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 12.99/2.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 12.99/2.09  fof(f86,plain,(
% 12.99/2.09    ~r1_tarski(k4_xboole_0(k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) | ~m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 12.99/2.09    inference(superposition,[],[f35,f52])).
% 12.99/2.09  fof(f35,plain,(
% 12.99/2.09    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))),
% 12.99/2.09    inference(cnf_transformation,[],[f27])).
% 12.99/2.09  % SZS output end Proof for theBenchmark
% 12.99/2.09  % (27942)------------------------------
% 12.99/2.09  % (27942)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.99/2.09  % (27942)Termination reason: Refutation
% 12.99/2.09  
% 12.99/2.09  % (27942)Memory used [KB]: 13304
% 12.99/2.09  % (27942)Time elapsed: 0.422 s
% 12.99/2.09  % (27942)------------------------------
% 12.99/2.09  % (27942)------------------------------
% 12.99/2.10  % (27880)Success in time 1.724 s
%------------------------------------------------------------------------------
