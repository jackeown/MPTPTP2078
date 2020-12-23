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
% DateTime   : Thu Dec  3 13:11:38 EST 2020

% Result     : Theorem 21.26s
% Output     : Refutation 21.26s
% Verified   : 
% Statistics : Number of formulae       :  201 (1074 expanded)
%              Number of leaves         :   33 ( 312 expanded)
%              Depth                    :   33
%              Number of atoms          :  608 (4343 expanded)
%              Number of equality atoms :  138 (1229 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f34182,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f127,f128,f4461,f4475,f4515,f4558,f4809,f4913,f4984,f14047,f34181])).

fof(f34181,plain,
    ( ~ spl4_2
    | spl4_75
    | ~ spl4_139 ),
    inference(avatar_contradiction_clause,[],[f34180])).

fof(f34180,plain,
    ( $false
    | ~ spl4_2
    | spl4_75
    | ~ spl4_139 ),
    inference(subsumption_resolution,[],[f34177,f4774])).

fof(f4774,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | spl4_75 ),
    inference(avatar_component_clause,[],[f4773])).

fof(f4773,plain,
    ( spl4_75
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_75])])).

fof(f34177,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl4_2
    | ~ spl4_139 ),
    inference(backward_demodulation,[],[f1057,f33378])).

fof(f33378,plain,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_139 ),
    inference(forward_demodulation,[],[f33359,f125])).

fof(f125,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl4_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f33359,plain,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1))
    | ~ spl4_139 ),
    inference(superposition,[],[f22799,f24578])).

fof(f24578,plain,
    ( ! [X11] : k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X11) = k7_subset_1(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1),X11)
    | ~ spl4_139 ),
    inference(resolution,[],[f22738,f14036])).

fof(f14036,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_139 ),
    inference(avatar_component_clause,[],[f14035])).

fof(f14035,plain,
    ( spl4_139
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_139])])).

fof(f22738,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) ) ),
    inference(backward_demodulation,[],[f100,f4867])).

fof(f4867,plain,(
    ! [X4,X3] : k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,X4))) = k7_subset_1(X3,X3,X4) ),
    inference(resolution,[],[f488,f138])).

fof(f138,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(forward_demodulation,[],[f136,f133])).

fof(f133,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f96,f95])).

fof(f95,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f61,f72])).

fof(f72,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f61,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f96,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f62,f94])).

fof(f94,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f73,f72])).

fof(f73,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f62,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f136,plain,(
    ! [X0] : r1_tarski(k5_xboole_0(X0,k1_xboole_0),X0) ),
    inference(superposition,[],[f97,f95])).

fof(f97,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(definition_unfolding,[],[f70,f94])).

fof(f70,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f488,plain,(
    ! [X2,X3,X1] :
      ( ~ r1_tarski(X2,X1)
      | k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))) = k7_subset_1(X1,X2,X3) ) ),
    inference(resolution,[],[f100,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ) ),
    inference(definition_unfolding,[],[f81,f94])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f22799,plain,(
    ! [X120] : sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(X120,X120,sK1)) ),
    inference(backward_demodulation,[],[f8233,f4867])).

fof(f8233,plain,(
    ! [X120] : sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(X120,k1_setfam_1(k2_tarski(X120,sK1)))) ),
    inference(forward_demodulation,[],[f8180,f133])).

fof(f8180,plain,(
    ! [X120] : k5_xboole_0(sK1,k1_xboole_0) = k7_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(X120,k1_setfam_1(k2_tarski(X120,sK1)))) ),
    inference(superposition,[],[f487,f8093])).

fof(f8093,plain,(
    ! [X0,X1] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))) ),
    inference(duplicate_literal_removal,[],[f8069])).

fof(f8069,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))))
      | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))) ) ),
    inference(resolution,[],[f2387,f2269])).

fof(f2269,plain,(
    ! [X10,X11] :
      ( r2_hidden(sK2(X10,X11,k1_xboole_0),X11)
      | k1_xboole_0 = k1_setfam_1(k2_tarski(X10,X11)) ) ),
    inference(resolution,[],[f2260,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f86,f72])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f48,f49])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f2260,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(superposition,[],[f2244,f95])).

fof(f2244,plain,(
    ! [X14,X10,X13] : ~ r2_hidden(X10,k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(k5_xboole_0(sK1,sK1),X13)),X14))) ),
    inference(condensation,[],[f2234])).

fof(f2234,plain,(
    ! [X14,X12,X10,X13,X11] :
      ( ~ r2_hidden(X10,k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(k5_xboole_0(sK1,sK1),X11)),X12)))
      | ~ r2_hidden(X10,k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(k5_xboole_0(sK1,sK1),X13)),X14))) ) ),
    inference(resolution,[],[f871,f115])).

fof(f115,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(equality_resolution,[],[f106])).

fof(f106,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f82,f72])).

fof(f82,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f871,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ r2_hidden(X8,k1_setfam_1(k2_tarski(k5_xboole_0(sK1,sK1),X11)))
      | ~ r2_hidden(X8,k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(k5_xboole_0(sK1,sK1),X9)),X10))) ) ),
    inference(resolution,[],[f852,f115])).

fof(f852,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(sK1,sK1))
      | ~ r2_hidden(X0,k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(k5_xboole_0(sK1,sK1),X1)),X2))) ) ),
    inference(superposition,[],[f549,f147])).

fof(f147,plain,(
    ! [X2] : k1_setfam_1(k2_tarski(X2,X2)) = X2 ),
    inference(resolution,[],[f98,f138])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f74,f72])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f549,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ r2_hidden(X8,k5_xboole_0(X9,k1_setfam_1(k2_tarski(X9,sK1))))
      | ~ r2_hidden(X8,k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(k5_xboole_0(sK1,sK1),X10)),X11))) ) ),
    inference(resolution,[],[f545,f115])).

fof(f545,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(X6,k1_setfam_1(k2_tarski(k5_xboole_0(sK1,sK1),X8)))
      | ~ r2_hidden(X6,k5_xboole_0(X7,k1_setfam_1(k2_tarski(X7,sK1)))) ) ),
    inference(resolution,[],[f541,f115])).

fof(f541,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k5_xboole_0(sK1,sK1))
      | ~ r2_hidden(X4,k5_xboole_0(X5,k1_setfam_1(k2_tarski(X5,sK1)))) ) ),
    inference(superposition,[],[f523,f492])).

fof(f492,plain,(
    k5_xboole_0(sK1,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) ),
    inference(superposition,[],[f487,f157])).

fof(f157,plain,(
    sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) ),
    inference(resolution,[],[f146,f58])).

fof(f58,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f42,f41])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | ~ v3_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | ~ v3_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | ~ v3_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | v3_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | ~ v3_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | v3_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

fof(f146,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ) ),
    inference(resolution,[],[f98,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f523,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_hidden(X2,k7_subset_1(u1_struct_0(sK0),sK1,X1))
      | ~ r2_hidden(X2,k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,sK1)))) ) ),
    inference(superposition,[],[f183,f506])).

fof(f506,plain,(
    ! [X1] : k7_subset_1(u1_struct_0(sK0),sK1,X1) = k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X1))) ),
    inference(forward_demodulation,[],[f505,f71])).

fof(f71,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f505,plain,(
    ! [X1] : k7_subset_1(u1_struct_0(sK0),sK1,X1) = k1_setfam_1(k2_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X1),sK1)) ),
    inference(resolution,[],[f496,f98])).

fof(f496,plain,(
    ! [X0] : r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),sK1) ),
    inference(superposition,[],[f97,f487])).

fof(f183,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X3)))
      | ~ r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) ) ),
    inference(resolution,[],[f117,f115])).

fof(f117,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) ) ),
    inference(equality_resolution,[],[f111])).

fof(f111,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f89,f94])).

fof(f89,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f53,f54])).

fof(f54,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f2387,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(sK2(X4,X5,k1_xboole_0),k5_xboole_0(X6,k1_setfam_1(k2_tarski(X6,X4))))
      | k1_xboole_0 = k1_setfam_1(k2_tarski(X4,X5)) ) ),
    inference(resolution,[],[f2268,f117])).

fof(f2268,plain,(
    ! [X8,X9] :
      ( r2_hidden(sK2(X8,X9,k1_xboole_0),X8)
      | k1_xboole_0 = k1_setfam_1(k2_tarski(X8,X9)) ) ),
    inference(resolution,[],[f2260,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X0)
      | k1_setfam_1(k2_tarski(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f85,f72])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f487,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) ),
    inference(resolution,[],[f100,f58])).

fof(f1057,plain,(
    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f1056,f58])).

fof(f1056,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) ) ),
    inference(resolution,[],[f63,f57])).

fof(f57,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f14047,plain,(
    spl4_139 ),
    inference(avatar_contradiction_clause,[],[f14046])).

fof(f14046,plain,
    ( $false
    | spl4_139 ),
    inference(subsumption_resolution,[],[f14045,f57])).

fof(f14045,plain,
    ( ~ l1_pre_topc(sK0)
    | spl4_139 ),
    inference(subsumption_resolution,[],[f14043,f58])).

fof(f14043,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl4_139 ),
    inference(resolution,[],[f14037,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f14037,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_139 ),
    inference(avatar_component_clause,[],[f14035])).

fof(f4984,plain,
    ( spl4_1
    | ~ spl4_75 ),
    inference(avatar_contradiction_clause,[],[f4983])).

fof(f4983,plain,
    ( $false
    | spl4_1
    | ~ spl4_75 ),
    inference(subsumption_resolution,[],[f4982,f56])).

fof(f56,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f4982,plain,
    ( ~ v2_pre_topc(sK0)
    | spl4_1
    | ~ spl4_75 ),
    inference(subsumption_resolution,[],[f4981,f57])).

fof(f4981,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl4_1
    | ~ spl4_75 ),
    inference(subsumption_resolution,[],[f4980,f58])).

fof(f4980,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl4_1
    | ~ spl4_75 ),
    inference(subsumption_resolution,[],[f4977,f122])).

fof(f122,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl4_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f4977,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_75 ),
    inference(superposition,[],[f77,f4775])).

fof(f4775,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl4_75 ),
    inference(avatar_component_clause,[],[f4773])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f4913,plain,
    ( ~ spl4_72
    | spl4_75 ),
    inference(avatar_contradiction_clause,[],[f4912])).

fof(f4912,plain,
    ( $false
    | ~ spl4_72
    | spl4_75 ),
    inference(subsumption_resolution,[],[f4911,f4774])).

fof(f4911,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl4_72 ),
    inference(forward_demodulation,[],[f4910,f201])).

fof(f201,plain,(
    sK1 = k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f200,f58])).

fof(f200,plain,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f76,f199])).

fof(f199,plain,(
    k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(forward_demodulation,[],[f198,f157])).

fof(f198,plain,(
    k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f195,f71])).

fof(f195,plain,(
    k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1))) ),
    inference(resolution,[],[f99,f58])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f75,f94])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f76,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f4910,plain,
    ( k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)) = k1_tops_1(sK0,sK1)
    | ~ spl4_72 ),
    inference(forward_demodulation,[],[f4909,f4559])).

fof(f4559,plain,
    ( k5_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl4_72 ),
    inference(forward_demodulation,[],[f4514,f199])).

fof(f4514,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_72 ),
    inference(avatar_component_clause,[],[f4512])).

fof(f4512,plain,
    ( spl4_72
  <=> k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).

fof(f4909,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1))) ),
    inference(forward_demodulation,[],[f4465,f199])).

fof(f4465,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(resolution,[],[f58,f1630])).

fof(f1630,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) ) ),
    inference(resolution,[],[f65,f57])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

fof(f4809,plain,
    ( spl4_2
    | ~ spl4_75 ),
    inference(avatar_contradiction_clause,[],[f4808])).

fof(f4808,plain,
    ( $false
    | spl4_2
    | ~ spl4_75 ),
    inference(subsumption_resolution,[],[f4807,f57])).

fof(f4807,plain,
    ( ~ l1_pre_topc(sK0)
    | spl4_2
    | ~ spl4_75 ),
    inference(subsumption_resolution,[],[f4806,f58])).

fof(f4806,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl4_2
    | ~ spl4_75 ),
    inference(subsumption_resolution,[],[f4797,f126])).

fof(f126,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f124])).

fof(f4797,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_75 ),
    inference(superposition,[],[f64,f4775])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f4558,plain,(
    spl4_71 ),
    inference(avatar_contradiction_clause,[],[f4557])).

fof(f4557,plain,
    ( $false
    | spl4_71 ),
    inference(subsumption_resolution,[],[f4556,f159])).

fof(f159,plain,(
    r1_tarski(k5_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    inference(superposition,[],[f134,f157])).

fof(f134,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))),X0) ),
    inference(superposition,[],[f97,f71])).

fof(f4556,plain,
    ( ~ r1_tarski(k5_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | spl4_71 ),
    inference(resolution,[],[f4555,f80])).

fof(f4555,plain,
    ( ~ m1_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_71 ),
    inference(forward_demodulation,[],[f4510,f199])).

fof(f4510,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_71 ),
    inference(avatar_component_clause,[],[f4508])).

fof(f4508,plain,
    ( spl4_71
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_71])])).

fof(f4515,plain,
    ( ~ spl4_71
    | spl4_72
    | ~ spl4_69 ),
    inference(avatar_split_clause,[],[f4506,f4454,f4512,f4508])).

fof(f4454,plain,
    ( spl4_69
  <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).

fof(f4506,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_69 ),
    inference(subsumption_resolution,[],[f4505,f57])).

fof(f4505,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_69 ),
    inference(resolution,[],[f4456,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f4456,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl4_69 ),
    inference(avatar_component_clause,[],[f4454])).

fof(f4475,plain,(
    spl4_70 ),
    inference(avatar_contradiction_clause,[],[f4474])).

fof(f4474,plain,
    ( $false
    | spl4_70 ),
    inference(subsumption_resolution,[],[f4460,f58])).

fof(f4460,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_70 ),
    inference(avatar_component_clause,[],[f4458])).

fof(f4458,plain,
    ( spl4_70
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).

fof(f4461,plain,
    ( spl4_69
    | ~ spl4_70
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f4452,f120,f4458,f4454])).

fof(f4452,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl4_1 ),
    inference(resolution,[],[f121,f639])).

fof(f639,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) ) ),
    inference(resolution,[],[f68,f57])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).

fof(f121,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f120])).

fof(f128,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f59,f124,f120])).

fof(f59,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f127,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f60,f124,f120])).

fof(f60,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:31:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.54  % (8121)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (8136)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (8120)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (8124)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.40/0.55  % (8128)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.40/0.55  % (8132)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.40/0.55  % (8129)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.40/0.55  % (8129)Refutation not found, incomplete strategy% (8129)------------------------------
% 1.40/0.55  % (8129)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (8129)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (8129)Memory used [KB]: 6140
% 1.40/0.55  % (8129)Time elapsed: 0.003 s
% 1.40/0.55  % (8129)------------------------------
% 1.40/0.55  % (8129)------------------------------
% 1.40/0.55  % (8135)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.40/0.55  % (8116)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.40/0.55  % (8139)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.40/0.55  % (8114)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.40/0.55  % (8137)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.40/0.56  % (8123)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.40/0.56  % (8127)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.40/0.56  % (8131)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.40/0.56  % (8130)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.40/0.56  % (8126)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.40/0.56  % (8119)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.40/0.56  % (8136)Refutation not found, incomplete strategy% (8136)------------------------------
% 1.40/0.56  % (8136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.56  % (8136)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.56  
% 1.40/0.56  % (8136)Memory used [KB]: 10746
% 1.40/0.56  % (8136)Time elapsed: 0.132 s
% 1.40/0.56  % (8136)------------------------------
% 1.40/0.56  % (8136)------------------------------
% 1.40/0.56  % (8141)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.52/0.57  % (8131)Refutation not found, incomplete strategy% (8131)------------------------------
% 1.52/0.57  % (8131)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.57  % (8118)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.52/0.57  % (8131)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.57  
% 1.52/0.57  % (8131)Memory used [KB]: 10618
% 1.52/0.57  % (8131)Time elapsed: 0.109 s
% 1.52/0.57  % (8131)------------------------------
% 1.52/0.57  % (8131)------------------------------
% 1.52/0.57  % (8115)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.52/0.57  % (8122)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.52/0.57  % (8125)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.52/0.57  % (8143)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.52/0.57  % (8138)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.52/0.57  % (8142)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.52/0.57  % (8140)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.52/0.57  % (8117)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.52/0.57  % (8133)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.52/0.58  % (8134)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 2.17/0.67  % (8154)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.17/0.69  % (8146)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.17/0.70  % (8152)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 3.47/0.84  % (8119)Time limit reached!
% 3.47/0.84  % (8119)------------------------------
% 3.47/0.84  % (8119)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.47/0.84  % (8119)Termination reason: Time limit
% 3.47/0.84  
% 3.47/0.84  % (8119)Memory used [KB]: 8443
% 3.47/0.84  % (8119)Time elapsed: 0.419 s
% 3.47/0.84  % (8119)------------------------------
% 3.47/0.84  % (8119)------------------------------
% 3.68/0.92  % (8126)Time limit reached!
% 3.68/0.92  % (8126)------------------------------
% 3.68/0.92  % (8126)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.09/0.93  % (8126)Termination reason: Time limit
% 4.09/0.93  
% 4.09/0.93  % (8126)Memory used [KB]: 8187
% 4.09/0.93  % (8126)Time elapsed: 0.504 s
% 4.09/0.93  % (8126)------------------------------
% 4.09/0.93  % (8126)------------------------------
% 4.09/0.94  % (8114)Time limit reached!
% 4.09/0.94  % (8114)------------------------------
% 4.09/0.94  % (8114)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.09/0.94  % (8114)Termination reason: Time limit
% 4.09/0.94  % (8114)Termination phase: Saturation
% 4.09/0.94  
% 4.09/0.94  % (8114)Memory used [KB]: 4221
% 4.09/0.94  % (8114)Time elapsed: 0.500 s
% 4.09/0.94  % (8114)------------------------------
% 4.09/0.94  % (8114)------------------------------
% 4.09/0.95  % (8115)Time limit reached!
% 4.09/0.95  % (8115)------------------------------
% 4.09/0.95  % (8115)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.09/0.95  % (8115)Termination reason: Time limit
% 4.09/0.95  % (8115)Termination phase: Saturation
% 4.09/0.95  
% 4.09/0.95  % (8115)Memory used [KB]: 6780
% 4.09/0.95  % (8115)Time elapsed: 0.500 s
% 4.09/0.95  % (8115)------------------------------
% 4.09/0.95  % (8115)------------------------------
% 4.31/0.97  % (8291)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 4.31/0.98  % (8124)Time limit reached!
% 4.31/0.98  % (8124)------------------------------
% 4.31/0.98  % (8124)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.31/0.98  % (8124)Termination reason: Time limit
% 4.31/0.98  
% 4.31/0.98  % (8124)Memory used [KB]: 12792
% 4.31/0.98  % (8124)Time elapsed: 0.532 s
% 4.31/0.98  % (8124)------------------------------
% 4.31/0.98  % (8124)------------------------------
% 4.31/1.03  % (8121)Time limit reached!
% 4.31/1.03  % (8121)------------------------------
% 4.31/1.03  % (8121)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.31/1.03  % (8121)Termination reason: Time limit
% 4.31/1.03  
% 4.31/1.03  % (8121)Memory used [KB]: 11257
% 4.31/1.03  % (8121)Time elapsed: 0.603 s
% 4.31/1.03  % (8121)------------------------------
% 4.31/1.03  % (8121)------------------------------
% 4.76/1.03  % (8130)Time limit reached!
% 4.76/1.03  % (8130)------------------------------
% 4.76/1.03  % (8130)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.76/1.03  % (8130)Termination reason: Time limit
% 4.76/1.03  % (8130)Termination phase: Saturation
% 4.76/1.03  
% 4.76/1.03  % (8130)Memory used [KB]: 18166
% 4.76/1.03  % (8130)Time elapsed: 0.600 s
% 4.76/1.03  % (8130)------------------------------
% 4.76/1.03  % (8130)------------------------------
% 4.76/1.04  % (8142)Time limit reached!
% 4.76/1.04  % (8142)------------------------------
% 4.76/1.04  % (8142)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.76/1.04  % (8142)Termination reason: Time limit
% 4.76/1.04  
% 4.76/1.04  % (8142)Memory used [KB]: 8827
% 4.76/1.04  % (8142)Time elapsed: 0.614 s
% 4.76/1.04  % (8142)------------------------------
% 4.76/1.04  % (8142)------------------------------
% 4.76/1.04  % (8315)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 4.76/1.06  % (8310)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 5.51/1.08  % (8319)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 5.51/1.08  % (8327)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 5.51/1.14  % (8339)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 6.07/1.16  % (8338)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 6.07/1.17  % (8340)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 6.72/1.23  % (8135)Time limit reached!
% 6.72/1.23  % (8135)------------------------------
% 6.72/1.23  % (8135)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.72/1.23  % (8135)Termination reason: Time limit
% 6.72/1.23  % (8135)Termination phase: Saturation
% 6.72/1.23  
% 6.72/1.23  % (8135)Memory used [KB]: 5756
% 6.72/1.23  % (8135)Time elapsed: 0.813 s
% 6.72/1.23  % (8135)------------------------------
% 6.72/1.23  % (8135)------------------------------
% 6.91/1.29  % (8291)Time limit reached!
% 6.91/1.29  % (8291)------------------------------
% 6.91/1.29  % (8291)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.91/1.31  % (8291)Termination reason: Time limit
% 6.91/1.31  
% 6.91/1.31  % (8291)Memory used [KB]: 6780
% 6.91/1.31  % (8291)Time elapsed: 0.425 s
% 6.91/1.31  % (8291)------------------------------
% 6.91/1.31  % (8291)------------------------------
% 7.43/1.34  % (8383)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 7.43/1.36  % (8310)Time limit reached!
% 7.43/1.36  % (8310)------------------------------
% 7.43/1.36  % (8310)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.43/1.36  % (8310)Termination reason: Time limit
% 7.43/1.36  
% 7.43/1.36  % (8310)Memory used [KB]: 13304
% 7.43/1.36  % (8310)Time elapsed: 0.411 s
% 7.43/1.36  % (8310)------------------------------
% 7.43/1.36  % (8310)------------------------------
% 7.82/1.42  % (8384)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 7.82/1.43  % (8116)Time limit reached!
% 7.82/1.43  % (8116)------------------------------
% 7.82/1.43  % (8116)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.82/1.44  % (8116)Termination reason: Time limit
% 7.82/1.44  
% 7.82/1.44  % (8116)Memory used [KB]: 21875
% 7.82/1.44  % (8116)Time elapsed: 1.009 s
% 7.82/1.44  % (8116)------------------------------
% 7.82/1.44  % (8116)------------------------------
% 8.56/1.50  % (8385)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 9.09/1.55  % (8386)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 9.09/1.63  % (8140)Time limit reached!
% 9.09/1.63  % (8140)------------------------------
% 9.09/1.63  % (8140)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.09/1.63  % (8140)Termination reason: Time limit
% 9.09/1.63  % (8140)Termination phase: Saturation
% 9.09/1.63  
% 9.09/1.63  % (8140)Memory used [KB]: 15863
% 9.09/1.63  % (8140)Time elapsed: 1.205 s
% 9.09/1.63  % (8140)------------------------------
% 9.09/1.63  % (8140)------------------------------
% 10.31/1.74  % (8138)Time limit reached!
% 10.31/1.74  % (8138)------------------------------
% 10.31/1.74  % (8138)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.31/1.74  % (8138)Termination reason: Time limit
% 10.31/1.74  
% 10.31/1.74  % (8138)Memory used [KB]: 20596
% 10.31/1.74  % (8138)Time elapsed: 1.315 s
% 10.31/1.74  % (8138)------------------------------
% 10.31/1.74  % (8138)------------------------------
% 10.31/1.75  % (8387)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 11.54/1.86  % (8384)Time limit reached!
% 11.54/1.86  % (8384)------------------------------
% 11.54/1.86  % (8384)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.54/1.86  % (8384)Termination reason: Time limit
% 11.54/1.86  
% 11.54/1.86  % (8384)Memory used [KB]: 2174
% 11.54/1.86  % (8384)Time elapsed: 0.524 s
% 11.54/1.86  % (8384)------------------------------
% 11.54/1.86  % (8384)------------------------------
% 11.54/1.87  % (8388)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 12.11/1.94  % (8141)Time limit reached!
% 12.11/1.94  % (8141)------------------------------
% 12.11/1.94  % (8141)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.11/1.94  % (8141)Termination reason: Time limit
% 12.11/1.94  % (8141)Termination phase: Saturation
% 12.11/1.94  
% 12.11/1.94  % (8141)Memory used [KB]: 13560
% 12.11/1.94  % (8141)Time elapsed: 1.500 s
% 12.11/1.94  % (8141)------------------------------
% 12.11/1.94  % (8141)------------------------------
% 12.11/1.95  % (8118)Time limit reached!
% 12.11/1.95  % (8118)------------------------------
% 12.11/1.95  % (8118)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.11/1.95  % (8118)Termination reason: Time limit
% 12.11/1.95  % (8118)Termination phase: Saturation
% 12.11/1.95  
% 12.11/1.95  % (8118)Memory used [KB]: 14583
% 12.11/1.95  % (8118)Time elapsed: 1.500 s
% 12.11/1.95  % (8118)------------------------------
% 12.11/1.95  % (8118)------------------------------
% 12.56/1.98  % (8389)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 12.56/2.05  % (8125)Time limit reached!
% 12.56/2.05  % (8125)------------------------------
% 12.56/2.05  % (8125)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.56/2.05  % (8125)Termination reason: Time limit
% 12.56/2.05  
% 12.56/2.05  % (8125)Memory used [KB]: 15735
% 12.56/2.05  % (8125)Time elapsed: 1.621 s
% 12.56/2.05  % (8125)------------------------------
% 12.56/2.05  % (8125)------------------------------
% 13.13/2.07  % (8390)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 13.25/2.09  % (8391)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 14.07/2.18  % (8388)Time limit reached!
% 14.07/2.18  % (8388)------------------------------
% 14.07/2.18  % (8388)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.07/2.18  % (8388)Termination reason: Time limit
% 14.07/2.18  % (8388)Termination phase: Saturation
% 14.07/2.18  
% 14.07/2.18  % (8388)Memory used [KB]: 4221
% 14.07/2.18  % (8388)Time elapsed: 0.400 s
% 14.07/2.18  % (8388)------------------------------
% 14.07/2.18  % (8388)------------------------------
% 14.07/2.19  % (8392)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 14.07/2.20  % (8319)Time limit reached!
% 14.07/2.20  % (8319)------------------------------
% 14.07/2.20  % (8319)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.07/2.20  % (8319)Termination reason: Time limit
% 14.07/2.20  
% 14.07/2.20  % (8319)Memory used [KB]: 11513
% 14.07/2.20  % (8319)Time elapsed: 1.229 s
% 14.07/2.20  % (8319)------------------------------
% 14.07/2.20  % (8319)------------------------------
% 14.72/2.24  % (8128)Time limit reached!
% 14.72/2.24  % (8128)------------------------------
% 14.72/2.24  % (8128)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.72/2.24  % (8128)Termination reason: Time limit
% 14.72/2.24  % (8128)Termination phase: Saturation
% 14.72/2.24  
% 14.72/2.24  % (8128)Memory used [KB]: 5117
% 14.72/2.24  % (8128)Time elapsed: 1.800 s
% 14.72/2.24  % (8128)------------------------------
% 14.72/2.24  % (8128)------------------------------
% 15.14/2.31  % (8393)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 15.14/2.31  % (8154)Time limit reached!
% 15.14/2.31  % (8154)------------------------------
% 15.14/2.31  % (8154)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.14/2.31  % (8154)Termination reason: Time limit
% 15.14/2.31  
% 15.14/2.31  % (8154)Memory used [KB]: 16758
% 15.14/2.31  % (8154)Time elapsed: 1.720 s
% 15.14/2.31  % (8154)------------------------------
% 15.14/2.31  % (8154)------------------------------
% 15.14/2.33  % (8394)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 15.72/2.37  % (8395)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 15.72/2.39  % (8391)Time limit reached!
% 15.72/2.39  % (8391)------------------------------
% 15.72/2.39  % (8391)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.72/2.40  % (8391)Termination reason: Time limit
% 15.72/2.40  % (8391)Termination phase: Saturation
% 15.72/2.40  
% 15.72/2.40  % (8391)Memory used [KB]: 2686
% 15.72/2.40  % (8391)Time elapsed: 0.400 s
% 15.72/2.40  % (8391)------------------------------
% 15.72/2.40  % (8391)------------------------------
% 15.99/2.42  % (8132)Time limit reached!
% 15.99/2.42  % (8132)------------------------------
% 15.99/2.42  % (8132)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.99/2.42  % (8132)Termination reason: Time limit
% 15.99/2.42  % (8132)Termination phase: Saturation
% 15.99/2.42  
% 15.99/2.42  % (8132)Memory used [KB]: 13944
% 15.99/2.42  % (8132)Time elapsed: 2.002 s
% 15.99/2.42  % (8132)------------------------------
% 15.99/2.42  % (8132)------------------------------
% 15.99/2.44  % (8396)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 16.21/2.49  % (8120)Time limit reached!
% 16.21/2.49  % (8120)------------------------------
% 16.21/2.49  % (8120)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.21/2.49  % (8120)Termination reason: Time limit
% 16.21/2.49  
% 16.21/2.49  % (8120)Memory used [KB]: 23539
% 16.21/2.49  % (8120)Time elapsed: 2.034 s
% 16.21/2.49  % (8120)------------------------------
% 16.21/2.49  % (8120)------------------------------
% 16.21/2.51  % (8398)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 16.80/2.54  % (8397)dis+3_24_av=off:bd=off:bs=unit_only:fsr=off:fde=unused:gs=on:irw=on:lma=on:nm=0:nwc=1.1:sos=on:uhcvi=on_180 on theBenchmark
% 17.13/2.61  % (8399)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_34 on theBenchmark
% 18.81/2.77  % (8338)Time limit reached!
% 18.81/2.77  % (8338)------------------------------
% 18.81/2.77  % (8338)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 18.81/2.77  % (8396)Time limit reached!
% 18.81/2.77  % (8396)------------------------------
% 18.81/2.77  % (8396)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 18.81/2.78  % (8396)Termination reason: Time limit
% 18.81/2.78  
% 18.81/2.78  % (8396)Memory used [KB]: 10746
% 18.81/2.78  % (8396)Time elapsed: 0.423 s
% 18.81/2.78  % (8396)------------------------------
% 18.81/2.78  % (8396)------------------------------
% 18.81/2.79  % (8338)Termination reason: Time limit
% 18.81/2.79  
% 18.81/2.79  % (8338)Memory used [KB]: 13304
% 18.81/2.79  % (8338)Time elapsed: 1.718 s
% 18.81/2.79  % (8338)------------------------------
% 18.81/2.79  % (8338)------------------------------
% 19.56/2.87  % (8387)Time limit reached!
% 19.56/2.87  % (8387)------------------------------
% 19.56/2.87  % (8387)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 19.56/2.87  % (8387)Termination reason: Time limit
% 19.56/2.87  
% 19.56/2.87  % (8387)Memory used [KB]: 14072
% 19.56/2.87  % (8387)Time elapsed: 1.228 s
% 19.56/2.87  % (8387)------------------------------
% 19.56/2.87  % (8387)------------------------------
% 19.56/2.87  % (8398)Time limit reached!
% 19.56/2.87  % (8398)------------------------------
% 19.56/2.87  % (8398)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 19.56/2.87  % (8398)Termination reason: Time limit
% 19.56/2.87  
% 19.56/2.87  % (8398)Memory used [KB]: 9594
% 19.56/2.87  % (8398)Time elapsed: 0.423 s
% 19.56/2.87  % (8398)------------------------------
% 19.56/2.87  % (8398)------------------------------
% 21.26/3.05  % (8133)Time limit reached!
% 21.26/3.05  % (8133)------------------------------
% 21.26/3.05  % (8133)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 21.26/3.05  % (8133)Termination reason: Time limit
% 21.26/3.05  
% 21.26/3.05  % (8133)Memory used [KB]: 24306
% 21.26/3.05  % (8133)Time elapsed: 2.637 s
% 21.26/3.05  % (8133)------------------------------
% 21.26/3.05  % (8133)------------------------------
% 21.26/3.13  % (8117)Refutation found. Thanks to Tanya!
% 21.26/3.13  % SZS status Theorem for theBenchmark
% 21.26/3.13  % SZS output start Proof for theBenchmark
% 21.26/3.13  fof(f34182,plain,(
% 21.26/3.13    $false),
% 21.26/3.13    inference(avatar_sat_refutation,[],[f127,f128,f4461,f4475,f4515,f4558,f4809,f4913,f4984,f14047,f34181])).
% 21.26/3.14  fof(f34181,plain,(
% 21.26/3.14    ~spl4_2 | spl4_75 | ~spl4_139),
% 21.26/3.14    inference(avatar_contradiction_clause,[],[f34180])).
% 21.26/3.14  fof(f34180,plain,(
% 21.26/3.14    $false | (~spl4_2 | spl4_75 | ~spl4_139)),
% 21.26/3.14    inference(subsumption_resolution,[],[f34177,f4774])).
% 21.26/3.14  fof(f4774,plain,(
% 21.26/3.14    sK1 != k1_tops_1(sK0,sK1) | spl4_75),
% 21.26/3.14    inference(avatar_component_clause,[],[f4773])).
% 21.26/3.14  fof(f4773,plain,(
% 21.26/3.14    spl4_75 <=> sK1 = k1_tops_1(sK0,sK1)),
% 21.26/3.14    introduced(avatar_definition,[new_symbols(naming,[spl4_75])])).
% 21.26/3.14  fof(f34177,plain,(
% 21.26/3.14    sK1 = k1_tops_1(sK0,sK1) | (~spl4_2 | ~spl4_139)),
% 21.26/3.14    inference(backward_demodulation,[],[f1057,f33378])).
% 21.26/3.14  fof(f33378,plain,(
% 21.26/3.14    sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl4_2 | ~spl4_139)),
% 21.26/3.14    inference(forward_demodulation,[],[f33359,f125])).
% 21.26/3.14  fof(f125,plain,(
% 21.26/3.14    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl4_2),
% 21.26/3.14    inference(avatar_component_clause,[],[f124])).
% 21.26/3.14  fof(f124,plain,(
% 21.26/3.14    spl4_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 21.26/3.14    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 21.26/3.14  fof(f33359,plain,(
% 21.26/3.14    sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)) | ~spl4_139),
% 21.26/3.14    inference(superposition,[],[f22799,f24578])).
% 21.26/3.14  fof(f24578,plain,(
% 21.26/3.14    ( ! [X11] : (k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X11) = k7_subset_1(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1),X11)) ) | ~spl4_139),
% 21.26/3.14    inference(resolution,[],[f22738,f14036])).
% 21.26/3.14  fof(f14036,plain,(
% 21.26/3.14    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_139),
% 21.26/3.14    inference(avatar_component_clause,[],[f14035])).
% 21.26/3.14  fof(f14035,plain,(
% 21.26/3.14    spl4_139 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 21.26/3.14    introduced(avatar_definition,[new_symbols(naming,[spl4_139])])).
% 21.26/3.14  fof(f22738,plain,(
% 21.26/3.14    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)) )),
% 21.26/3.14    inference(backward_demodulation,[],[f100,f4867])).
% 21.26/3.14  fof(f4867,plain,(
% 21.26/3.14    ( ! [X4,X3] : (k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,X4))) = k7_subset_1(X3,X3,X4)) )),
% 21.26/3.14    inference(resolution,[],[f488,f138])).
% 21.26/3.14  fof(f138,plain,(
% 21.26/3.14    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 21.26/3.14    inference(forward_demodulation,[],[f136,f133])).
% 21.26/3.14  fof(f133,plain,(
% 21.26/3.14    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 21.26/3.14    inference(forward_demodulation,[],[f96,f95])).
% 21.26/3.14  fof(f95,plain,(
% 21.26/3.14    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 21.26/3.14    inference(definition_unfolding,[],[f61,f72])).
% 21.26/3.14  fof(f72,plain,(
% 21.26/3.14    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 21.26/3.14    inference(cnf_transformation,[],[f12])).
% 21.26/3.14  fof(f12,axiom,(
% 21.26/3.14    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 21.26/3.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 21.26/3.14  fof(f61,plain,(
% 21.26/3.14    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 21.26/3.14    inference(cnf_transformation,[],[f5])).
% 21.26/3.14  fof(f5,axiom,(
% 21.26/3.14    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 21.26/3.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 21.26/3.14  fof(f96,plain,(
% 21.26/3.14    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0) )),
% 21.26/3.14    inference(definition_unfolding,[],[f62,f94])).
% 21.26/3.14  fof(f94,plain,(
% 21.26/3.14    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 21.26/3.14    inference(definition_unfolding,[],[f73,f72])).
% 21.26/3.14  fof(f73,plain,(
% 21.26/3.14    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 21.26/3.14    inference(cnf_transformation,[],[f3])).
% 21.26/3.14  fof(f3,axiom,(
% 21.26/3.14    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 21.26/3.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 21.26/3.14  fof(f62,plain,(
% 21.26/3.14    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 21.26/3.14    inference(cnf_transformation,[],[f7])).
% 21.26/3.14  fof(f7,axiom,(
% 21.26/3.14    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 21.26/3.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 21.26/3.14  fof(f136,plain,(
% 21.26/3.14    ( ! [X0] : (r1_tarski(k5_xboole_0(X0,k1_xboole_0),X0)) )),
% 21.26/3.14    inference(superposition,[],[f97,f95])).
% 21.26/3.14  fof(f97,plain,(
% 21.26/3.14    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) )),
% 21.26/3.14    inference(definition_unfolding,[],[f70,f94])).
% 21.26/3.14  fof(f70,plain,(
% 21.26/3.14    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 21.26/3.14    inference(cnf_transformation,[],[f6])).
% 21.26/3.14  fof(f6,axiom,(
% 21.26/3.14    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 21.26/3.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 21.26/3.14  fof(f488,plain,(
% 21.26/3.14    ( ! [X2,X3,X1] : (~r1_tarski(X2,X1) | k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))) = k7_subset_1(X1,X2,X3)) )),
% 21.26/3.14    inference(resolution,[],[f100,f80])).
% 21.26/3.14  fof(f80,plain,(
% 21.26/3.14    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 21.26/3.14    inference(cnf_transformation,[],[f45])).
% 21.26/3.14  fof(f45,plain,(
% 21.26/3.14    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 21.26/3.14    inference(nnf_transformation,[],[f13])).
% 21.26/3.14  fof(f13,axiom,(
% 21.26/3.14    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 21.26/3.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 21.26/3.14  fof(f100,plain,(
% 21.26/3.14    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) )),
% 21.26/3.14    inference(definition_unfolding,[],[f81,f94])).
% 21.26/3.14  fof(f81,plain,(
% 21.26/3.14    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 21.26/3.14    inference(cnf_transformation,[],[f38])).
% 21.26/3.14  fof(f38,plain,(
% 21.26/3.14    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 21.26/3.14    inference(ennf_transformation,[],[f11])).
% 21.26/3.14  fof(f11,axiom,(
% 21.26/3.14    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 21.26/3.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 21.26/3.14  fof(f22799,plain,(
% 21.26/3.14    ( ! [X120] : (sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(X120,X120,sK1))) )),
% 21.26/3.14    inference(backward_demodulation,[],[f8233,f4867])).
% 21.26/3.14  fof(f8233,plain,(
% 21.26/3.14    ( ! [X120] : (sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(X120,k1_setfam_1(k2_tarski(X120,sK1))))) )),
% 21.26/3.14    inference(forward_demodulation,[],[f8180,f133])).
% 21.26/3.14  fof(f8180,plain,(
% 21.26/3.14    ( ! [X120] : (k5_xboole_0(sK1,k1_xboole_0) = k7_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(X120,k1_setfam_1(k2_tarski(X120,sK1))))) )),
% 21.26/3.14    inference(superposition,[],[f487,f8093])).
% 21.26/3.14  fof(f8093,plain,(
% 21.26/3.14    ( ! [X0,X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))))) )),
% 21.26/3.14    inference(duplicate_literal_removal,[],[f8069])).
% 21.26/3.14  fof(f8069,plain,(
% 21.26/3.14    ( ! [X0,X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))) | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))))) )),
% 21.26/3.14    inference(resolution,[],[f2387,f2269])).
% 21.26/3.14  fof(f2269,plain,(
% 21.26/3.14    ( ! [X10,X11] : (r2_hidden(sK2(X10,X11,k1_xboole_0),X11) | k1_xboole_0 = k1_setfam_1(k2_tarski(X10,X11))) )),
% 21.26/3.14    inference(resolution,[],[f2260,f102])).
% 21.26/3.14  fof(f102,plain,(
% 21.26/3.14    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X1) | k1_setfam_1(k2_tarski(X0,X1)) = X2) )),
% 21.26/3.14    inference(definition_unfolding,[],[f86,f72])).
% 21.26/3.14  fof(f86,plain,(
% 21.26/3.14    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 21.26/3.14    inference(cnf_transformation,[],[f50])).
% 21.26/3.14  fof(f50,plain,(
% 21.26/3.14    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 21.26/3.14    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f48,f49])).
% 21.26/3.14  fof(f49,plain,(
% 21.26/3.14    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 21.26/3.14    introduced(choice_axiom,[])).
% 21.26/3.14  fof(f48,plain,(
% 21.26/3.14    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 21.26/3.14    inference(rectify,[],[f47])).
% 21.26/3.14  fof(f47,plain,(
% 21.26/3.14    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 21.26/3.14    inference(flattening,[],[f46])).
% 21.26/3.14  fof(f46,plain,(
% 21.26/3.14    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 21.26/3.14    inference(nnf_transformation,[],[f1])).
% 21.26/3.14  fof(f1,axiom,(
% 21.26/3.14    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 21.26/3.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 21.26/3.14  fof(f2260,plain,(
% 21.26/3.14    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 21.26/3.14    inference(superposition,[],[f2244,f95])).
% 21.26/3.14  fof(f2244,plain,(
% 21.26/3.14    ( ! [X14,X10,X13] : (~r2_hidden(X10,k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(k5_xboole_0(sK1,sK1),X13)),X14)))) )),
% 21.26/3.14    inference(condensation,[],[f2234])).
% 21.26/3.14  fof(f2234,plain,(
% 21.26/3.14    ( ! [X14,X12,X10,X13,X11] : (~r2_hidden(X10,k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(k5_xboole_0(sK1,sK1),X11)),X12))) | ~r2_hidden(X10,k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(k5_xboole_0(sK1,sK1),X13)),X14)))) )),
% 21.26/3.14    inference(resolution,[],[f871,f115])).
% 21.26/3.14  fof(f115,plain,(
% 21.26/3.14    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 21.26/3.14    inference(equality_resolution,[],[f106])).
% 21.26/3.14  fof(f106,plain,(
% 21.26/3.14    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 21.26/3.14    inference(definition_unfolding,[],[f82,f72])).
% 21.26/3.14  fof(f82,plain,(
% 21.26/3.14    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 21.26/3.14    inference(cnf_transformation,[],[f50])).
% 21.26/3.14  fof(f871,plain,(
% 21.26/3.14    ( ! [X10,X8,X11,X9] : (~r2_hidden(X8,k1_setfam_1(k2_tarski(k5_xboole_0(sK1,sK1),X11))) | ~r2_hidden(X8,k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(k5_xboole_0(sK1,sK1),X9)),X10)))) )),
% 21.26/3.14    inference(resolution,[],[f852,f115])).
% 21.26/3.14  fof(f852,plain,(
% 21.26/3.14    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(sK1,sK1)) | ~r2_hidden(X0,k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(k5_xboole_0(sK1,sK1),X1)),X2)))) )),
% 21.26/3.14    inference(superposition,[],[f549,f147])).
% 21.26/3.14  fof(f147,plain,(
% 21.26/3.14    ( ! [X2] : (k1_setfam_1(k2_tarski(X2,X2)) = X2) )),
% 21.26/3.14    inference(resolution,[],[f98,f138])).
% 21.26/3.14  fof(f98,plain,(
% 21.26/3.14    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0) )),
% 21.26/3.14    inference(definition_unfolding,[],[f74,f72])).
% 21.26/3.14  fof(f74,plain,(
% 21.26/3.14    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 21.26/3.14    inference(cnf_transformation,[],[f31])).
% 21.26/3.14  fof(f31,plain,(
% 21.26/3.14    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 21.26/3.14    inference(ennf_transformation,[],[f4])).
% 21.26/3.14  fof(f4,axiom,(
% 21.26/3.14    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 21.26/3.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 21.26/3.14  fof(f549,plain,(
% 21.26/3.14    ( ! [X10,X8,X11,X9] : (~r2_hidden(X8,k5_xboole_0(X9,k1_setfam_1(k2_tarski(X9,sK1)))) | ~r2_hidden(X8,k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(k5_xboole_0(sK1,sK1),X10)),X11)))) )),
% 21.26/3.14    inference(resolution,[],[f545,f115])).
% 21.26/3.14  fof(f545,plain,(
% 21.26/3.14    ( ! [X6,X8,X7] : (~r2_hidden(X6,k1_setfam_1(k2_tarski(k5_xboole_0(sK1,sK1),X8))) | ~r2_hidden(X6,k5_xboole_0(X7,k1_setfam_1(k2_tarski(X7,sK1))))) )),
% 21.26/3.14    inference(resolution,[],[f541,f115])).
% 21.26/3.14  fof(f541,plain,(
% 21.26/3.14    ( ! [X4,X5] : (~r2_hidden(X4,k5_xboole_0(sK1,sK1)) | ~r2_hidden(X4,k5_xboole_0(X5,k1_setfam_1(k2_tarski(X5,sK1))))) )),
% 21.26/3.14    inference(superposition,[],[f523,f492])).
% 21.26/3.14  fof(f492,plain,(
% 21.26/3.14    k5_xboole_0(sK1,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))),
% 21.26/3.14    inference(superposition,[],[f487,f157])).
% 21.26/3.14  fof(f157,plain,(
% 21.26/3.14    sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))),
% 21.26/3.14    inference(resolution,[],[f146,f58])).
% 21.26/3.14  fof(f58,plain,(
% 21.26/3.14    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 21.26/3.14    inference(cnf_transformation,[],[f43])).
% 21.26/3.14  fof(f43,plain,(
% 21.26/3.14    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 21.26/3.14    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f42,f41])).
% 21.26/3.14  fof(f41,plain,(
% 21.26/3.14    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 21.26/3.14    introduced(choice_axiom,[])).
% 21.26/3.14  fof(f42,plain,(
% 21.26/3.14    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 21.26/3.14    introduced(choice_axiom,[])).
% 21.26/3.14  fof(f40,plain,(
% 21.26/3.14    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 21.26/3.14    inference(flattening,[],[f39])).
% 21.26/3.14  fof(f39,plain,(
% 21.26/3.14    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 21.26/3.14    inference(nnf_transformation,[],[f24])).
% 21.26/3.14  fof(f24,plain,(
% 21.26/3.14    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 21.26/3.14    inference(flattening,[],[f23])).
% 21.26/3.14  fof(f23,plain,(
% 21.26/3.14    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 21.26/3.14    inference(ennf_transformation,[],[f22])).
% 21.26/3.14  fof(f22,negated_conjecture,(
% 21.26/3.14    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 21.26/3.14    inference(negated_conjecture,[],[f21])).
% 21.26/3.14  fof(f21,conjecture,(
% 21.26/3.14    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 21.26/3.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).
% 21.26/3.14  fof(f146,plain,(
% 21.26/3.14    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | k1_setfam_1(k2_tarski(X0,X1)) = X0) )),
% 21.26/3.14    inference(resolution,[],[f98,f79])).
% 21.26/3.14  fof(f79,plain,(
% 21.26/3.14    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 21.26/3.14    inference(cnf_transformation,[],[f45])).
% 21.26/3.14  fof(f523,plain,(
% 21.26/3.14    ( ! [X2,X3,X1] : (~r2_hidden(X2,k7_subset_1(u1_struct_0(sK0),sK1,X1)) | ~r2_hidden(X2,k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,sK1))))) )),
% 21.26/3.14    inference(superposition,[],[f183,f506])).
% 21.26/3.14  fof(f506,plain,(
% 21.26/3.14    ( ! [X1] : (k7_subset_1(u1_struct_0(sK0),sK1,X1) = k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X1)))) )),
% 21.26/3.14    inference(forward_demodulation,[],[f505,f71])).
% 21.26/3.14  fof(f71,plain,(
% 21.26/3.14    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 21.26/3.14    inference(cnf_transformation,[],[f8])).
% 21.26/3.14  fof(f8,axiom,(
% 21.26/3.14    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 21.26/3.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 21.26/3.14  fof(f505,plain,(
% 21.26/3.14    ( ! [X1] : (k7_subset_1(u1_struct_0(sK0),sK1,X1) = k1_setfam_1(k2_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X1),sK1))) )),
% 21.26/3.14    inference(resolution,[],[f496,f98])).
% 21.26/3.14  fof(f496,plain,(
% 21.26/3.14    ( ! [X0] : (r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),sK1)) )),
% 21.26/3.14    inference(superposition,[],[f97,f487])).
% 21.26/3.14  fof(f183,plain,(
% 21.26/3.14    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X3))) | ~r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))) )),
% 21.26/3.14    inference(resolution,[],[f117,f115])).
% 21.26/3.14  fof(f117,plain,(
% 21.26/3.14    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) )),
% 21.26/3.14    inference(equality_resolution,[],[f111])).
% 21.26/3.14  fof(f111,plain,(
% 21.26/3.14    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2) )),
% 21.26/3.14    inference(definition_unfolding,[],[f89,f94])).
% 21.26/3.14  fof(f89,plain,(
% 21.26/3.14    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 21.26/3.14    inference(cnf_transformation,[],[f55])).
% 21.26/3.14  fof(f55,plain,(
% 21.26/3.14    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 21.26/3.14    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f53,f54])).
% 21.26/3.14  fof(f54,plain,(
% 21.26/3.14    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 21.26/3.14    introduced(choice_axiom,[])).
% 21.26/3.14  fof(f53,plain,(
% 21.26/3.14    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 21.26/3.14    inference(rectify,[],[f52])).
% 21.26/3.14  fof(f52,plain,(
% 21.26/3.14    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 21.26/3.14    inference(flattening,[],[f51])).
% 21.26/3.14  fof(f51,plain,(
% 21.26/3.14    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 21.26/3.14    inference(nnf_transformation,[],[f2])).
% 21.26/3.14  fof(f2,axiom,(
% 21.26/3.14    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 21.26/3.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 21.26/3.14  fof(f2387,plain,(
% 21.26/3.14    ( ! [X6,X4,X5] : (~r2_hidden(sK2(X4,X5,k1_xboole_0),k5_xboole_0(X6,k1_setfam_1(k2_tarski(X6,X4)))) | k1_xboole_0 = k1_setfam_1(k2_tarski(X4,X5))) )),
% 21.26/3.14    inference(resolution,[],[f2268,f117])).
% 21.26/3.14  fof(f2268,plain,(
% 21.26/3.14    ( ! [X8,X9] : (r2_hidden(sK2(X8,X9,k1_xboole_0),X8) | k1_xboole_0 = k1_setfam_1(k2_tarski(X8,X9))) )),
% 21.26/3.14    inference(resolution,[],[f2260,f103])).
% 21.26/3.14  fof(f103,plain,(
% 21.26/3.14    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X0) | k1_setfam_1(k2_tarski(X0,X1)) = X2) )),
% 21.26/3.14    inference(definition_unfolding,[],[f85,f72])).
% 21.26/3.14  fof(f85,plain,(
% 21.26/3.14    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 21.26/3.14    inference(cnf_transformation,[],[f50])).
% 21.26/3.14  fof(f487,plain,(
% 21.26/3.14    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0)))) )),
% 21.26/3.14    inference(resolution,[],[f100,f58])).
% 21.26/3.14  fof(f1057,plain,(
% 21.26/3.14    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 21.26/3.14    inference(resolution,[],[f1056,f58])).
% 21.26/3.14  fof(f1056,plain,(
% 21.26/3.14    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0))) )),
% 21.26/3.14    inference(resolution,[],[f63,f57])).
% 21.26/3.14  fof(f57,plain,(
% 21.26/3.14    l1_pre_topc(sK0)),
% 21.26/3.14    inference(cnf_transformation,[],[f43])).
% 21.26/3.14  fof(f63,plain,(
% 21.26/3.14    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 21.26/3.14    inference(cnf_transformation,[],[f25])).
% 21.26/3.14  fof(f25,plain,(
% 21.26/3.14    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 21.26/3.14    inference(ennf_transformation,[],[f20])).
% 21.26/3.14  fof(f20,axiom,(
% 21.26/3.14    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 21.26/3.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 21.26/3.14  fof(f14047,plain,(
% 21.26/3.14    spl4_139),
% 21.26/3.14    inference(avatar_contradiction_clause,[],[f14046])).
% 21.26/3.14  fof(f14046,plain,(
% 21.26/3.14    $false | spl4_139),
% 21.26/3.14    inference(subsumption_resolution,[],[f14045,f57])).
% 21.26/3.14  fof(f14045,plain,(
% 21.26/3.14    ~l1_pre_topc(sK0) | spl4_139),
% 21.26/3.14    inference(subsumption_resolution,[],[f14043,f58])).
% 21.26/3.14  fof(f14043,plain,(
% 21.26/3.14    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl4_139),
% 21.26/3.14    inference(resolution,[],[f14037,f78])).
% 21.26/3.14  fof(f78,plain,(
% 21.26/3.14    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 21.26/3.14    inference(cnf_transformation,[],[f37])).
% 21.26/3.14  fof(f37,plain,(
% 21.26/3.14    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 21.26/3.14    inference(flattening,[],[f36])).
% 21.26/3.14  fof(f36,plain,(
% 21.26/3.14    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 21.26/3.14    inference(ennf_transformation,[],[f14])).
% 21.26/3.14  fof(f14,axiom,(
% 21.26/3.14    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 21.26/3.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 21.26/3.14  fof(f14037,plain,(
% 21.26/3.14    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_139),
% 21.26/3.14    inference(avatar_component_clause,[],[f14035])).
% 21.26/3.14  fof(f4984,plain,(
% 21.26/3.14    spl4_1 | ~spl4_75),
% 21.26/3.14    inference(avatar_contradiction_clause,[],[f4983])).
% 21.26/3.14  fof(f4983,plain,(
% 21.26/3.14    $false | (spl4_1 | ~spl4_75)),
% 21.26/3.14    inference(subsumption_resolution,[],[f4982,f56])).
% 21.26/3.14  fof(f56,plain,(
% 21.26/3.14    v2_pre_topc(sK0)),
% 21.26/3.14    inference(cnf_transformation,[],[f43])).
% 21.26/3.14  fof(f4982,plain,(
% 21.26/3.14    ~v2_pre_topc(sK0) | (spl4_1 | ~spl4_75)),
% 21.26/3.14    inference(subsumption_resolution,[],[f4981,f57])).
% 21.26/3.14  fof(f4981,plain,(
% 21.26/3.14    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl4_1 | ~spl4_75)),
% 21.26/3.14    inference(subsumption_resolution,[],[f4980,f58])).
% 21.26/3.14  fof(f4980,plain,(
% 21.26/3.14    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl4_1 | ~spl4_75)),
% 21.26/3.14    inference(subsumption_resolution,[],[f4977,f122])).
% 21.26/3.14  fof(f122,plain,(
% 21.26/3.14    ~v3_pre_topc(sK1,sK0) | spl4_1),
% 21.26/3.14    inference(avatar_component_clause,[],[f120])).
% 21.26/3.14  fof(f120,plain,(
% 21.26/3.14    spl4_1 <=> v3_pre_topc(sK1,sK0)),
% 21.26/3.14    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 21.26/3.14  fof(f4977,plain,(
% 21.26/3.14    v3_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl4_75),
% 21.26/3.14    inference(superposition,[],[f77,f4775])).
% 21.26/3.14  fof(f4775,plain,(
% 21.26/3.14    sK1 = k1_tops_1(sK0,sK1) | ~spl4_75),
% 21.26/3.14    inference(avatar_component_clause,[],[f4773])).
% 21.26/3.14  fof(f77,plain,(
% 21.26/3.14    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 21.26/3.14    inference(cnf_transformation,[],[f35])).
% 21.26/3.14  fof(f35,plain,(
% 21.26/3.14    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 21.26/3.14    inference(flattening,[],[f34])).
% 21.26/3.14  fof(f34,plain,(
% 21.26/3.14    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 21.26/3.14    inference(ennf_transformation,[],[f17])).
% 21.26/3.14  fof(f17,axiom,(
% 21.26/3.14    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 21.26/3.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 21.26/3.14  fof(f4913,plain,(
% 21.26/3.14    ~spl4_72 | spl4_75),
% 21.26/3.14    inference(avatar_contradiction_clause,[],[f4912])).
% 21.26/3.14  fof(f4912,plain,(
% 21.26/3.14    $false | (~spl4_72 | spl4_75)),
% 21.26/3.14    inference(subsumption_resolution,[],[f4911,f4774])).
% 21.26/3.14  fof(f4911,plain,(
% 21.26/3.14    sK1 = k1_tops_1(sK0,sK1) | ~spl4_72),
% 21.26/3.14    inference(forward_demodulation,[],[f4910,f201])).
% 21.26/3.14  fof(f201,plain,(
% 21.26/3.14    sK1 = k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))),
% 21.26/3.14    inference(subsumption_resolution,[],[f200,f58])).
% 21.26/3.14  fof(f200,plain,(
% 21.26/3.14    sK1 = k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 21.26/3.14    inference(superposition,[],[f76,f199])).
% 21.26/3.14  fof(f199,plain,(
% 21.26/3.14    k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1)),
% 21.26/3.14    inference(forward_demodulation,[],[f198,f157])).
% 21.26/3.14  fof(f198,plain,(
% 21.26/3.14    k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))))),
% 21.26/3.14    inference(forward_demodulation,[],[f195,f71])).
% 21.26/3.14  fof(f195,plain,(
% 21.26/3.14    k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1)))),
% 21.26/3.14    inference(resolution,[],[f99,f58])).
% 21.26/3.14  fof(f99,plain,(
% 21.26/3.14    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 21.26/3.14    inference(definition_unfolding,[],[f75,f94])).
% 21.26/3.14  fof(f75,plain,(
% 21.26/3.14    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 21.26/3.14    inference(cnf_transformation,[],[f32])).
% 21.26/3.14  fof(f32,plain,(
% 21.26/3.14    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 21.26/3.14    inference(ennf_transformation,[],[f9])).
% 21.26/3.14  fof(f9,axiom,(
% 21.26/3.14    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 21.26/3.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 21.26/3.14  fof(f76,plain,(
% 21.26/3.14    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 21.26/3.14    inference(cnf_transformation,[],[f33])).
% 21.26/3.14  fof(f33,plain,(
% 21.26/3.14    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 21.26/3.14    inference(ennf_transformation,[],[f10])).
% 21.26/3.14  fof(f10,axiom,(
% 21.26/3.14    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 21.26/3.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 21.26/3.14  fof(f4910,plain,(
% 21.26/3.14    k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)) = k1_tops_1(sK0,sK1) | ~spl4_72),
% 21.26/3.14    inference(forward_demodulation,[],[f4909,f4559])).
% 21.26/3.14  fof(f4559,plain,(
% 21.26/3.14    k5_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)) | ~spl4_72),
% 21.26/3.14    inference(forward_demodulation,[],[f4514,f199])).
% 21.26/3.14  fof(f4514,plain,(
% 21.26/3.14    k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl4_72),
% 21.26/3.14    inference(avatar_component_clause,[],[f4512])).
% 21.26/3.14  fof(f4512,plain,(
% 21.26/3.14    spl4_72 <=> k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 21.26/3.14    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).
% 21.26/3.14  fof(f4909,plain,(
% 21.26/3.14    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)))),
% 21.26/3.14    inference(forward_demodulation,[],[f4465,f199])).
% 21.26/3.14  fof(f4465,plain,(
% 21.26/3.14    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),
% 21.26/3.14    inference(resolution,[],[f58,f1630])).
% 21.26/3.14  fof(f1630,plain,(
% 21.26/3.14    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)))) )),
% 21.26/3.14    inference(resolution,[],[f65,f57])).
% 21.26/3.14  fof(f65,plain,(
% 21.26/3.14    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) )),
% 21.26/3.14    inference(cnf_transformation,[],[f27])).
% 21.26/3.14  fof(f27,plain,(
% 21.26/3.14    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 21.26/3.14    inference(ennf_transformation,[],[f16])).
% 21.26/3.14  fof(f16,axiom,(
% 21.26/3.14    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 21.26/3.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).
% 21.26/3.14  fof(f4809,plain,(
% 21.26/3.14    spl4_2 | ~spl4_75),
% 21.26/3.14    inference(avatar_contradiction_clause,[],[f4808])).
% 21.26/3.14  fof(f4808,plain,(
% 21.26/3.14    $false | (spl4_2 | ~spl4_75)),
% 21.26/3.14    inference(subsumption_resolution,[],[f4807,f57])).
% 21.26/3.14  fof(f4807,plain,(
% 21.26/3.14    ~l1_pre_topc(sK0) | (spl4_2 | ~spl4_75)),
% 21.26/3.14    inference(subsumption_resolution,[],[f4806,f58])).
% 21.26/3.14  fof(f4806,plain,(
% 21.26/3.14    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl4_2 | ~spl4_75)),
% 21.26/3.14    inference(subsumption_resolution,[],[f4797,f126])).
% 21.26/3.14  fof(f126,plain,(
% 21.26/3.14    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | spl4_2),
% 21.26/3.14    inference(avatar_component_clause,[],[f124])).
% 21.26/3.14  fof(f4797,plain,(
% 21.26/3.14    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl4_75),
% 21.26/3.14    inference(superposition,[],[f64,f4775])).
% 21.26/3.14  fof(f64,plain,(
% 21.26/3.14    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 21.26/3.14    inference(cnf_transformation,[],[f26])).
% 21.26/3.14  fof(f26,plain,(
% 21.26/3.14    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 21.26/3.14    inference(ennf_transformation,[],[f18])).
% 21.26/3.14  fof(f18,axiom,(
% 21.26/3.14    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 21.26/3.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 21.26/3.14  fof(f4558,plain,(
% 21.26/3.14    spl4_71),
% 21.26/3.14    inference(avatar_contradiction_clause,[],[f4557])).
% 21.26/3.14  fof(f4557,plain,(
% 21.26/3.14    $false | spl4_71),
% 21.26/3.14    inference(subsumption_resolution,[],[f4556,f159])).
% 21.26/3.14  fof(f159,plain,(
% 21.26/3.14    r1_tarski(k5_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 21.26/3.14    inference(superposition,[],[f134,f157])).
% 21.26/3.14  fof(f134,plain,(
% 21.26/3.14    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))),X0)) )),
% 21.26/3.14    inference(superposition,[],[f97,f71])).
% 21.26/3.14  fof(f4556,plain,(
% 21.26/3.14    ~r1_tarski(k5_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | spl4_71),
% 21.26/3.14    inference(resolution,[],[f4555,f80])).
% 21.26/3.14  fof(f4555,plain,(
% 21.26/3.14    ~m1_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_71),
% 21.26/3.14    inference(forward_demodulation,[],[f4510,f199])).
% 21.26/3.14  fof(f4510,plain,(
% 21.26/3.14    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_71),
% 21.26/3.14    inference(avatar_component_clause,[],[f4508])).
% 21.26/3.14  fof(f4508,plain,(
% 21.26/3.14    spl4_71 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 21.26/3.14    introduced(avatar_definition,[new_symbols(naming,[spl4_71])])).
% 21.26/3.14  fof(f4515,plain,(
% 21.26/3.14    ~spl4_71 | spl4_72 | ~spl4_69),
% 21.26/3.14    inference(avatar_split_clause,[],[f4506,f4454,f4512,f4508])).
% 21.26/3.14  fof(f4454,plain,(
% 21.26/3.14    spl4_69 <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 21.26/3.14    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).
% 21.26/3.14  fof(f4506,plain,(
% 21.26/3.14    k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_69),
% 21.26/3.14    inference(subsumption_resolution,[],[f4505,f57])).
% 21.26/3.14  fof(f4505,plain,(
% 21.26/3.14    k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl4_69),
% 21.26/3.14    inference(resolution,[],[f4456,f66])).
% 21.26/3.14  fof(f66,plain,(
% 21.26/3.14    ( ! [X0,X1] : (~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 21.26/3.14    inference(cnf_transformation,[],[f29])).
% 21.26/3.14  fof(f29,plain,(
% 21.26/3.14    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 21.26/3.14    inference(flattening,[],[f28])).
% 21.26/3.14  fof(f28,plain,(
% 21.26/3.14    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 21.26/3.14    inference(ennf_transformation,[],[f15])).
% 21.26/3.14  fof(f15,axiom,(
% 21.26/3.14    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 21.26/3.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 21.26/3.14  fof(f4456,plain,(
% 21.26/3.14    v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~spl4_69),
% 21.26/3.14    inference(avatar_component_clause,[],[f4454])).
% 21.26/3.14  fof(f4475,plain,(
% 21.26/3.14    spl4_70),
% 21.26/3.14    inference(avatar_contradiction_clause,[],[f4474])).
% 21.26/3.14  fof(f4474,plain,(
% 21.26/3.14    $false | spl4_70),
% 21.26/3.14    inference(subsumption_resolution,[],[f4460,f58])).
% 21.26/3.14  fof(f4460,plain,(
% 21.26/3.14    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl4_70),
% 21.26/3.14    inference(avatar_component_clause,[],[f4458])).
% 21.26/3.14  fof(f4458,plain,(
% 21.26/3.14    spl4_70 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 21.26/3.14    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).
% 21.26/3.14  fof(f4461,plain,(
% 21.26/3.14    spl4_69 | ~spl4_70 | ~spl4_1),
% 21.26/3.14    inference(avatar_split_clause,[],[f4452,f120,f4458,f4454])).
% 21.26/3.14  fof(f4452,plain,(
% 21.26/3.14    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~spl4_1),
% 21.26/3.14    inference(resolution,[],[f121,f639])).
% 21.26/3.14  fof(f639,plain,(
% 21.26/3.14    ( ! [X0] : (~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)) )),
% 21.26/3.14    inference(resolution,[],[f68,f57])).
% 21.26/3.14  fof(f68,plain,(
% 21.26/3.14    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) )),
% 21.26/3.14    inference(cnf_transformation,[],[f44])).
% 21.26/3.14  fof(f44,plain,(
% 21.26/3.14    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 21.26/3.14    inference(nnf_transformation,[],[f30])).
% 21.26/3.14  fof(f30,plain,(
% 21.26/3.14    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 21.26/3.14    inference(ennf_transformation,[],[f19])).
% 21.26/3.14  fof(f19,axiom,(
% 21.26/3.14    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 21.26/3.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).
% 21.26/3.14  fof(f121,plain,(
% 21.26/3.14    v3_pre_topc(sK1,sK0) | ~spl4_1),
% 21.26/3.14    inference(avatar_component_clause,[],[f120])).
% 21.26/3.14  fof(f128,plain,(
% 21.26/3.14    spl4_1 | spl4_2),
% 21.26/3.14    inference(avatar_split_clause,[],[f59,f124,f120])).
% 21.26/3.14  fof(f59,plain,(
% 21.26/3.14    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 21.26/3.14    inference(cnf_transformation,[],[f43])).
% 21.26/3.14  fof(f127,plain,(
% 21.26/3.14    ~spl4_1 | ~spl4_2),
% 21.26/3.14    inference(avatar_split_clause,[],[f60,f124,f120])).
% 21.26/3.14  fof(f60,plain,(
% 21.26/3.14    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 21.26/3.14    inference(cnf_transformation,[],[f43])).
% 21.26/3.14  % SZS output end Proof for theBenchmark
% 21.26/3.14  % (8117)------------------------------
% 21.26/3.14  % (8117)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 21.26/3.14  % (8117)Termination reason: Refutation
% 21.26/3.14  
% 22.00/3.14  % (8117)Memory used [KB]: 25330
% 22.00/3.14  % (8117)Time elapsed: 2.679 s
% 22.00/3.14  % (8117)------------------------------
% 22.00/3.14  % (8117)------------------------------
% 22.00/3.14  % (8113)Success in time 2.781 s
%------------------------------------------------------------------------------
