%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:12 EST 2020

% Result     : Theorem 3.17s
% Output     : Refutation 3.91s
% Verified   : 
% Statistics : Number of formulae       :  241 (1340 expanded)
%              Number of leaves         :   41 ( 430 expanded)
%              Depth                    :   24
%              Number of atoms          :  601 (2538 expanded)
%              Number of equality atoms :  164 ( 923 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4780,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f101,f106,f111,f122,f155,f158,f303,f650,f688,f1433,f1442,f1528,f1625,f1665,f2164,f2802,f4504,f4684,f4772,f4779])).

fof(f4779,plain,
    ( ~ spl2_4
    | ~ spl2_42
    | spl2_69 ),
    inference(avatar_contradiction_clause,[],[f4778])).

fof(f4778,plain,
    ( $false
    | ~ spl2_4
    | ~ spl2_42
    | spl2_69 ),
    inference(subsumption_resolution,[],[f2800,f1533])).

fof(f1533,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl2_4
    | ~ spl2_42 ),
    inference(unit_resulting_resolution,[],[f121,f1441,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f1441,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_42 ),
    inference(avatar_component_clause,[],[f1439])).

fof(f1439,plain,
    ( spl2_42
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).

fof(f121,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl2_4
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f2800,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))
    | spl2_69 ),
    inference(avatar_component_clause,[],[f2799])).

fof(f2799,plain,
    ( spl2_69
  <=> r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_69])])).

fof(f4772,plain,
    ( ~ spl2_3
    | spl2_6
    | ~ spl2_20
    | ~ spl2_25
    | ~ spl2_42
    | ~ spl2_51
    | ~ spl2_55
    | ~ spl2_63
    | ~ spl2_69 ),
    inference(avatar_contradiction_clause,[],[f4771])).

fof(f4771,plain,
    ( $false
    | ~ spl2_3
    | spl2_6
    | ~ spl2_20
    | ~ spl2_25
    | ~ spl2_42
    | ~ spl2_51
    | ~ spl2_55
    | ~ spl2_63
    | ~ spl2_69 ),
    inference(subsumption_resolution,[],[f4769,f153])).

fof(f153,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl2_6
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f4769,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_20
    | ~ spl2_25
    | ~ spl2_42
    | ~ spl2_51
    | ~ spl2_55
    | ~ spl2_63
    | ~ spl2_69 ),
    inference(backward_demodulation,[],[f687,f4766])).

fof(f4766,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_3
    | ~ spl2_20
    | ~ spl2_42
    | ~ spl2_51
    | ~ spl2_55
    | ~ spl2_63
    | ~ spl2_69 ),
    inference(backward_demodulation,[],[f4764,f4547])).

fof(f4547,plain,
    ( sK1 = k5_xboole_0(sK1,k7_subset_1(sK1,k2_tops_1(sK0,sK1),sK1))
    | ~ spl2_51
    | ~ spl2_55 ),
    inference(forward_demodulation,[],[f4531,f1624])).

fof(f1624,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_51 ),
    inference(avatar_component_clause,[],[f1622])).

fof(f1622,plain,
    ( spl2_51
  <=> k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).

fof(f4531,plain,
    ( sK1 = k5_xboole_0(sK1,k7_subset_1(sK1,k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))),sK1))
    | ~ spl2_55 ),
    inference(superposition,[],[f4494,f1664])).

fof(f1664,plain,
    ( k3_subset_1(sK1,k2_tops_1(sK0,sK1)) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_55 ),
    inference(avatar_component_clause,[],[f1662])).

fof(f1662,plain,
    ( spl2_55
  <=> k3_subset_1(sK1,k2_tops_1(sK0,sK1)) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_55])])).

fof(f4494,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k7_subset_1(X0,k3_subset_1(X0,k7_subset_1(X0,X0,X1)),X0)) = X0 ),
    inference(backward_demodulation,[],[f1337,f4483])).

fof(f4483,plain,(
    ! [X6,X5] : k4_subset_1(X5,X5,k3_subset_1(X5,k7_subset_1(X5,X5,X6))) = X5 ),
    inference(superposition,[],[f4460,f592])).

fof(f592,plain,(
    ! [X0,X1] : k7_subset_1(X0,X0,k7_subset_1(X0,X0,X1)) = k3_subset_1(X0,k7_subset_1(X0,X0,X1)) ),
    inference(unit_resulting_resolution,[],[f256,f253])).

fof(f253,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1) ) ),
    inference(backward_demodulation,[],[f90,f245])).

fof(f245,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X0,X0,X1) ),
    inference(unit_resulting_resolution,[],[f95,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f82,f69])).

fof(f69,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f95,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f63,f60])).

fof(f60,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f63,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f73,f69])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f256,plain,(
    ! [X0,X1] : m1_subset_1(k7_subset_1(X0,X0,X1),k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f125,f245])).

fof(f125,plain,(
    ! [X0,X1] : m1_subset_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f88,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f88,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f67,f69])).

fof(f67,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f4460,plain,(
    ! [X0,X1] : k4_subset_1(X0,X0,k7_subset_1(X0,X0,X1)) = X0 ),
    inference(forward_demodulation,[],[f4459,f196])).

fof(f196,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f194,f195])).

fof(f195,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f187,f189])).

fof(f189,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f113,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f113,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f61,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f61,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f187,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(unit_resulting_resolution,[],[f88,f113,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
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

fof(f194,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = X0 ),
    inference(backward_demodulation,[],[f87,f189])).

fof(f87,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(definition_unfolding,[],[f62,f86])).

fof(f86,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f68,f69])).

fof(f68,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f62,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f4459,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_xboole_0) = k4_subset_1(X0,X0,k7_subset_1(X0,X0,X1)) ),
    inference(backward_demodulation,[],[f624,f4354])).

fof(f4354,plain,(
    ! [X0,X1] : k1_xboole_0 = k7_subset_1(X0,k7_subset_1(X0,X0,X1),X0) ),
    inference(superposition,[],[f593,f910])).

fof(f910,plain,(
    ! [X2,X1] : k1_xboole_0 = k7_subset_1(k7_subset_1(X1,X1,X2),k7_subset_1(X1,X1,X2),X1) ),
    inference(forward_demodulation,[],[f908,f513])).

fof(f513,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f226,f502])).

fof(f502,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(backward_demodulation,[],[f169,f500])).

fof(f500,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f499,f211])).

fof(f211,plain,(
    ! [X0] : k4_subset_1(X0,k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) = X0 ),
    inference(unit_resulting_resolution,[],[f61,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0 ) ),
    inference(forward_demodulation,[],[f75,f60])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

fof(f499,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = k4_subset_1(X0,k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f498,f230])).

fof(f230,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) = X0 ),
    inference(backward_demodulation,[],[f202,f219])).

fof(f219,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f61,f90])).

fof(f202,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = X0 ),
    inference(unit_resulting_resolution,[],[f113,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1 ) ),
    inference(definition_unfolding,[],[f71,f86])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f498,plain,(
    ! [X0] : k4_subset_1(X0,k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,k3_subset_1(k3_subset_1(X0,k1_xboole_0),k1_xboole_0)) ),
    inference(forward_demodulation,[],[f482,f305])).

fof(f305,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = k7_subset_1(X0,X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f61,f253])).

fof(f482,plain,(
    ! [X0] : k4_subset_1(X0,k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,k7_subset_1(k3_subset_1(X0,k1_xboole_0),k3_subset_1(X0,k1_xboole_0),k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f61,f160,f255])).

fof(f255,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k7_subset_1(X2,X2,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(backward_demodulation,[],[f92,f245])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f85,f86])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f160,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f61,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f169,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f61,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f226,plain,(
    ! [X0] : k3_subset_1(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f220,f126])).

fof(f126,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(unit_resulting_resolution,[],[f93,f70])).

fof(f93,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f220,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k3_subset_1(X0,X0) ),
    inference(unit_resulting_resolution,[],[f95,f90])).

fof(f908,plain,(
    ! [X2,X1] : k7_subset_1(k7_subset_1(X1,X1,X2),k7_subset_1(X1,X1,X2),X1) = k5_xboole_0(k7_subset_1(X1,X1,X2),k7_subset_1(X1,X1,X2)) ),
    inference(superposition,[],[f245,f257])).

fof(f257,plain,(
    ! [X0,X1] : k7_subset_1(X0,X0,X1) = k3_xboole_0(k7_subset_1(X0,X0,X1),X0) ),
    inference(backward_demodulation,[],[f127,f245])).

fof(f127,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(unit_resulting_resolution,[],[f88,f70])).

fof(f593,plain,(
    ! [X2,X0,X1] : k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),X2) = k7_subset_1(X0,k7_subset_1(X0,X0,X1),X2) ),
    inference(unit_resulting_resolution,[],[f256,f254])).

fof(f254,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) ) ),
    inference(backward_demodulation,[],[f91,f245])).

fof(f624,plain,(
    ! [X0,X1] : k4_subset_1(X0,X0,k7_subset_1(X0,X0,X1)) = k5_xboole_0(X0,k7_subset_1(X0,k7_subset_1(X0,X0,X1),X0)) ),
    inference(backward_demodulation,[],[f599,f593])).

fof(f599,plain,(
    ! [X0,X1] : k4_subset_1(X0,X0,k7_subset_1(X0,X0,X1)) = k5_xboole_0(X0,k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),X0)) ),
    inference(unit_resulting_resolution,[],[f95,f256,f255])).

fof(f1337,plain,(
    ! [X0,X1] : k4_subset_1(X0,X0,k3_subset_1(X0,k7_subset_1(X0,X0,X1))) = k5_xboole_0(X0,k7_subset_1(X0,k3_subset_1(X0,k7_subset_1(X0,X0,X1)),X0)) ),
    inference(forward_demodulation,[],[f1262,f1244])).

fof(f1244,plain,(
    ! [X2,X0,X1] : k7_subset_1(X0,k3_subset_1(X0,k7_subset_1(X0,X0,X1)),X2) = k7_subset_1(k3_subset_1(X0,k7_subset_1(X0,X0,X1)),k3_subset_1(X0,k7_subset_1(X0,X0,X1)),X2) ),
    inference(unit_resulting_resolution,[],[f256,f274])).

fof(f274,plain,(
    ! [X8,X7,X9] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(X7))
      | k7_subset_1(X7,k3_subset_1(X7,X8),X9) = k7_subset_1(k3_subset_1(X7,X8),k3_subset_1(X7,X8),X9) ) ),
    inference(forward_demodulation,[],[f249,f245])).

fof(f249,plain,(
    ! [X8,X7,X9] :
      ( k7_subset_1(X7,k3_subset_1(X7,X8),X9) = k5_xboole_0(k3_subset_1(X7,X8),k3_xboole_0(k3_subset_1(X7,X8),X9))
      | ~ m1_subset_1(X8,k1_zfmisc_1(X7)) ) ),
    inference(resolution,[],[f91,f72])).

fof(f1262,plain,(
    ! [X0,X1] : k4_subset_1(X0,X0,k3_subset_1(X0,k7_subset_1(X0,X0,X1))) = k5_xboole_0(X0,k7_subset_1(k3_subset_1(X0,k7_subset_1(X0,X0,X1)),k3_subset_1(X0,k7_subset_1(X0,X0,X1)),X0)) ),
    inference(unit_resulting_resolution,[],[f256,f95,f349])).

fof(f349,plain,(
    ! [X8,X7,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(X7))
      | ~ m1_subset_1(X8,k1_zfmisc_1(X7))
      | k4_subset_1(X7,X8,k3_subset_1(X7,X9)) = k5_xboole_0(X8,k7_subset_1(k3_subset_1(X7,X9),k3_subset_1(X7,X9),X8)) ) ),
    inference(resolution,[],[f255,f72])).

fof(f4764,plain,
    ( k2_pre_topc(sK0,sK1) = k5_xboole_0(sK1,k7_subset_1(sK1,k2_tops_1(sK0,sK1),sK1))
    | ~ spl2_3
    | ~ spl2_20
    | ~ spl2_42
    | ~ spl2_63
    | ~ spl2_69 ),
    inference(backward_demodulation,[],[f2163,f4763])).

fof(f4763,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(sK1,sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_20
    | ~ spl2_42
    | ~ spl2_63
    | ~ spl2_69 ),
    inference(backward_demodulation,[],[f4760,f649])).

fof(f649,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f647])).

fof(f647,plain,
    ( spl2_20
  <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f4760,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k4_subset_1(sK1,sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_42
    | ~ spl2_63
    | ~ spl2_69 ),
    inference(forward_demodulation,[],[f4729,f2163])).

fof(f4729,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k7_subset_1(sK1,k2_tops_1(sK0,sK1),sK1))
    | ~ spl2_3
    | ~ spl2_42
    | ~ spl2_69 ),
    inference(forward_demodulation,[],[f4651,f1544])).

fof(f1544,plain,
    ( ! [X0] : k7_subset_1(sK1,k2_tops_1(sK0,sK1),X0) = k7_subset_1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X0)
    | ~ spl2_42 ),
    inference(unit_resulting_resolution,[],[f1441,f271])).

fof(f271,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X3,X2)
      | k7_subset_1(X3,X3,X4) = k7_subset_1(X2,X3,X4) ) ),
    inference(forward_demodulation,[],[f247,f245])).

fof(f247,plain,(
    ! [X4,X2,X3] :
      ( k5_xboole_0(X3,k3_xboole_0(X3,X4)) = k7_subset_1(X2,X3,X4)
      | ~ r1_tarski(X3,X2) ) ),
    inference(resolution,[],[f91,f81])).

fof(f4651,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k7_subset_1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1))
    | ~ spl2_3
    | ~ spl2_69 ),
    inference(resolution,[],[f2801,f1179])).

fof(f1179,plain,
    ( ! [X14] :
        ( ~ r1_tarski(X14,u1_struct_0(sK0))
        | k4_subset_1(u1_struct_0(sK0),sK1,X14) = k5_xboole_0(sK1,k7_subset_1(X14,X14,sK1)) )
    | ~ spl2_3 ),
    inference(resolution,[],[f347,f110])).

fof(f110,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f347,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | k4_subset_1(X2,X3,X4) = k5_xboole_0(X3,k7_subset_1(X4,X4,X3))
      | ~ r1_tarski(X4,X2) ) ),
    inference(resolution,[],[f255,f81])).

fof(f2801,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl2_69 ),
    inference(avatar_component_clause,[],[f2799])).

fof(f2163,plain,
    ( k4_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k7_subset_1(sK1,k2_tops_1(sK0,sK1),sK1))
    | ~ spl2_63 ),
    inference(avatar_component_clause,[],[f2161])).

fof(f2161,plain,
    ( spl2_63
  <=> k4_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k7_subset_1(sK1,k2_tops_1(sK0,sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_63])])).

fof(f687,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f685])).

fof(f685,plain,
    ( spl2_25
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f4684,plain,
    ( ~ spl2_4
    | spl2_5
    | ~ spl2_8
    | ~ spl2_20
    | ~ spl2_42
    | ~ spl2_69
    | ~ spl2_78 ),
    inference(avatar_contradiction_clause,[],[f4683])).

fof(f4683,plain,
    ( $false
    | ~ spl2_4
    | spl2_5
    | ~ spl2_8
    | ~ spl2_20
    | ~ spl2_42
    | ~ spl2_69
    | ~ spl2_78 ),
    inference(subsumption_resolution,[],[f4682,f149])).

fof(f149,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl2_5
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f4682,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_20
    | ~ spl2_42
    | ~ spl2_69
    | ~ spl2_78 ),
    inference(backward_demodulation,[],[f302,f4680])).

fof(f4680,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_4
    | ~ spl2_20
    | ~ spl2_42
    | ~ spl2_69
    | ~ spl2_78 ),
    inference(backward_demodulation,[],[f649,f4679])).

fof(f4679,plain,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_4
    | ~ spl2_42
    | ~ spl2_69
    | ~ spl2_78 ),
    inference(forward_demodulation,[],[f4678,f4503])).

fof(f4503,plain,
    ( sK1 = k5_xboole_0(sK1,k7_subset_1(sK1,k2_tops_1(sK0,sK1),sK1))
    | ~ spl2_78 ),
    inference(avatar_component_clause,[],[f4501])).

fof(f4501,plain,
    ( spl2_78
  <=> sK1 = k5_xboole_0(sK1,k7_subset_1(sK1,k2_tops_1(sK0,sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_78])])).

fof(f4678,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k7_subset_1(sK1,k2_tops_1(sK0,sK1),sK1))
    | ~ spl2_4
    | ~ spl2_42
    | ~ spl2_69 ),
    inference(forward_demodulation,[],[f4641,f1544])).

fof(f4641,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k7_subset_1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1))
    | ~ spl2_4
    | ~ spl2_69 ),
    inference(unit_resulting_resolution,[],[f121,f2801,f1174])).

fof(f1174,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X4,X2)
      | k4_subset_1(X2,X3,X4) = k5_xboole_0(X3,k7_subset_1(X4,X4,X3))
      | ~ r1_tarski(X3,X2) ) ),
    inference(resolution,[],[f347,f81])).

fof(f302,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f300])).

fof(f300,plain,
    ( spl2_8
  <=> v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f4504,plain,
    ( spl2_78
    | ~ spl2_41
    | ~ spl2_63 ),
    inference(avatar_split_clause,[],[f4499,f2161,f1430,f4501])).

fof(f1430,plain,
    ( spl2_41
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).

fof(f4499,plain,
    ( sK1 = k5_xboole_0(sK1,k7_subset_1(sK1,k2_tops_1(sK0,sK1),sK1))
    | ~ spl2_41
    | ~ spl2_63 ),
    inference(backward_demodulation,[],[f2163,f4490])).

fof(f4490,plain,
    ( sK1 = k4_subset_1(sK1,sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_41 ),
    inference(superposition,[],[f4460,f1432])).

fof(f1432,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_41 ),
    inference(avatar_component_clause,[],[f1430])).

fof(f2802,plain,
    ( spl2_69
    | ~ spl2_4
    | ~ spl2_41 ),
    inference(avatar_split_clause,[],[f1514,f1430,f119,f2799])).

fof(f1514,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl2_4
    | ~ spl2_41 ),
    inference(superposition,[],[f264,f1432])).

fof(f264,plain,
    ( ! [X0] : r1_tarski(k7_subset_1(sK1,sK1,X0),u1_struct_0(sK0))
    | ~ spl2_4 ),
    inference(backward_demodulation,[],[f143,f245])).

fof(f143,plain,
    ( ! [X0] : r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),u1_struct_0(sK0))
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f88,f121,f84])).

fof(f2164,plain,
    ( spl2_63
    | ~ spl2_42 ),
    inference(avatar_split_clause,[],[f1559,f1439,f2161])).

fof(f1559,plain,
    ( k4_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k7_subset_1(sK1,k2_tops_1(sK0,sK1),sK1))
    | ~ spl2_42 ),
    inference(backward_demodulation,[],[f1545,f1544])).

fof(f1545,plain,
    ( k4_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k7_subset_1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1))
    | ~ spl2_42 ),
    inference(unit_resulting_resolution,[],[f95,f1441,f347])).

fof(f1665,plain,
    ( spl2_55
    | ~ spl2_42 ),
    inference(avatar_split_clause,[],[f1543,f1439,f1662])).

fof(f1543,plain,
    ( k3_subset_1(sK1,k2_tops_1(sK0,sK1)) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_42 ),
    inference(unit_resulting_resolution,[],[f1441,f262])).

fof(f262,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,X1)
      | k3_subset_1(X1,X2) = k7_subset_1(X1,X1,X2) ) ),
    inference(backward_demodulation,[],[f222,f245])).

fof(f222,plain,(
    ! [X2,X1] :
      ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_subset_1(X1,X2)
      | ~ r1_tarski(X2,X1) ) ),
    inference(resolution,[],[f90,f81])).

fof(f1625,plain,
    ( spl2_51
    | ~ spl2_42 ),
    inference(avatar_split_clause,[],[f1540,f1439,f1622])).

fof(f1540,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_42 ),
    inference(unit_resulting_resolution,[],[f1441,f172])).

fof(f172,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,X1)
      | k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    inference(resolution,[],[f74,f81])).

fof(f1528,plain,
    ( spl2_42
    | ~ spl2_41 ),
    inference(avatar_split_clause,[],[f1515,f1430,f1439])).

fof(f1515,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_41 ),
    inference(superposition,[],[f251,f1432])).

fof(f251,plain,(
    ! [X0,X1] : r1_tarski(k7_subset_1(X0,X0,X1),X0) ),
    inference(backward_demodulation,[],[f88,f245])).

fof(f1442,plain,
    ( spl2_42
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f1436,f148,f108,f103,f1439])).

fof(f103,plain,
    ( spl2_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f1436,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f105,f110,f150,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k2_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

fof(f150,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f148])).

fof(f105,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f1433,plain,
    ( spl2_41
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f586,f152,f108,f1430])).

fof(f586,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(superposition,[],[f270,f154])).

fof(f154,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f152])).

fof(f270,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f243,f245])).

fof(f243,plain,
    ( ! [X0] : k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) = k7_subset_1(u1_struct_0(sK0),sK1,X0)
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f110,f91])).

fof(f688,plain,
    ( spl2_25
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f369,f108,f103,f685])).

fof(f369,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f105,f110,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f650,plain,
    ( spl2_20
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f328,f108,f103,f647])).

fof(f328,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f105,f110,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f303,plain,
    ( spl2_8
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f238,f108,f103,f98,f300])).

fof(f98,plain,
    ( spl2_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f238,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f100,f105,f110,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f100,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f98])).

fof(f158,plain,
    ( ~ spl2_5
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f157,f152,f148])).

fof(f157,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_6 ),
    inference(trivial_inequality_removal,[],[f156])).

fof(f156,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_6 ),
    inference(backward_demodulation,[],[f59,f154])).

fof(f59,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f48,f50,f49])).

fof(f49,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | ~ v4_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | ~ v4_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | v4_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | ~ v4_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | v4_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | ~ v4_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | v4_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

fof(f155,plain,
    ( spl2_5
    | spl2_6 ),
    inference(avatar_split_clause,[],[f58,f152,f148])).

fof(f58,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f122,plain,
    ( spl2_4
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f112,f108,f119])).

fof(f112,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f110,f80])).

fof(f111,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f57,f108])).

fof(f57,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f51])).

fof(f106,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f56,f103])).

fof(f56,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f101,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f55,f98])).

fof(f55,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:18:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.48  % (30831)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.50  % (30830)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.50  % (30816)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.51  % (30820)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.51  % (30818)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.51  % (30844)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.51  % (30821)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (30817)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (30829)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.53  % (30836)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.53  % (30828)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.53  % (30825)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.53  % (30827)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.54  % (30838)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.54  % (30837)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.54  % (30822)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.54  % (30834)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.54  % (30817)Refutation not found, incomplete strategy% (30817)------------------------------
% 0.22/0.54  % (30817)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (30817)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (30817)Memory used [KB]: 1791
% 0.22/0.54  % (30817)Time elapsed: 0.120 s
% 0.22/0.54  % (30817)------------------------------
% 0.22/0.54  % (30817)------------------------------
% 0.22/0.54  % (30845)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.54  % (30843)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.54  % (30841)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.55  % (30847)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.55  % (30833)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.55  % (30824)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.55  % (30835)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.55  % (30848)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (30848)Refutation not found, incomplete strategy% (30848)------------------------------
% 0.22/0.55  % (30848)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (30848)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (30848)Memory used [KB]: 1663
% 0.22/0.55  % (30848)Time elapsed: 0.149 s
% 0.22/0.55  % (30848)------------------------------
% 0.22/0.55  % (30848)------------------------------
% 0.22/0.56  % (30840)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.56  % (30826)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.57  % (30842)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.57  % (30823)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.58  % (30844)Refutation not found, incomplete strategy% (30844)------------------------------
% 0.22/0.58  % (30844)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (30844)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (30844)Memory used [KB]: 6780
% 0.22/0.58  % (30844)Time elapsed: 0.169 s
% 0.22/0.58  % (30844)------------------------------
% 0.22/0.58  % (30844)------------------------------
% 0.22/0.58  % (30839)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 2.01/0.67  % (30863)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.01/0.67  % (30864)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.01/0.68  % (30820)Refutation not found, incomplete strategy% (30820)------------------------------
% 2.01/0.68  % (30820)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.01/0.68  % (30820)Termination reason: Refutation not found, incomplete strategy
% 2.01/0.68  
% 2.01/0.68  % (30820)Memory used [KB]: 6140
% 2.01/0.68  % (30820)Time elapsed: 0.252 s
% 2.01/0.68  % (30820)------------------------------
% 2.01/0.68  % (30820)------------------------------
% 2.64/0.71  % (30865)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.64/0.71  % (30865)Refutation not found, incomplete strategy% (30865)------------------------------
% 2.64/0.71  % (30865)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.64/0.71  % (30865)Termination reason: Refutation not found, incomplete strategy
% 2.64/0.71  
% 2.64/0.71  % (30865)Memory used [KB]: 6140
% 2.64/0.71  % (30865)Time elapsed: 0.109 s
% 2.64/0.71  % (30865)------------------------------
% 2.64/0.71  % (30865)------------------------------
% 3.17/0.82  % (30877)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 3.17/0.84  % (30842)Time limit reached!
% 3.17/0.84  % (30842)------------------------------
% 3.17/0.84  % (30842)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.17/0.84  % (30842)Termination reason: Time limit
% 3.17/0.84  % (30842)Termination phase: Saturation
% 3.17/0.84  
% 3.17/0.84  % (30842)Memory used [KB]: 12025
% 3.17/0.84  % (30842)Time elapsed: 0.422 s
% 3.17/0.84  % (30842)------------------------------
% 3.17/0.84  % (30842)------------------------------
% 3.17/0.84  % (30818)Time limit reached!
% 3.17/0.84  % (30818)------------------------------
% 3.17/0.84  % (30818)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.17/0.84  % (30818)Termination reason: Time limit
% 3.17/0.84  % (30818)Termination phase: Saturation
% 3.17/0.84  
% 3.17/0.84  % (30818)Memory used [KB]: 6524
% 3.17/0.84  % (30818)Time elapsed: 0.400 s
% 3.17/0.84  % (30818)------------------------------
% 3.17/0.84  % (30818)------------------------------
% 3.17/0.85  % (30878)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 3.17/0.86  % (30838)Refutation found. Thanks to Tanya!
% 3.17/0.86  % SZS status Theorem for theBenchmark
% 3.17/0.86  % SZS output start Proof for theBenchmark
% 3.91/0.88  fof(f4780,plain,(
% 3.91/0.88    $false),
% 3.91/0.88    inference(avatar_sat_refutation,[],[f101,f106,f111,f122,f155,f158,f303,f650,f688,f1433,f1442,f1528,f1625,f1665,f2164,f2802,f4504,f4684,f4772,f4779])).
% 3.91/0.88  fof(f4779,plain,(
% 3.91/0.88    ~spl2_4 | ~spl2_42 | spl2_69),
% 3.91/0.88    inference(avatar_contradiction_clause,[],[f4778])).
% 3.91/0.88  fof(f4778,plain,(
% 3.91/0.88    $false | (~spl2_4 | ~spl2_42 | spl2_69)),
% 3.91/0.88    inference(subsumption_resolution,[],[f2800,f1533])).
% 3.91/0.88  fof(f1533,plain,(
% 3.91/0.88    r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) | (~spl2_4 | ~spl2_42)),
% 3.91/0.88    inference(unit_resulting_resolution,[],[f121,f1441,f84])).
% 3.91/0.88  fof(f84,plain,(
% 3.91/0.88    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.91/0.88    inference(cnf_transformation,[],[f44])).
% 3.91/0.88  fof(f44,plain,(
% 3.91/0.88    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.91/0.88    inference(flattening,[],[f43])).
% 3.91/0.88  fof(f43,plain,(
% 3.91/0.88    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.91/0.88    inference(ennf_transformation,[],[f5])).
% 3.91/0.88  fof(f5,axiom,(
% 3.91/0.88    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.91/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 3.91/0.88  fof(f1441,plain,(
% 3.91/0.88    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_42),
% 3.91/0.88    inference(avatar_component_clause,[],[f1439])).
% 3.91/0.88  fof(f1439,plain,(
% 3.91/0.88    spl2_42 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 3.91/0.88    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).
% 3.91/0.88  fof(f121,plain,(
% 3.91/0.88    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl2_4),
% 3.91/0.88    inference(avatar_component_clause,[],[f119])).
% 3.91/0.88  fof(f119,plain,(
% 3.91/0.88    spl2_4 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 3.91/0.88    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 3.91/0.88  fof(f2800,plain,(
% 3.91/0.88    ~r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) | spl2_69),
% 3.91/0.88    inference(avatar_component_clause,[],[f2799])).
% 3.91/0.88  fof(f2799,plain,(
% 3.91/0.88    spl2_69 <=> r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 3.91/0.88    introduced(avatar_definition,[new_symbols(naming,[spl2_69])])).
% 3.91/0.88  fof(f4772,plain,(
% 3.91/0.88    ~spl2_3 | spl2_6 | ~spl2_20 | ~spl2_25 | ~spl2_42 | ~spl2_51 | ~spl2_55 | ~spl2_63 | ~spl2_69),
% 3.91/0.88    inference(avatar_contradiction_clause,[],[f4771])).
% 3.91/0.88  fof(f4771,plain,(
% 3.91/0.88    $false | (~spl2_3 | spl2_6 | ~spl2_20 | ~spl2_25 | ~spl2_42 | ~spl2_51 | ~spl2_55 | ~spl2_63 | ~spl2_69)),
% 3.91/0.88    inference(subsumption_resolution,[],[f4769,f153])).
% 3.91/0.88  fof(f153,plain,(
% 3.91/0.88    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | spl2_6),
% 3.91/0.88    inference(avatar_component_clause,[],[f152])).
% 3.91/0.88  fof(f152,plain,(
% 3.91/0.88    spl2_6 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 3.91/0.88    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 3.91/0.88  fof(f4769,plain,(
% 3.91/0.88    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_20 | ~spl2_25 | ~spl2_42 | ~spl2_51 | ~spl2_55 | ~spl2_63 | ~spl2_69)),
% 3.91/0.88    inference(backward_demodulation,[],[f687,f4766])).
% 3.91/0.88  fof(f4766,plain,(
% 3.91/0.88    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_3 | ~spl2_20 | ~spl2_42 | ~spl2_51 | ~spl2_55 | ~spl2_63 | ~spl2_69)),
% 3.91/0.88    inference(backward_demodulation,[],[f4764,f4547])).
% 3.91/0.88  fof(f4547,plain,(
% 3.91/0.88    sK1 = k5_xboole_0(sK1,k7_subset_1(sK1,k2_tops_1(sK0,sK1),sK1)) | (~spl2_51 | ~spl2_55)),
% 3.91/0.88    inference(forward_demodulation,[],[f4531,f1624])).
% 3.91/0.88  fof(f1624,plain,(
% 3.91/0.88    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) | ~spl2_51),
% 3.91/0.88    inference(avatar_component_clause,[],[f1622])).
% 3.91/0.88  fof(f1622,plain,(
% 3.91/0.88    spl2_51 <=> k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1)))),
% 3.91/0.88    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).
% 3.91/0.88  fof(f4531,plain,(
% 3.91/0.88    sK1 = k5_xboole_0(sK1,k7_subset_1(sK1,k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))),sK1)) | ~spl2_55),
% 3.91/0.88    inference(superposition,[],[f4494,f1664])).
% 3.91/0.88  fof(f1664,plain,(
% 3.91/0.88    k3_subset_1(sK1,k2_tops_1(sK0,sK1)) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) | ~spl2_55),
% 3.91/0.88    inference(avatar_component_clause,[],[f1662])).
% 3.91/0.88  fof(f1662,plain,(
% 3.91/0.88    spl2_55 <=> k3_subset_1(sK1,k2_tops_1(sK0,sK1)) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1))),
% 3.91/0.88    introduced(avatar_definition,[new_symbols(naming,[spl2_55])])).
% 3.91/0.88  fof(f4494,plain,(
% 3.91/0.88    ( ! [X0,X1] : (k5_xboole_0(X0,k7_subset_1(X0,k3_subset_1(X0,k7_subset_1(X0,X0,X1)),X0)) = X0) )),
% 3.91/0.88    inference(backward_demodulation,[],[f1337,f4483])).
% 3.91/0.88  fof(f4483,plain,(
% 3.91/0.88    ( ! [X6,X5] : (k4_subset_1(X5,X5,k3_subset_1(X5,k7_subset_1(X5,X5,X6))) = X5) )),
% 3.91/0.88    inference(superposition,[],[f4460,f592])).
% 3.91/0.88  fof(f592,plain,(
% 3.91/0.88    ( ! [X0,X1] : (k7_subset_1(X0,X0,k7_subset_1(X0,X0,X1)) = k3_subset_1(X0,k7_subset_1(X0,X0,X1))) )),
% 3.91/0.88    inference(unit_resulting_resolution,[],[f256,f253])).
% 3.91/0.88  fof(f253,plain,(
% 3.91/0.88    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1)) )),
% 3.91/0.88    inference(backward_demodulation,[],[f90,f245])).
% 3.91/0.88  fof(f245,plain,(
% 3.91/0.88    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X0,X0,X1)) )),
% 3.91/0.88    inference(unit_resulting_resolution,[],[f95,f91])).
% 3.91/0.88  fof(f91,plain,(
% 3.91/0.88    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2))) )),
% 3.91/0.88    inference(definition_unfolding,[],[f82,f69])).
% 3.91/0.88  fof(f69,plain,(
% 3.91/0.88    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.91/0.88    inference(cnf_transformation,[],[f2])).
% 3.91/0.88  fof(f2,axiom,(
% 3.91/0.88    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.91/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 3.91/0.88  fof(f82,plain,(
% 3.91/0.88    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.91/0.88    inference(cnf_transformation,[],[f40])).
% 3.91/0.88  fof(f40,plain,(
% 3.91/0.88    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.91/0.88    inference(ennf_transformation,[],[f15])).
% 3.91/0.88  fof(f15,axiom,(
% 3.91/0.88    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 3.91/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 3.91/0.88  fof(f95,plain,(
% 3.91/0.88    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 3.91/0.88    inference(forward_demodulation,[],[f63,f60])).
% 3.91/0.88  fof(f60,plain,(
% 3.91/0.88    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.91/0.88    inference(cnf_transformation,[],[f9])).
% 3.91/0.88  fof(f9,axiom,(
% 3.91/0.88    ! [X0] : k2_subset_1(X0) = X0),
% 3.91/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 3.91/0.88  fof(f63,plain,(
% 3.91/0.88    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.91/0.88    inference(cnf_transformation,[],[f11])).
% 3.91/0.88  fof(f11,axiom,(
% 3.91/0.88    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.91/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 3.91/0.88  fof(f90,plain,(
% 3.91/0.88    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 3.91/0.88    inference(definition_unfolding,[],[f73,f69])).
% 3.91/0.88  fof(f73,plain,(
% 3.91/0.88    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.91/0.88    inference(cnf_transformation,[],[f35])).
% 3.91/0.88  fof(f35,plain,(
% 3.91/0.88    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.91/0.88    inference(ennf_transformation,[],[f10])).
% 3.91/0.88  fof(f10,axiom,(
% 3.91/0.88    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.91/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 3.91/0.88  fof(f256,plain,(
% 3.91/0.88    ( ! [X0,X1] : (m1_subset_1(k7_subset_1(X0,X0,X1),k1_zfmisc_1(X0))) )),
% 3.91/0.88    inference(backward_demodulation,[],[f125,f245])).
% 3.91/0.88  fof(f125,plain,(
% 3.91/0.88    ( ! [X0,X1] : (m1_subset_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k1_zfmisc_1(X0))) )),
% 3.91/0.88    inference(unit_resulting_resolution,[],[f88,f81])).
% 3.91/0.88  fof(f81,plain,(
% 3.91/0.88    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.91/0.88    inference(cnf_transformation,[],[f54])).
% 3.91/0.88  fof(f54,plain,(
% 3.91/0.88    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.91/0.88    inference(nnf_transformation,[],[f18])).
% 3.91/0.88  fof(f18,axiom,(
% 3.91/0.88    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.91/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 3.91/0.88  fof(f88,plain,(
% 3.91/0.88    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 3.91/0.88    inference(definition_unfolding,[],[f67,f69])).
% 3.91/0.88  fof(f67,plain,(
% 3.91/0.88    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.91/0.88    inference(cnf_transformation,[],[f7])).
% 3.91/0.88  fof(f7,axiom,(
% 3.91/0.88    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.91/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 3.91/0.88  fof(f4460,plain,(
% 3.91/0.88    ( ! [X0,X1] : (k4_subset_1(X0,X0,k7_subset_1(X0,X0,X1)) = X0) )),
% 3.91/0.88    inference(forward_demodulation,[],[f4459,f196])).
% 3.91/0.88  fof(f196,plain,(
% 3.91/0.88    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.91/0.88    inference(backward_demodulation,[],[f194,f195])).
% 3.91/0.88  fof(f195,plain,(
% 3.91/0.88    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 3.91/0.88    inference(forward_demodulation,[],[f187,f189])).
% 3.91/0.88  fof(f189,plain,(
% 3.91/0.88    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 3.91/0.88    inference(unit_resulting_resolution,[],[f113,f70])).
% 3.91/0.88  fof(f70,plain,(
% 3.91/0.88    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 3.91/0.88    inference(cnf_transformation,[],[f32])).
% 3.91/0.88  fof(f32,plain,(
% 3.91/0.88    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.91/0.88    inference(ennf_transformation,[],[f6])).
% 3.91/0.88  fof(f6,axiom,(
% 3.91/0.88    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.91/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 3.91/0.88  fof(f113,plain,(
% 3.91/0.88    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.91/0.88    inference(unit_resulting_resolution,[],[f61,f80])).
% 3.91/0.88  fof(f80,plain,(
% 3.91/0.88    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 3.91/0.88    inference(cnf_transformation,[],[f54])).
% 3.91/0.88  fof(f61,plain,(
% 3.91/0.88    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.91/0.88    inference(cnf_transformation,[],[f17])).
% 3.91/0.88  fof(f17,axiom,(
% 3.91/0.88    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.91/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 3.91/0.88  fof(f187,plain,(
% 3.91/0.88    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) )),
% 3.91/0.88    inference(unit_resulting_resolution,[],[f88,f113,f79])).
% 3.91/0.88  fof(f79,plain,(
% 3.91/0.88    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 3.91/0.88    inference(cnf_transformation,[],[f53])).
% 3.91/0.88  fof(f53,plain,(
% 3.91/0.88    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.91/0.88    inference(flattening,[],[f52])).
% 3.91/0.88  fof(f52,plain,(
% 3.91/0.88    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.91/0.88    inference(nnf_transformation,[],[f1])).
% 3.91/0.88  fof(f1,axiom,(
% 3.91/0.88    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.91/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.91/0.88  fof(f194,plain,(
% 3.91/0.88    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = X0) )),
% 3.91/0.88    inference(backward_demodulation,[],[f87,f189])).
% 3.91/0.88  fof(f87,plain,(
% 3.91/0.88    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0) )),
% 3.91/0.88    inference(definition_unfolding,[],[f62,f86])).
% 3.91/0.88  fof(f86,plain,(
% 3.91/0.88    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 3.91/0.88    inference(definition_unfolding,[],[f68,f69])).
% 3.91/0.88  fof(f68,plain,(
% 3.91/0.88    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.91/0.88    inference(cnf_transformation,[],[f8])).
% 3.91/0.88  fof(f8,axiom,(
% 3.91/0.88    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.91/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 3.91/0.88  fof(f62,plain,(
% 3.91/0.88    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.91/0.88    inference(cnf_transformation,[],[f4])).
% 3.91/0.88  fof(f4,axiom,(
% 3.91/0.88    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.91/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 3.91/0.88  fof(f4459,plain,(
% 3.91/0.88    ( ! [X0,X1] : (k5_xboole_0(X0,k1_xboole_0) = k4_subset_1(X0,X0,k7_subset_1(X0,X0,X1))) )),
% 3.91/0.88    inference(backward_demodulation,[],[f624,f4354])).
% 3.91/0.88  fof(f4354,plain,(
% 3.91/0.88    ( ! [X0,X1] : (k1_xboole_0 = k7_subset_1(X0,k7_subset_1(X0,X0,X1),X0)) )),
% 3.91/0.88    inference(superposition,[],[f593,f910])).
% 3.91/0.88  fof(f910,plain,(
% 3.91/0.88    ( ! [X2,X1] : (k1_xboole_0 = k7_subset_1(k7_subset_1(X1,X1,X2),k7_subset_1(X1,X1,X2),X1)) )),
% 3.91/0.88    inference(forward_demodulation,[],[f908,f513])).
% 3.91/0.88  fof(f513,plain,(
% 3.91/0.88    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 3.91/0.88    inference(backward_demodulation,[],[f226,f502])).
% 3.91/0.88  fof(f502,plain,(
% 3.91/0.88    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 3.91/0.88    inference(backward_demodulation,[],[f169,f500])).
% 3.91/0.88  fof(f500,plain,(
% 3.91/0.88    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 3.91/0.88    inference(forward_demodulation,[],[f499,f211])).
% 3.91/0.88  fof(f211,plain,(
% 3.91/0.88    ( ! [X0] : (k4_subset_1(X0,k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) = X0) )),
% 3.91/0.88    inference(unit_resulting_resolution,[],[f61,f96])).
% 3.91/0.88  fof(f96,plain,(
% 3.91/0.88    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0) )),
% 3.91/0.88    inference(forward_demodulation,[],[f75,f60])).
% 3.91/0.88  fof(f75,plain,(
% 3.91/0.88    ( ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.91/0.88    inference(cnf_transformation,[],[f37])).
% 3.91/0.88  fof(f37,plain,(
% 3.91/0.88    ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.91/0.88    inference(ennf_transformation,[],[f16])).
% 3.91/0.88  fof(f16,axiom,(
% 3.91/0.88    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 3.91/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).
% 3.91/0.88  fof(f499,plain,(
% 3.91/0.88    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = k4_subset_1(X0,k1_xboole_0,k3_subset_1(X0,k1_xboole_0))) )),
% 3.91/0.88    inference(forward_demodulation,[],[f498,f230])).
% 3.91/0.88  fof(f230,plain,(
% 3.91/0.88    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) = X0) )),
% 3.91/0.88    inference(backward_demodulation,[],[f202,f219])).
% 3.91/0.88  fof(f219,plain,(
% 3.91/0.88    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) )),
% 3.91/0.88    inference(unit_resulting_resolution,[],[f61,f90])).
% 3.91/0.88  fof(f202,plain,(
% 3.91/0.88    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = X0) )),
% 3.91/0.88    inference(unit_resulting_resolution,[],[f113,f89])).
% 3.91/0.88  fof(f89,plain,(
% 3.91/0.88    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1) )),
% 3.91/0.88    inference(definition_unfolding,[],[f71,f86])).
% 3.91/0.88  fof(f71,plain,(
% 3.91/0.88    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 3.91/0.88    inference(cnf_transformation,[],[f33])).
% 3.91/0.88  fof(f33,plain,(
% 3.91/0.88    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.91/0.88    inference(ennf_transformation,[],[f3])).
% 3.91/0.88  fof(f3,axiom,(
% 3.91/0.88    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.91/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 3.91/0.88  fof(f498,plain,(
% 3.91/0.88    ( ! [X0] : (k4_subset_1(X0,k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,k3_subset_1(k3_subset_1(X0,k1_xboole_0),k1_xboole_0))) )),
% 3.91/0.88    inference(forward_demodulation,[],[f482,f305])).
% 3.91/0.88  fof(f305,plain,(
% 3.91/0.88    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = k7_subset_1(X0,X0,k1_xboole_0)) )),
% 3.91/0.88    inference(unit_resulting_resolution,[],[f61,f253])).
% 3.91/0.88  fof(f482,plain,(
% 3.91/0.88    ( ! [X0] : (k4_subset_1(X0,k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,k7_subset_1(k3_subset_1(X0,k1_xboole_0),k3_subset_1(X0,k1_xboole_0),k1_xboole_0))) )),
% 3.91/0.88    inference(unit_resulting_resolution,[],[f61,f160,f255])).
% 3.91/0.88  fof(f255,plain,(
% 3.91/0.88    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k7_subset_1(X2,X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.91/0.88    inference(backward_demodulation,[],[f92,f245])).
% 3.91/0.88  fof(f92,plain,(
% 3.91/0.88    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.91/0.88    inference(definition_unfolding,[],[f85,f86])).
% 3.91/0.88  fof(f85,plain,(
% 3.91/0.88    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.91/0.88    inference(cnf_transformation,[],[f46])).
% 3.91/0.88  fof(f46,plain,(
% 3.91/0.88    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.91/0.88    inference(flattening,[],[f45])).
% 3.91/0.88  fof(f45,plain,(
% 3.91/0.88    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.91/0.88    inference(ennf_transformation,[],[f14])).
% 3.91/0.88  fof(f14,axiom,(
% 3.91/0.88    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 3.91/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 3.91/0.88  fof(f160,plain,(
% 3.91/0.88    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 3.91/0.88    inference(unit_resulting_resolution,[],[f61,f72])).
% 3.91/0.88  fof(f72,plain,(
% 3.91/0.88    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.91/0.88    inference(cnf_transformation,[],[f34])).
% 3.91/0.88  fof(f34,plain,(
% 3.91/0.88    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.91/0.88    inference(ennf_transformation,[],[f12])).
% 3.91/0.88  fof(f12,axiom,(
% 3.91/0.88    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.91/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 3.91/0.88  fof(f169,plain,(
% 3.91/0.88    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0))) )),
% 3.91/0.88    inference(unit_resulting_resolution,[],[f61,f74])).
% 3.91/0.88  fof(f74,plain,(
% 3.91/0.88    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 3.91/0.88    inference(cnf_transformation,[],[f36])).
% 3.91/0.88  fof(f36,plain,(
% 3.91/0.88    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.91/0.88    inference(ennf_transformation,[],[f13])).
% 3.91/0.88  fof(f13,axiom,(
% 3.91/0.88    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 3.91/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 3.91/0.88  fof(f226,plain,(
% 3.91/0.88    ( ! [X0] : (k3_subset_1(X0,X0) = k5_xboole_0(X0,X0)) )),
% 3.91/0.88    inference(forward_demodulation,[],[f220,f126])).
% 3.91/0.88  fof(f126,plain,(
% 3.91/0.88    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.91/0.88    inference(unit_resulting_resolution,[],[f93,f70])).
% 3.91/0.88  fof(f93,plain,(
% 3.91/0.88    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.91/0.88    inference(equality_resolution,[],[f78])).
% 3.91/0.88  fof(f78,plain,(
% 3.91/0.88    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.91/0.88    inference(cnf_transformation,[],[f53])).
% 3.91/0.88  fof(f220,plain,(
% 3.91/0.88    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k3_subset_1(X0,X0)) )),
% 3.91/0.88    inference(unit_resulting_resolution,[],[f95,f90])).
% 3.91/0.88  fof(f908,plain,(
% 3.91/0.88    ( ! [X2,X1] : (k7_subset_1(k7_subset_1(X1,X1,X2),k7_subset_1(X1,X1,X2),X1) = k5_xboole_0(k7_subset_1(X1,X1,X2),k7_subset_1(X1,X1,X2))) )),
% 3.91/0.88    inference(superposition,[],[f245,f257])).
% 3.91/0.88  fof(f257,plain,(
% 3.91/0.88    ( ! [X0,X1] : (k7_subset_1(X0,X0,X1) = k3_xboole_0(k7_subset_1(X0,X0,X1),X0)) )),
% 3.91/0.88    inference(backward_demodulation,[],[f127,f245])).
% 3.91/0.88  fof(f127,plain,(
% 3.91/0.88    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 3.91/0.88    inference(unit_resulting_resolution,[],[f88,f70])).
% 3.91/0.88  fof(f593,plain,(
% 3.91/0.88    ( ! [X2,X0,X1] : (k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),X2) = k7_subset_1(X0,k7_subset_1(X0,X0,X1),X2)) )),
% 3.91/0.88    inference(unit_resulting_resolution,[],[f256,f254])).
% 3.91/0.88  fof(f254,plain,(
% 3.91/0.88    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)) )),
% 3.91/0.88    inference(backward_demodulation,[],[f91,f245])).
% 3.91/0.88  fof(f624,plain,(
% 3.91/0.88    ( ! [X0,X1] : (k4_subset_1(X0,X0,k7_subset_1(X0,X0,X1)) = k5_xboole_0(X0,k7_subset_1(X0,k7_subset_1(X0,X0,X1),X0))) )),
% 3.91/0.88    inference(backward_demodulation,[],[f599,f593])).
% 3.91/0.88  fof(f599,plain,(
% 3.91/0.88    ( ! [X0,X1] : (k4_subset_1(X0,X0,k7_subset_1(X0,X0,X1)) = k5_xboole_0(X0,k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),X0))) )),
% 3.91/0.88    inference(unit_resulting_resolution,[],[f95,f256,f255])).
% 3.91/0.88  fof(f1337,plain,(
% 3.91/0.88    ( ! [X0,X1] : (k4_subset_1(X0,X0,k3_subset_1(X0,k7_subset_1(X0,X0,X1))) = k5_xboole_0(X0,k7_subset_1(X0,k3_subset_1(X0,k7_subset_1(X0,X0,X1)),X0))) )),
% 3.91/0.88    inference(forward_demodulation,[],[f1262,f1244])).
% 3.91/0.88  fof(f1244,plain,(
% 3.91/0.88    ( ! [X2,X0,X1] : (k7_subset_1(X0,k3_subset_1(X0,k7_subset_1(X0,X0,X1)),X2) = k7_subset_1(k3_subset_1(X0,k7_subset_1(X0,X0,X1)),k3_subset_1(X0,k7_subset_1(X0,X0,X1)),X2)) )),
% 3.91/0.88    inference(unit_resulting_resolution,[],[f256,f274])).
% 3.91/0.88  fof(f274,plain,(
% 3.91/0.88    ( ! [X8,X7,X9] : (~m1_subset_1(X8,k1_zfmisc_1(X7)) | k7_subset_1(X7,k3_subset_1(X7,X8),X9) = k7_subset_1(k3_subset_1(X7,X8),k3_subset_1(X7,X8),X9)) )),
% 3.91/0.88    inference(forward_demodulation,[],[f249,f245])).
% 3.91/0.88  fof(f249,plain,(
% 3.91/0.88    ( ! [X8,X7,X9] : (k7_subset_1(X7,k3_subset_1(X7,X8),X9) = k5_xboole_0(k3_subset_1(X7,X8),k3_xboole_0(k3_subset_1(X7,X8),X9)) | ~m1_subset_1(X8,k1_zfmisc_1(X7))) )),
% 3.91/0.88    inference(resolution,[],[f91,f72])).
% 3.91/0.88  fof(f1262,plain,(
% 3.91/0.88    ( ! [X0,X1] : (k4_subset_1(X0,X0,k3_subset_1(X0,k7_subset_1(X0,X0,X1))) = k5_xboole_0(X0,k7_subset_1(k3_subset_1(X0,k7_subset_1(X0,X0,X1)),k3_subset_1(X0,k7_subset_1(X0,X0,X1)),X0))) )),
% 3.91/0.88    inference(unit_resulting_resolution,[],[f256,f95,f349])).
% 3.91/0.88  fof(f349,plain,(
% 3.91/0.88    ( ! [X8,X7,X9] : (~m1_subset_1(X9,k1_zfmisc_1(X7)) | ~m1_subset_1(X8,k1_zfmisc_1(X7)) | k4_subset_1(X7,X8,k3_subset_1(X7,X9)) = k5_xboole_0(X8,k7_subset_1(k3_subset_1(X7,X9),k3_subset_1(X7,X9),X8))) )),
% 3.91/0.88    inference(resolution,[],[f255,f72])).
% 3.91/0.88  fof(f4764,plain,(
% 3.91/0.88    k2_pre_topc(sK0,sK1) = k5_xboole_0(sK1,k7_subset_1(sK1,k2_tops_1(sK0,sK1),sK1)) | (~spl2_3 | ~spl2_20 | ~spl2_42 | ~spl2_63 | ~spl2_69)),
% 3.91/0.88    inference(backward_demodulation,[],[f2163,f4763])).
% 3.91/0.88  fof(f4763,plain,(
% 3.91/0.88    k2_pre_topc(sK0,sK1) = k4_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_20 | ~spl2_42 | ~spl2_63 | ~spl2_69)),
% 3.91/0.88    inference(backward_demodulation,[],[f4760,f649])).
% 3.91/0.88  fof(f649,plain,(
% 3.91/0.88    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_20),
% 3.91/0.88    inference(avatar_component_clause,[],[f647])).
% 3.91/0.88  fof(f647,plain,(
% 3.91/0.88    spl2_20 <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 3.91/0.88    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 3.91/0.88  fof(f4760,plain,(
% 3.91/0.88    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k4_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_42 | ~spl2_63 | ~spl2_69)),
% 3.91/0.88    inference(forward_demodulation,[],[f4729,f2163])).
% 3.91/0.88  fof(f4729,plain,(
% 3.91/0.88    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k7_subset_1(sK1,k2_tops_1(sK0,sK1),sK1)) | (~spl2_3 | ~spl2_42 | ~spl2_69)),
% 3.91/0.88    inference(forward_demodulation,[],[f4651,f1544])).
% 3.91/0.88  fof(f1544,plain,(
% 3.91/0.88    ( ! [X0] : (k7_subset_1(sK1,k2_tops_1(sK0,sK1),X0) = k7_subset_1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X0)) ) | ~spl2_42),
% 3.91/0.88    inference(unit_resulting_resolution,[],[f1441,f271])).
% 3.91/0.88  fof(f271,plain,(
% 3.91/0.88    ( ! [X4,X2,X3] : (~r1_tarski(X3,X2) | k7_subset_1(X3,X3,X4) = k7_subset_1(X2,X3,X4)) )),
% 3.91/0.88    inference(forward_demodulation,[],[f247,f245])).
% 3.91/0.88  fof(f247,plain,(
% 3.91/0.88    ( ! [X4,X2,X3] : (k5_xboole_0(X3,k3_xboole_0(X3,X4)) = k7_subset_1(X2,X3,X4) | ~r1_tarski(X3,X2)) )),
% 3.91/0.88    inference(resolution,[],[f91,f81])).
% 3.91/0.88  fof(f4651,plain,(
% 3.91/0.88    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k7_subset_1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1)) | (~spl2_3 | ~spl2_69)),
% 3.91/0.88    inference(resolution,[],[f2801,f1179])).
% 3.91/0.88  fof(f1179,plain,(
% 3.91/0.88    ( ! [X14] : (~r1_tarski(X14,u1_struct_0(sK0)) | k4_subset_1(u1_struct_0(sK0),sK1,X14) = k5_xboole_0(sK1,k7_subset_1(X14,X14,sK1))) ) | ~spl2_3),
% 3.91/0.88    inference(resolution,[],[f347,f110])).
% 3.91/0.88  fof(f110,plain,(
% 3.91/0.88    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 3.91/0.88    inference(avatar_component_clause,[],[f108])).
% 3.91/0.88  fof(f108,plain,(
% 3.91/0.88    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.91/0.88    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 3.91/0.88  fof(f347,plain,(
% 3.91/0.88    ( ! [X4,X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(X2)) | k4_subset_1(X2,X3,X4) = k5_xboole_0(X3,k7_subset_1(X4,X4,X3)) | ~r1_tarski(X4,X2)) )),
% 3.91/0.88    inference(resolution,[],[f255,f81])).
% 3.91/0.88  fof(f2801,plain,(
% 3.91/0.88    r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) | ~spl2_69),
% 3.91/0.88    inference(avatar_component_clause,[],[f2799])).
% 3.91/0.88  fof(f2163,plain,(
% 3.91/0.88    k4_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k7_subset_1(sK1,k2_tops_1(sK0,sK1),sK1)) | ~spl2_63),
% 3.91/0.88    inference(avatar_component_clause,[],[f2161])).
% 3.91/0.88  fof(f2161,plain,(
% 3.91/0.88    spl2_63 <=> k4_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k7_subset_1(sK1,k2_tops_1(sK0,sK1),sK1))),
% 3.91/0.88    introduced(avatar_definition,[new_symbols(naming,[spl2_63])])).
% 3.91/0.88  fof(f687,plain,(
% 3.91/0.88    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~spl2_25),
% 3.91/0.88    inference(avatar_component_clause,[],[f685])).
% 3.91/0.88  fof(f685,plain,(
% 3.91/0.88    spl2_25 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 3.91/0.88    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 3.91/0.88  fof(f4684,plain,(
% 3.91/0.88    ~spl2_4 | spl2_5 | ~spl2_8 | ~spl2_20 | ~spl2_42 | ~spl2_69 | ~spl2_78),
% 3.91/0.88    inference(avatar_contradiction_clause,[],[f4683])).
% 3.91/0.88  fof(f4683,plain,(
% 3.91/0.88    $false | (~spl2_4 | spl2_5 | ~spl2_8 | ~spl2_20 | ~spl2_42 | ~spl2_69 | ~spl2_78)),
% 3.91/0.88    inference(subsumption_resolution,[],[f4682,f149])).
% 3.91/0.88  fof(f149,plain,(
% 3.91/0.88    ~v4_pre_topc(sK1,sK0) | spl2_5),
% 3.91/0.88    inference(avatar_component_clause,[],[f148])).
% 3.91/0.88  fof(f148,plain,(
% 3.91/0.88    spl2_5 <=> v4_pre_topc(sK1,sK0)),
% 3.91/0.88    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 3.91/0.88  fof(f4682,plain,(
% 3.91/0.88    v4_pre_topc(sK1,sK0) | (~spl2_4 | ~spl2_8 | ~spl2_20 | ~spl2_42 | ~spl2_69 | ~spl2_78)),
% 3.91/0.88    inference(backward_demodulation,[],[f302,f4680])).
% 3.91/0.88  fof(f4680,plain,(
% 3.91/0.88    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_4 | ~spl2_20 | ~spl2_42 | ~spl2_69 | ~spl2_78)),
% 3.91/0.88    inference(backward_demodulation,[],[f649,f4679])).
% 3.91/0.88  fof(f4679,plain,(
% 3.91/0.88    sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_4 | ~spl2_42 | ~spl2_69 | ~spl2_78)),
% 3.91/0.88    inference(forward_demodulation,[],[f4678,f4503])).
% 3.91/0.88  fof(f4503,plain,(
% 3.91/0.88    sK1 = k5_xboole_0(sK1,k7_subset_1(sK1,k2_tops_1(sK0,sK1),sK1)) | ~spl2_78),
% 3.91/0.88    inference(avatar_component_clause,[],[f4501])).
% 3.91/0.88  fof(f4501,plain,(
% 3.91/0.88    spl2_78 <=> sK1 = k5_xboole_0(sK1,k7_subset_1(sK1,k2_tops_1(sK0,sK1),sK1))),
% 3.91/0.88    introduced(avatar_definition,[new_symbols(naming,[spl2_78])])).
% 3.91/0.88  fof(f4678,plain,(
% 3.91/0.88    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k7_subset_1(sK1,k2_tops_1(sK0,sK1),sK1)) | (~spl2_4 | ~spl2_42 | ~spl2_69)),
% 3.91/0.88    inference(forward_demodulation,[],[f4641,f1544])).
% 3.91/0.88  fof(f4641,plain,(
% 3.91/0.88    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k7_subset_1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1)) | (~spl2_4 | ~spl2_69)),
% 3.91/0.88    inference(unit_resulting_resolution,[],[f121,f2801,f1174])).
% 3.91/0.88  fof(f1174,plain,(
% 3.91/0.88    ( ! [X4,X2,X3] : (~r1_tarski(X4,X2) | k4_subset_1(X2,X3,X4) = k5_xboole_0(X3,k7_subset_1(X4,X4,X3)) | ~r1_tarski(X3,X2)) )),
% 3.91/0.88    inference(resolution,[],[f347,f81])).
% 3.91/0.88  fof(f302,plain,(
% 3.91/0.88    v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) | ~spl2_8),
% 3.91/0.88    inference(avatar_component_clause,[],[f300])).
% 3.91/0.88  fof(f300,plain,(
% 3.91/0.88    spl2_8 <=> v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)),
% 3.91/0.88    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 3.91/0.88  fof(f4504,plain,(
% 3.91/0.88    spl2_78 | ~spl2_41 | ~spl2_63),
% 3.91/0.88    inference(avatar_split_clause,[],[f4499,f2161,f1430,f4501])).
% 3.91/0.88  fof(f1430,plain,(
% 3.91/0.88    spl2_41 <=> k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))),
% 3.91/0.88    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).
% 3.91/0.88  fof(f4499,plain,(
% 3.91/0.88    sK1 = k5_xboole_0(sK1,k7_subset_1(sK1,k2_tops_1(sK0,sK1),sK1)) | (~spl2_41 | ~spl2_63)),
% 3.91/0.88    inference(backward_demodulation,[],[f2163,f4490])).
% 3.91/0.88  fof(f4490,plain,(
% 3.91/0.88    sK1 = k4_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) | ~spl2_41),
% 3.91/0.88    inference(superposition,[],[f4460,f1432])).
% 3.91/0.88  fof(f1432,plain,(
% 3.91/0.88    k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) | ~spl2_41),
% 3.91/0.88    inference(avatar_component_clause,[],[f1430])).
% 3.91/0.88  fof(f2802,plain,(
% 3.91/0.88    spl2_69 | ~spl2_4 | ~spl2_41),
% 3.91/0.88    inference(avatar_split_clause,[],[f1514,f1430,f119,f2799])).
% 3.91/0.88  fof(f1514,plain,(
% 3.91/0.88    r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) | (~spl2_4 | ~spl2_41)),
% 3.91/0.88    inference(superposition,[],[f264,f1432])).
% 3.91/0.88  fof(f264,plain,(
% 3.91/0.88    ( ! [X0] : (r1_tarski(k7_subset_1(sK1,sK1,X0),u1_struct_0(sK0))) ) | ~spl2_4),
% 3.91/0.88    inference(backward_demodulation,[],[f143,f245])).
% 3.91/0.88  fof(f143,plain,(
% 3.91/0.88    ( ! [X0] : (r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),u1_struct_0(sK0))) ) | ~spl2_4),
% 3.91/0.88    inference(unit_resulting_resolution,[],[f88,f121,f84])).
% 3.91/0.88  fof(f2164,plain,(
% 3.91/0.88    spl2_63 | ~spl2_42),
% 3.91/0.88    inference(avatar_split_clause,[],[f1559,f1439,f2161])).
% 3.91/0.88  fof(f1559,plain,(
% 3.91/0.88    k4_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k7_subset_1(sK1,k2_tops_1(sK0,sK1),sK1)) | ~spl2_42),
% 3.91/0.88    inference(backward_demodulation,[],[f1545,f1544])).
% 3.91/0.88  fof(f1545,plain,(
% 3.91/0.88    k4_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k7_subset_1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1)) | ~spl2_42),
% 3.91/0.88    inference(unit_resulting_resolution,[],[f95,f1441,f347])).
% 3.91/0.88  fof(f1665,plain,(
% 3.91/0.88    spl2_55 | ~spl2_42),
% 3.91/0.88    inference(avatar_split_clause,[],[f1543,f1439,f1662])).
% 3.91/0.88  fof(f1543,plain,(
% 3.91/0.88    k3_subset_1(sK1,k2_tops_1(sK0,sK1)) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) | ~spl2_42),
% 3.91/0.88    inference(unit_resulting_resolution,[],[f1441,f262])).
% 3.91/0.88  fof(f262,plain,(
% 3.91/0.88    ( ! [X2,X1] : (~r1_tarski(X2,X1) | k3_subset_1(X1,X2) = k7_subset_1(X1,X1,X2)) )),
% 3.91/0.88    inference(backward_demodulation,[],[f222,f245])).
% 3.91/0.88  fof(f222,plain,(
% 3.91/0.88    ( ! [X2,X1] : (k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_subset_1(X1,X2) | ~r1_tarski(X2,X1)) )),
% 3.91/0.88    inference(resolution,[],[f90,f81])).
% 3.91/0.88  fof(f1625,plain,(
% 3.91/0.88    spl2_51 | ~spl2_42),
% 3.91/0.88    inference(avatar_split_clause,[],[f1540,f1439,f1622])).
% 3.91/0.88  fof(f1540,plain,(
% 3.91/0.88    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) | ~spl2_42),
% 3.91/0.88    inference(unit_resulting_resolution,[],[f1441,f172])).
% 3.91/0.88  fof(f172,plain,(
% 3.91/0.88    ( ! [X2,X1] : (~r1_tarski(X2,X1) | k3_subset_1(X1,k3_subset_1(X1,X2)) = X2) )),
% 3.91/0.88    inference(resolution,[],[f74,f81])).
% 3.91/0.88  fof(f1528,plain,(
% 3.91/0.88    spl2_42 | ~spl2_41),
% 3.91/0.88    inference(avatar_split_clause,[],[f1515,f1430,f1439])).
% 3.91/0.88  fof(f1515,plain,(
% 3.91/0.88    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_41),
% 3.91/0.88    inference(superposition,[],[f251,f1432])).
% 3.91/0.88  fof(f251,plain,(
% 3.91/0.88    ( ! [X0,X1] : (r1_tarski(k7_subset_1(X0,X0,X1),X0)) )),
% 3.91/0.88    inference(backward_demodulation,[],[f88,f245])).
% 3.91/0.88  fof(f1442,plain,(
% 3.91/0.88    spl2_42 | ~spl2_2 | ~spl2_3 | ~spl2_5),
% 3.91/0.88    inference(avatar_split_clause,[],[f1436,f148,f108,f103,f1439])).
% 3.91/0.88  fof(f103,plain,(
% 3.91/0.88    spl2_2 <=> l1_pre_topc(sK0)),
% 3.91/0.88    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 3.91/0.88  fof(f1436,plain,(
% 3.91/0.88    r1_tarski(k2_tops_1(sK0,sK1),sK1) | (~spl2_2 | ~spl2_3 | ~spl2_5)),
% 3.91/0.88    inference(unit_resulting_resolution,[],[f105,f110,f150,f66])).
% 3.91/0.88  fof(f66,plain,(
% 3.91/0.88    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k2_tops_1(X0,X1),X1)) )),
% 3.91/0.88    inference(cnf_transformation,[],[f31])).
% 3.91/0.88  fof(f31,plain,(
% 3.91/0.88    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.91/0.88    inference(flattening,[],[f30])).
% 3.91/0.88  fof(f30,plain,(
% 3.91/0.88    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.91/0.88    inference(ennf_transformation,[],[f23])).
% 3.91/0.88  fof(f23,axiom,(
% 3.91/0.88    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 3.91/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).
% 3.91/0.88  fof(f150,plain,(
% 3.91/0.88    v4_pre_topc(sK1,sK0) | ~spl2_5),
% 3.91/0.88    inference(avatar_component_clause,[],[f148])).
% 3.91/0.88  fof(f105,plain,(
% 3.91/0.88    l1_pre_topc(sK0) | ~spl2_2),
% 3.91/0.88    inference(avatar_component_clause,[],[f103])).
% 3.91/0.88  fof(f1433,plain,(
% 3.91/0.88    spl2_41 | ~spl2_3 | ~spl2_6),
% 3.91/0.88    inference(avatar_split_clause,[],[f586,f152,f108,f1430])).
% 3.91/0.88  fof(f586,plain,(
% 3.91/0.88    k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_6)),
% 3.91/0.88    inference(superposition,[],[f270,f154])).
% 3.91/0.88  fof(f154,plain,(
% 3.91/0.88    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_6),
% 3.91/0.88    inference(avatar_component_clause,[],[f152])).
% 3.91/0.88  fof(f270,plain,(
% 3.91/0.88    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)) ) | ~spl2_3),
% 3.91/0.88    inference(forward_demodulation,[],[f243,f245])).
% 3.91/0.88  fof(f243,plain,(
% 3.91/0.88    ( ! [X0] : (k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) = k7_subset_1(u1_struct_0(sK0),sK1,X0)) ) | ~spl2_3),
% 3.91/0.88    inference(unit_resulting_resolution,[],[f110,f91])).
% 3.91/0.88  fof(f688,plain,(
% 3.91/0.88    spl2_25 | ~spl2_2 | ~spl2_3),
% 3.91/0.88    inference(avatar_split_clause,[],[f369,f108,f103,f685])).
% 3.91/0.88  fof(f369,plain,(
% 3.91/0.88    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3)),
% 3.91/0.88    inference(unit_resulting_resolution,[],[f105,f110,f65])).
% 3.91/0.88  fof(f65,plain,(
% 3.91/0.88    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))) )),
% 3.91/0.88    inference(cnf_transformation,[],[f29])).
% 3.91/0.88  fof(f29,plain,(
% 3.91/0.88    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.91/0.88    inference(ennf_transformation,[],[f21])).
% 3.91/0.88  fof(f21,axiom,(
% 3.91/0.88    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 3.91/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 3.91/0.88  fof(f650,plain,(
% 3.91/0.88    spl2_20 | ~spl2_2 | ~spl2_3),
% 3.91/0.88    inference(avatar_split_clause,[],[f328,f108,f103,f647])).
% 3.91/0.88  fof(f328,plain,(
% 3.91/0.88    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3)),
% 3.91/0.88    inference(unit_resulting_resolution,[],[f105,f110,f64])).
% 3.91/0.88  fof(f64,plain,(
% 3.91/0.88    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 3.91/0.88    inference(cnf_transformation,[],[f28])).
% 3.91/0.88  fof(f28,plain,(
% 3.91/0.88    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.91/0.88    inference(ennf_transformation,[],[f22])).
% 3.91/0.88  fof(f22,axiom,(
% 3.91/0.88    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 3.91/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 3.91/0.88  fof(f303,plain,(
% 3.91/0.88    spl2_8 | ~spl2_1 | ~spl2_2 | ~spl2_3),
% 3.91/0.88    inference(avatar_split_clause,[],[f238,f108,f103,f98,f300])).
% 3.91/0.88  fof(f98,plain,(
% 3.91/0.88    spl2_1 <=> v2_pre_topc(sK0)),
% 3.91/0.88    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 3.91/0.88  fof(f238,plain,(
% 3.91/0.88    v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) | (~spl2_1 | ~spl2_2 | ~spl2_3)),
% 3.91/0.88    inference(unit_resulting_resolution,[],[f100,f105,f110,f76])).
% 3.91/0.88  fof(f76,plain,(
% 3.91/0.88    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~v2_pre_topc(X0)) )),
% 3.91/0.88    inference(cnf_transformation,[],[f39])).
% 3.91/0.88  fof(f39,plain,(
% 3.91/0.88    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.91/0.88    inference(flattening,[],[f38])).
% 3.91/0.88  fof(f38,plain,(
% 3.91/0.88    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.91/0.88    inference(ennf_transformation,[],[f20])).
% 3.91/0.88  fof(f20,axiom,(
% 3.91/0.88    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 3.91/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).
% 3.91/0.88  fof(f100,plain,(
% 3.91/0.88    v2_pre_topc(sK0) | ~spl2_1),
% 3.91/0.88    inference(avatar_component_clause,[],[f98])).
% 3.91/0.88  fof(f158,plain,(
% 3.91/0.88    ~spl2_5 | ~spl2_6),
% 3.91/0.88    inference(avatar_split_clause,[],[f157,f152,f148])).
% 3.91/0.88  fof(f157,plain,(
% 3.91/0.88    ~v4_pre_topc(sK1,sK0) | ~spl2_6),
% 3.91/0.88    inference(trivial_inequality_removal,[],[f156])).
% 3.91/0.88  fof(f156,plain,(
% 3.91/0.88    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0) | ~spl2_6),
% 3.91/0.88    inference(backward_demodulation,[],[f59,f154])).
% 3.91/0.88  fof(f59,plain,(
% 3.91/0.88    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 3.91/0.88    inference(cnf_transformation,[],[f51])).
% 3.91/0.88  fof(f51,plain,(
% 3.91/0.88    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.91/0.88    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f48,f50,f49])).
% 3.91/0.88  fof(f49,plain,(
% 3.91/0.88    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.91/0.88    introduced(choice_axiom,[])).
% 3.91/0.88  fof(f50,plain,(
% 3.91/0.88    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 3.91/0.88    introduced(choice_axiom,[])).
% 3.91/0.88  fof(f48,plain,(
% 3.91/0.88    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.91/0.88    inference(flattening,[],[f47])).
% 3.91/0.88  fof(f47,plain,(
% 3.91/0.88    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.91/0.88    inference(nnf_transformation,[],[f27])).
% 3.91/0.88  fof(f27,plain,(
% 3.91/0.88    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.91/0.88    inference(flattening,[],[f26])).
% 3.91/0.88  fof(f26,plain,(
% 3.91/0.88    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.91/0.88    inference(ennf_transformation,[],[f25])).
% 3.91/0.88  fof(f25,negated_conjecture,(
% 3.91/0.88    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 3.91/0.88    inference(negated_conjecture,[],[f24])).
% 3.91/0.88  fof(f24,conjecture,(
% 3.91/0.88    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 3.91/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).
% 3.91/0.88  fof(f155,plain,(
% 3.91/0.88    spl2_5 | spl2_6),
% 3.91/0.88    inference(avatar_split_clause,[],[f58,f152,f148])).
% 3.91/0.88  fof(f58,plain,(
% 3.91/0.88    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 3.91/0.88    inference(cnf_transformation,[],[f51])).
% 3.91/0.88  fof(f122,plain,(
% 3.91/0.88    spl2_4 | ~spl2_3),
% 3.91/0.88    inference(avatar_split_clause,[],[f112,f108,f119])).
% 3.91/0.88  fof(f112,plain,(
% 3.91/0.88    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl2_3),
% 3.91/0.88    inference(unit_resulting_resolution,[],[f110,f80])).
% 3.91/0.88  fof(f111,plain,(
% 3.91/0.88    spl2_3),
% 3.91/0.88    inference(avatar_split_clause,[],[f57,f108])).
% 3.91/0.88  fof(f57,plain,(
% 3.91/0.88    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.91/0.88    inference(cnf_transformation,[],[f51])).
% 3.91/0.88  fof(f106,plain,(
% 3.91/0.88    spl2_2),
% 3.91/0.88    inference(avatar_split_clause,[],[f56,f103])).
% 3.91/0.88  fof(f56,plain,(
% 3.91/0.88    l1_pre_topc(sK0)),
% 3.91/0.88    inference(cnf_transformation,[],[f51])).
% 3.91/0.88  fof(f101,plain,(
% 3.91/0.88    spl2_1),
% 3.91/0.88    inference(avatar_split_clause,[],[f55,f98])).
% 3.91/0.88  fof(f55,plain,(
% 3.91/0.88    v2_pre_topc(sK0)),
% 3.91/0.88    inference(cnf_transformation,[],[f51])).
% 3.91/0.88  % SZS output end Proof for theBenchmark
% 3.91/0.88  % (30838)------------------------------
% 3.91/0.88  % (30838)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.91/0.88  % (30838)Termination reason: Refutation
% 3.91/0.88  
% 3.91/0.88  % (30838)Memory used [KB]: 13816
% 3.91/0.88  % (30838)Time elapsed: 0.461 s
% 3.91/0.88  % (30838)------------------------------
% 3.91/0.88  % (30838)------------------------------
% 3.91/0.89  % (30814)Success in time 0.516 s
%------------------------------------------------------------------------------
