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
% DateTime   : Thu Dec  3 12:44:58 EST 2020

% Result     : Theorem 4.21s
% Output     : Refutation 4.21s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 382 expanded)
%              Number of leaves         :   30 ( 129 expanded)
%              Depth                    :   16
%              Number of atoms          :  303 ( 725 expanded)
%              Number of equality atoms :   45 ( 149 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9994,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f558,f563,f570,f752,f794,f798,f5578,f5808,f5826,f5841,f5850,f6271,f9965])).

fof(f9965,plain,
    ( ~ spl4_2
    | ~ spl4_3
    | spl4_21 ),
    inference(avatar_contradiction_clause,[],[f9901])).

fof(f9901,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_3
    | spl4_21 ),
    inference(unit_resulting_resolution,[],[f751,f9886,f7462])).

fof(f7462,plain,
    ( ! [X37] :
        ( ~ r1_tarski(k4_xboole_0(X37,sK1),sK2)
        | r1_tarski(X37,sK0) )
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(superposition,[],[f1066,f4257])).

fof(f4257,plain,
    ( ! [X38] :
        ( sK0 = k2_xboole_0(sK0,X38)
        | ~ r1_tarski(X38,sK2) )
    | ~ spl4_2 ),
    inference(resolution,[],[f97,f1777])).

fof(f1777,plain,
    ( ! [X35,X34] :
        ( r1_tarski(k4_xboole_0(X34,X35),sK0)
        | ~ r1_tarski(X34,sK2) )
    | ~ spl4_2 ),
    inference(resolution,[],[f278,f127])).

fof(f127,plain,
    ( ! [X7] :
        ( ~ r1_tarski(X7,sK2)
        | r1_tarski(X7,sK0) )
    | ~ spl4_2 ),
    inference(resolution,[],[f53,f83])).

fof(f83,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl4_2 ),
    inference(resolution,[],[f76,f58])).

fof(f58,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f76,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl4_2
  <=> r2_hidden(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f278,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X1,X2),X0)
      | ~ r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f171,f87])).

fof(f87,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,X2) = X3
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f42,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f171,plain,(
    ! [X4,X2,X3] : r1_tarski(k4_xboole_0(X2,X3),k2_xboole_0(X4,X2)) ),
    inference(resolution,[],[f52,f149])).

fof(f149,plain,(
    ! [X4,X5,X3] : r1_tarski(k4_xboole_0(k4_xboole_0(X3,X4),X5),X3) ),
    inference(resolution,[],[f126,f33])).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f126,plain,(
    ! [X6,X4,X5] :
      ( ~ r1_tarski(X4,k4_xboole_0(X5,X6))
      | r1_tarski(X4,X5) ) ),
    inference(resolution,[],[f53,f33])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f97,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k4_xboole_0(X3,X2),X2)
      | k2_xboole_0(X2,X3) = X2 ) ),
    inference(superposition,[],[f37,f87])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f1066,plain,
    ( ! [X0] : r1_tarski(X0,k2_xboole_0(sK0,k4_xboole_0(X0,sK1)))
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f1055,f35])).

fof(f1055,plain,
    ( ! [X0] : r1_tarski(X0,k2_xboole_0(k4_xboole_0(X0,sK1),sK0))
    | ~ spl4_3 ),
    inference(resolution,[],[f984,f52])).

fof(f984,plain,
    ( ! [X3] : r1_tarski(k4_xboole_0(X3,k4_xboole_0(X3,sK1)),sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f801,f328])).

fof(f328,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(superposition,[],[f33,f55])).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f34,f36,f36])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f801,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | r1_tarski(X0,sK0) )
    | ~ spl4_3 ),
    inference(resolution,[],[f799,f53])).

fof(f799,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f81,f58])).

fof(f81,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl4_3
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f9886,plain,(
    ! [X14,X15] : r1_tarski(k4_xboole_0(k2_xboole_0(X14,X15),X14),X15) ),
    inference(forward_demodulation,[],[f9810,f4294])).

fof(f4294,plain,(
    ! [X3] : k2_xboole_0(X3,k1_xboole_0) = X3 ),
    inference(superposition,[],[f4232,f1922])).

fof(f1922,plain,(
    ! [X43] : k2_xboole_0(X43,X43) = k2_xboole_0(X43,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1893,f131])).

fof(f131,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f101,f33])).

fof(f101,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f46,f32])).

fof(f32,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1893,plain,(
    ! [X43] : k2_xboole_0(X43,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X43))) = k2_xboole_0(X43,X43) ),
    inference(superposition,[],[f370,f1838])).

fof(f1838,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(resolution,[],[f1801,f103])).

fof(f103,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,k4_xboole_0(X2,X3))
      | k4_xboole_0(X2,X3) = X2 ) ),
    inference(resolution,[],[f46,f33])).

fof(f1801,plain,(
    ! [X3] : r1_tarski(X3,k4_xboole_0(X3,k1_xboole_0)) ),
    inference(resolution,[],[f470,f56])).

fof(f56,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f470,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k4_xboole_0(X2,k1_xboole_0),X3)
      | r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f404,f42])).

fof(f404,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1)) ),
    inference(resolution,[],[f385,f52])).

fof(f385,plain,(
    ! [X8,X7] : r1_tarski(k4_xboole_0(X7,k4_xboole_0(X7,k1_xboole_0)),X8) ),
    inference(resolution,[],[f328,f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f53,f32])).

fof(f370,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,k4_xboole_0(X3,X2))) = k2_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f329,f35])).

fof(f329,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),X2) = k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,k4_xboole_0(X3,X2))) ),
    inference(superposition,[],[f37,f55])).

fof(f4232,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f97,f33])).

fof(f9810,plain,(
    ! [X14,X15] : r1_tarski(k4_xboole_0(k2_xboole_0(X14,X15),k2_xboole_0(X14,k1_xboole_0)),X15) ),
    inference(superposition,[],[f402,f1867])).

fof(f1867,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2) ),
    inference(superposition,[],[f386,f1838])).

fof(f386,plain,(
    ! [X9] : k1_xboole_0 = k4_xboole_0(X9,k4_xboole_0(X9,k1_xboole_0)) ),
    inference(resolution,[],[f328,f101])).

fof(f402,plain,(
    ! [X2,X3,X1] : r1_tarski(k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X3)))),X3) ),
    inference(forward_demodulation,[],[f392,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f392,plain,(
    ! [X2,X3,X1] : r1_tarski(k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k2_xboole_0(X2,X3))),X3) ),
    inference(superposition,[],[f328,f51])).

fof(f751,plain,
    ( ~ r1_tarski(k2_xboole_0(sK1,sK2),sK0)
    | spl4_21 ),
    inference(avatar_component_clause,[],[f749])).

fof(f749,plain,
    ( spl4_21
  <=> r1_tarski(k2_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f6271,plain,
    ( spl4_57
    | ~ spl4_73 ),
    inference(avatar_contradiction_clause,[],[f6258])).

fof(f6258,plain,
    ( $false
    | spl4_57
    | ~ spl4_73 ),
    inference(unit_resulting_resolution,[],[f56,f256,f5858,f53])).

fof(f5858,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1))
    | spl4_57
    | ~ spl4_73 ),
    inference(forward_demodulation,[],[f5577,f5836])).

fof(f5836,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl4_73 ),
    inference(avatar_component_clause,[],[f5834])).

fof(f5834,plain,
    ( spl4_73
  <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_73])])).

fof(f5577,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_subset_1(sK0,sK1))
    | spl4_57 ),
    inference(avatar_component_clause,[],[f5575])).

fof(f5575,plain,
    ( spl4_57
  <=> r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).

fof(f256,plain,(
    ! [X24,X23,X22] : r1_tarski(k4_xboole_0(X22,k2_xboole_0(X23,X24)),k4_xboole_0(X22,X23)) ),
    inference(superposition,[],[f33,f51])).

fof(f5850,plain,
    ( ~ spl4_10
    | ~ spl4_72
    | spl4_74 ),
    inference(avatar_split_clause,[],[f5849,f5838,f5805,f226])).

fof(f226,plain,
    ( spl4_10
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f5805,plain,
    ( spl4_72
  <=> r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).

fof(f5838,plain,
    ( spl4_74
  <=> r1_tarski(k4_xboole_0(sK0,sK1),k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).

fof(f5849,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl4_74 ),
    inference(superposition,[],[f5840,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f5840,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),k3_subset_1(sK0,sK1))
    | spl4_74 ),
    inference(avatar_component_clause,[],[f5838])).

fof(f5841,plain,
    ( spl4_73
    | ~ spl4_74
    | ~ spl4_56 ),
    inference(avatar_split_clause,[],[f5829,f5570,f5838,f5834])).

fof(f5570,plain,
    ( spl4_56
  <=> r1_tarski(k3_subset_1(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f5829,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),k3_subset_1(sK0,sK1))
    | k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl4_56 ),
    inference(resolution,[],[f5571,f46])).

fof(f5571,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),k4_xboole_0(sK0,sK1))
    | ~ spl4_56 ),
    inference(avatar_component_clause,[],[f5570])).

fof(f5826,plain,(
    spl4_72 ),
    inference(avatar_contradiction_clause,[],[f5814])).

fof(f5814,plain,
    ( $false
    | spl4_72 ),
    inference(unit_resulting_resolution,[],[f33,f5807,f470])).

fof(f5807,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))
    | spl4_72 ),
    inference(avatar_component_clause,[],[f5805])).

fof(f5808,plain,
    ( ~ spl4_10
    | ~ spl4_72
    | spl4_56 ),
    inference(avatar_split_clause,[],[f5801,f5570,f5805,f226])).

fof(f5801,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl4_56 ),
    inference(superposition,[],[f5572,f43])).

fof(f5572,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),k4_xboole_0(sK0,sK1))
    | spl4_56 ),
    inference(avatar_component_clause,[],[f5570])).

fof(f5578,plain,
    ( ~ spl4_13
    | ~ spl4_57
    | spl4_14 ),
    inference(avatar_split_clause,[],[f588,f555,f5575,f550])).

fof(f550,plain,
    ( spl4_13
  <=> m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f555,plain,
    ( spl4_14
  <=> r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f588,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_subset_1(sK0,sK1))
    | ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | spl4_14 ),
    inference(superposition,[],[f557,f43])).

fof(f557,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k3_subset_1(sK0,sK1))
    | spl4_14 ),
    inference(avatar_component_clause,[],[f555])).

fof(f798,plain,(
    ~ spl4_1 ),
    inference(avatar_contradiction_clause,[],[f795])).

fof(f795,plain,
    ( $false
    | ~ spl4_1 ),
    inference(unit_resulting_resolution,[],[f31,f72])).

fof(f72,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl4_1
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f31,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f794,plain,
    ( spl4_1
    | spl4_3 ),
    inference(avatar_split_clause,[],[f564,f79,f70])).

fof(f564,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f30,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).

fof(f752,plain,
    ( ~ spl4_21
    | spl4_1
    | spl4_13 ),
    inference(avatar_split_clause,[],[f741,f550,f70,f749])).

fof(f741,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ r1_tarski(k2_xboole_0(sK1,sK2),sK0)
    | spl4_13 ),
    inference(resolution,[],[f65,f552])).

fof(f552,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | spl4_13 ),
    inference(avatar_component_clause,[],[f550])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(k1_zfmisc_1(X0))
      | ~ r1_tarski(X1,X0) ) ),
    inference(resolution,[],[f40,f59])).

fof(f59,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f570,plain,(
    spl4_12 ),
    inference(avatar_contradiction_clause,[],[f566])).

fof(f566,plain,
    ( $false
    | spl4_12 ),
    inference(subsumption_resolution,[],[f28,f548])).

fof(f548,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | spl4_12 ),
    inference(avatar_component_clause,[],[f546])).

fof(f546,plain,
    ( spl4_12
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f563,plain,(
    spl4_10 ),
    inference(avatar_contradiction_clause,[],[f559])).

fof(f559,plain,
    ( $false
    | spl4_10 ),
    inference(subsumption_resolution,[],[f30,f228])).

fof(f228,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl4_10 ),
    inference(avatar_component_clause,[],[f226])).

fof(f558,plain,
    ( ~ spl4_10
    | ~ spl4_12
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f544,f555,f546,f226])).

fof(f544,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k3_subset_1(sK0,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f29,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f29,plain,(
    ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f77,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f66,f74,f70])).

fof(f66,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f41,f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:23:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.49  % (13542)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.49  % (13539)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (13534)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.50  % (13538)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (13547)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.20/0.51  % (13546)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.20/0.51  % (13537)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.20/0.51  % (13536)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.20/0.51  % (13543)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.20/0.52  % (13550)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.20/0.52  % (13556)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.20/0.52  % (13534)Refutation not found, incomplete strategy% (13534)------------------------------
% 1.20/0.52  % (13534)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.52  % (13548)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.20/0.52  % (13554)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.20/0.52  % (13533)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.20/0.52  % (13562)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.20/0.52  % (13545)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.20/0.52  % (13555)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.30/0.53  % (13534)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.53  
% 1.30/0.53  % (13534)Memory used [KB]: 1663
% 1.30/0.53  % (13534)Time elapsed: 0.117 s
% 1.30/0.53  % (13534)------------------------------
% 1.30/0.53  % (13534)------------------------------
% 1.30/0.53  % (13553)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.30/0.53  % (13540)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.30/0.53  % (13557)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.30/0.53  % (13560)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.30/0.53  % (13549)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.30/0.53  % (13535)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.30/0.54  % (13552)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.30/0.54  % (13541)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.30/0.55  % (13559)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.30/0.55  % (13558)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.30/0.55  % (13544)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.30/0.55  % (13559)Refutation not found, incomplete strategy% (13559)------------------------------
% 1.30/0.55  % (13559)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.55  % (13559)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.55  
% 1.30/0.55  % (13559)Memory used [KB]: 6268
% 1.30/0.55  % (13559)Time elapsed: 0.141 s
% 1.30/0.55  % (13559)------------------------------
% 1.30/0.55  % (13559)------------------------------
% 1.30/0.55  % (13551)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.30/0.56  % (13561)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 2.03/0.64  % (13568)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.03/0.67  % (13569)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.03/0.68  % (13536)Refutation not found, incomplete strategy% (13536)------------------------------
% 2.03/0.68  % (13536)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.03/0.68  % (13536)Termination reason: Refutation not found, incomplete strategy
% 2.03/0.68  
% 2.03/0.68  % (13536)Memory used [KB]: 6268
% 2.03/0.68  % (13536)Time elapsed: 0.271 s
% 2.03/0.68  % (13536)------------------------------
% 2.03/0.68  % (13536)------------------------------
% 3.06/0.80  % (13535)Time limit reached!
% 3.06/0.80  % (13535)------------------------------
% 3.06/0.80  % (13535)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.06/0.80  % (13535)Termination reason: Time limit
% 3.06/0.80  % (13535)Termination phase: Saturation
% 3.06/0.80  
% 3.06/0.80  % (13535)Memory used [KB]: 6908
% 3.06/0.80  % (13535)Time elapsed: 0.400 s
% 3.06/0.80  % (13535)------------------------------
% 3.06/0.80  % (13535)------------------------------
% 3.06/0.81  % (13557)Time limit reached!
% 3.06/0.81  % (13557)------------------------------
% 3.06/0.81  % (13557)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.06/0.81  % (13557)Termination reason: Time limit
% 3.06/0.81  
% 3.06/0.81  % (13557)Memory used [KB]: 11769
% 3.06/0.81  % (13557)Time elapsed: 0.401 s
% 3.06/0.81  % (13557)------------------------------
% 3.06/0.81  % (13557)------------------------------
% 3.06/0.81  % (13576)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 3.06/0.83  % (13576)Refutation not found, incomplete strategy% (13576)------------------------------
% 3.06/0.83  % (13576)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.06/0.83  % (13576)Termination reason: Refutation not found, incomplete strategy
% 3.06/0.83  
% 3.06/0.83  % (13576)Memory used [KB]: 6268
% 3.06/0.83  % (13576)Time elapsed: 0.122 s
% 3.06/0.83  % (13576)------------------------------
% 3.06/0.83  % (13576)------------------------------
% 3.83/0.90  % (13547)Time limit reached!
% 3.83/0.90  % (13547)------------------------------
% 3.83/0.90  % (13547)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.83/0.90  % (13547)Termination reason: Time limit
% 3.83/0.90  % (13547)Termination phase: Saturation
% 3.83/0.90  
% 3.83/0.90  % (13547)Memory used [KB]: 3965
% 3.83/0.90  % (13547)Time elapsed: 0.500 s
% 3.83/0.90  % (13547)------------------------------
% 3.83/0.90  % (13547)------------------------------
% 3.98/0.90  % (13539)Time limit reached!
% 3.98/0.90  % (13539)------------------------------
% 3.98/0.90  % (13539)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.98/0.91  % (13539)Termination reason: Time limit
% 3.98/0.91  % (13539)Termination phase: Saturation
% 3.98/0.91  
% 3.98/0.91  % (13539)Memory used [KB]: 15607
% 3.98/0.91  % (13539)Time elapsed: 0.500 s
% 3.98/0.91  % (13539)------------------------------
% 3.98/0.91  % (13539)------------------------------
% 3.98/0.92  % (13562)Time limit reached!
% 3.98/0.92  % (13562)------------------------------
% 3.98/0.92  % (13562)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.21/0.93  % (13562)Termination reason: Time limit
% 4.21/0.93  
% 4.21/0.93  % (13562)Memory used [KB]: 2046
% 4.21/0.93  % (13562)Time elapsed: 0.516 s
% 4.21/0.93  % (13562)------------------------------
% 4.21/0.93  % (13562)------------------------------
% 4.21/0.93  % (13577)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 4.21/0.93  % (13578)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 4.21/0.97  % (13579)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 4.21/1.00  % (13546)Refutation found. Thanks to Tanya!
% 4.21/1.00  % SZS status Theorem for theBenchmark
% 4.21/1.01  % SZS output start Proof for theBenchmark
% 4.21/1.01  fof(f9994,plain,(
% 4.21/1.01    $false),
% 4.21/1.01    inference(avatar_sat_refutation,[],[f77,f558,f563,f570,f752,f794,f798,f5578,f5808,f5826,f5841,f5850,f6271,f9965])).
% 4.21/1.01  fof(f9965,plain,(
% 4.21/1.01    ~spl4_2 | ~spl4_3 | spl4_21),
% 4.21/1.01    inference(avatar_contradiction_clause,[],[f9901])).
% 4.21/1.01  fof(f9901,plain,(
% 4.21/1.01    $false | (~spl4_2 | ~spl4_3 | spl4_21)),
% 4.21/1.01    inference(unit_resulting_resolution,[],[f751,f9886,f7462])).
% 4.21/1.01  fof(f7462,plain,(
% 4.21/1.01    ( ! [X37] : (~r1_tarski(k4_xboole_0(X37,sK1),sK2) | r1_tarski(X37,sK0)) ) | (~spl4_2 | ~spl4_3)),
% 4.21/1.01    inference(superposition,[],[f1066,f4257])).
% 4.21/1.01  fof(f4257,plain,(
% 4.21/1.01    ( ! [X38] : (sK0 = k2_xboole_0(sK0,X38) | ~r1_tarski(X38,sK2)) ) | ~spl4_2),
% 4.21/1.01    inference(resolution,[],[f97,f1777])).
% 4.21/1.01  fof(f1777,plain,(
% 4.21/1.01    ( ! [X35,X34] : (r1_tarski(k4_xboole_0(X34,X35),sK0) | ~r1_tarski(X34,sK2)) ) | ~spl4_2),
% 4.21/1.01    inference(resolution,[],[f278,f127])).
% 4.21/1.01  fof(f127,plain,(
% 4.21/1.01    ( ! [X7] : (~r1_tarski(X7,sK2) | r1_tarski(X7,sK0)) ) | ~spl4_2),
% 4.21/1.01    inference(resolution,[],[f53,f83])).
% 4.21/1.01  fof(f83,plain,(
% 4.21/1.01    r1_tarski(sK2,sK0) | ~spl4_2),
% 4.21/1.01    inference(resolution,[],[f76,f58])).
% 4.21/1.01  fof(f58,plain,(
% 4.21/1.01    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 4.21/1.01    inference(equality_resolution,[],[f48])).
% 4.21/1.01  fof(f48,plain,(
% 4.21/1.01    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 4.21/1.01    inference(cnf_transformation,[],[f12])).
% 4.21/1.01  fof(f12,axiom,(
% 4.21/1.01    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 4.21/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 4.21/1.01  fof(f76,plain,(
% 4.21/1.01    r2_hidden(sK2,k1_zfmisc_1(sK0)) | ~spl4_2),
% 4.21/1.01    inference(avatar_component_clause,[],[f74])).
% 4.21/1.01  fof(f74,plain,(
% 4.21/1.01    spl4_2 <=> r2_hidden(sK2,k1_zfmisc_1(sK0))),
% 4.21/1.01    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 4.21/1.01  fof(f53,plain,(
% 4.21/1.01    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1) | r1_tarski(X0,X2)) )),
% 4.21/1.01    inference(cnf_transformation,[],[f25])).
% 4.21/1.01  fof(f25,plain,(
% 4.21/1.01    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 4.21/1.01    inference(flattening,[],[f24])).
% 4.21/1.01  fof(f24,plain,(
% 4.21/1.01    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 4.21/1.01    inference(ennf_transformation,[],[f5])).
% 4.21/1.01  fof(f5,axiom,(
% 4.21/1.01    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 4.21/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 4.21/1.02  fof(f278,plain,(
% 4.21/1.02    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X1,X2),X0) | ~r1_tarski(X1,X0)) )),
% 4.21/1.02    inference(superposition,[],[f171,f87])).
% 4.21/1.02  fof(f87,plain,(
% 4.21/1.02    ( ! [X2,X3] : (k2_xboole_0(X3,X2) = X3 | ~r1_tarski(X2,X3)) )),
% 4.21/1.02    inference(superposition,[],[f42,f35])).
% 4.21/1.02  fof(f35,plain,(
% 4.21/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 4.21/1.02    inference(cnf_transformation,[],[f1])).
% 4.21/1.02  fof(f1,axiom,(
% 4.21/1.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 4.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 4.21/1.02  fof(f42,plain,(
% 4.21/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 4.21/1.02    inference(cnf_transformation,[],[f21])).
% 4.21/1.02  fof(f21,plain,(
% 4.21/1.02    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 4.21/1.02    inference(ennf_transformation,[],[f4])).
% 4.21/1.02  fof(f4,axiom,(
% 4.21/1.02    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 4.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 4.21/1.02  fof(f171,plain,(
% 4.21/1.02    ( ! [X4,X2,X3] : (r1_tarski(k4_xboole_0(X2,X3),k2_xboole_0(X4,X2))) )),
% 4.21/1.02    inference(resolution,[],[f52,f149])).
% 4.21/1.02  fof(f149,plain,(
% 4.21/1.02    ( ! [X4,X5,X3] : (r1_tarski(k4_xboole_0(k4_xboole_0(X3,X4),X5),X3)) )),
% 4.21/1.02    inference(resolution,[],[f126,f33])).
% 4.21/1.02  fof(f33,plain,(
% 4.21/1.02    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 4.21/1.02    inference(cnf_transformation,[],[f7])).
% 4.21/1.02  fof(f7,axiom,(
% 4.21/1.02    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 4.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 4.21/1.02  fof(f126,plain,(
% 4.21/1.02    ( ! [X6,X4,X5] : (~r1_tarski(X4,k4_xboole_0(X5,X6)) | r1_tarski(X4,X5)) )),
% 4.21/1.02    inference(resolution,[],[f53,f33])).
% 4.21/1.02  fof(f52,plain,(
% 4.21/1.02    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 4.21/1.02    inference(cnf_transformation,[],[f23])).
% 4.21/1.02  fof(f23,plain,(
% 4.21/1.02    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 4.21/1.02    inference(ennf_transformation,[],[f10])).
% 4.21/1.02  fof(f10,axiom,(
% 4.21/1.02    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 4.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 4.21/1.02  fof(f97,plain,(
% 4.21/1.02    ( ! [X2,X3] : (~r1_tarski(k4_xboole_0(X3,X2),X2) | k2_xboole_0(X2,X3) = X2) )),
% 4.21/1.02    inference(superposition,[],[f37,f87])).
% 4.21/1.02  fof(f37,plain,(
% 4.21/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 4.21/1.02    inference(cnf_transformation,[],[f8])).
% 4.21/1.02  fof(f8,axiom,(
% 4.21/1.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 4.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 4.21/1.02  fof(f1066,plain,(
% 4.21/1.02    ( ! [X0] : (r1_tarski(X0,k2_xboole_0(sK0,k4_xboole_0(X0,sK1)))) ) | ~spl4_3),
% 4.21/1.02    inference(forward_demodulation,[],[f1055,f35])).
% 4.21/1.02  fof(f1055,plain,(
% 4.21/1.02    ( ! [X0] : (r1_tarski(X0,k2_xboole_0(k4_xboole_0(X0,sK1),sK0))) ) | ~spl4_3),
% 4.21/1.02    inference(resolution,[],[f984,f52])).
% 4.21/1.02  fof(f984,plain,(
% 4.21/1.02    ( ! [X3] : (r1_tarski(k4_xboole_0(X3,k4_xboole_0(X3,sK1)),sK0)) ) | ~spl4_3),
% 4.21/1.02    inference(resolution,[],[f801,f328])).
% 4.21/1.02  fof(f328,plain,(
% 4.21/1.02    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) )),
% 4.21/1.02    inference(superposition,[],[f33,f55])).
% 4.21/1.02  fof(f55,plain,(
% 4.21/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 4.21/1.02    inference(definition_unfolding,[],[f34,f36,f36])).
% 4.21/1.02  fof(f36,plain,(
% 4.21/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 4.21/1.02    inference(cnf_transformation,[],[f11])).
% 4.21/1.02  fof(f11,axiom,(
% 4.21/1.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 4.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 4.21/1.02  fof(f34,plain,(
% 4.21/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 4.21/1.02    inference(cnf_transformation,[],[f2])).
% 4.21/1.02  fof(f2,axiom,(
% 4.21/1.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 4.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 4.21/1.02  fof(f801,plain,(
% 4.21/1.02    ( ! [X0] : (~r1_tarski(X0,sK1) | r1_tarski(X0,sK0)) ) | ~spl4_3),
% 4.21/1.02    inference(resolution,[],[f799,f53])).
% 4.21/1.02  fof(f799,plain,(
% 4.21/1.02    r1_tarski(sK1,sK0) | ~spl4_3),
% 4.21/1.02    inference(resolution,[],[f81,f58])).
% 4.21/1.02  fof(f81,plain,(
% 4.21/1.02    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl4_3),
% 4.21/1.02    inference(avatar_component_clause,[],[f79])).
% 4.21/1.02  fof(f79,plain,(
% 4.21/1.02    spl4_3 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 4.21/1.02    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 4.21/1.02  fof(f9886,plain,(
% 4.21/1.02    ( ! [X14,X15] : (r1_tarski(k4_xboole_0(k2_xboole_0(X14,X15),X14),X15)) )),
% 4.21/1.02    inference(forward_demodulation,[],[f9810,f4294])).
% 4.21/1.02  fof(f4294,plain,(
% 4.21/1.02    ( ! [X3] : (k2_xboole_0(X3,k1_xboole_0) = X3) )),
% 4.21/1.02    inference(superposition,[],[f4232,f1922])).
% 4.21/1.02  fof(f1922,plain,(
% 4.21/1.02    ( ! [X43] : (k2_xboole_0(X43,X43) = k2_xboole_0(X43,k1_xboole_0)) )),
% 4.21/1.02    inference(forward_demodulation,[],[f1893,f131])).
% 4.21/1.02  fof(f131,plain,(
% 4.21/1.02    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 4.21/1.02    inference(resolution,[],[f101,f33])).
% 4.21/1.02  fof(f101,plain,(
% 4.21/1.02    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 4.21/1.02    inference(resolution,[],[f46,f32])).
% 4.21/1.02  fof(f32,plain,(
% 4.21/1.02    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 4.21/1.02    inference(cnf_transformation,[],[f6])).
% 4.21/1.02  fof(f6,axiom,(
% 4.21/1.02    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 4.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 4.21/1.02  fof(f46,plain,(
% 4.21/1.02    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 4.21/1.02    inference(cnf_transformation,[],[f3])).
% 4.21/1.02  fof(f3,axiom,(
% 4.21/1.02    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 4.21/1.02  fof(f1893,plain,(
% 4.21/1.02    ( ! [X43] : (k2_xboole_0(X43,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X43))) = k2_xboole_0(X43,X43)) )),
% 4.21/1.02    inference(superposition,[],[f370,f1838])).
% 4.21/1.02  fof(f1838,plain,(
% 4.21/1.02    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.21/1.02    inference(resolution,[],[f1801,f103])).
% 4.21/1.02  fof(f103,plain,(
% 4.21/1.02    ( ! [X2,X3] : (~r1_tarski(X2,k4_xboole_0(X2,X3)) | k4_xboole_0(X2,X3) = X2) )),
% 4.21/1.02    inference(resolution,[],[f46,f33])).
% 4.21/1.02  fof(f1801,plain,(
% 4.21/1.02    ( ! [X3] : (r1_tarski(X3,k4_xboole_0(X3,k1_xboole_0))) )),
% 4.21/1.02    inference(resolution,[],[f470,f56])).
% 4.21/1.02  fof(f56,plain,(
% 4.21/1.02    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 4.21/1.02    inference(equality_resolution,[],[f45])).
% 4.21/1.02  fof(f45,plain,(
% 4.21/1.02    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 4.21/1.02    inference(cnf_transformation,[],[f3])).
% 4.21/1.02  fof(f470,plain,(
% 4.21/1.02    ( ! [X2,X3] : (~r1_tarski(k4_xboole_0(X2,k1_xboole_0),X3) | r1_tarski(X2,X3)) )),
% 4.21/1.02    inference(superposition,[],[f404,f42])).
% 4.21/1.02  fof(f404,plain,(
% 4.21/1.02    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1))) )),
% 4.21/1.02    inference(resolution,[],[f385,f52])).
% 4.21/1.02  fof(f385,plain,(
% 4.21/1.02    ( ! [X8,X7] : (r1_tarski(k4_xboole_0(X7,k4_xboole_0(X7,k1_xboole_0)),X8)) )),
% 4.21/1.02    inference(resolution,[],[f328,f124])).
% 4.21/1.02  fof(f124,plain,(
% 4.21/1.02    ( ! [X0,X1] : (~r1_tarski(X0,k1_xboole_0) | r1_tarski(X0,X1)) )),
% 4.21/1.02    inference(resolution,[],[f53,f32])).
% 4.21/1.02  fof(f370,plain,(
% 4.21/1.02    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,k4_xboole_0(X3,X2))) = k2_xboole_0(X2,k4_xboole_0(X2,X3))) )),
% 4.21/1.02    inference(forward_demodulation,[],[f329,f35])).
% 4.21/1.02  fof(f329,plain,(
% 4.21/1.02    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),X2) = k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,k4_xboole_0(X3,X2)))) )),
% 4.21/1.02    inference(superposition,[],[f37,f55])).
% 4.21/1.02  fof(f4232,plain,(
% 4.21/1.02    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 4.21/1.02    inference(resolution,[],[f97,f33])).
% 4.21/1.02  fof(f9810,plain,(
% 4.21/1.02    ( ! [X14,X15] : (r1_tarski(k4_xboole_0(k2_xboole_0(X14,X15),k2_xboole_0(X14,k1_xboole_0)),X15)) )),
% 4.21/1.02    inference(superposition,[],[f402,f1867])).
% 4.21/1.02  fof(f1867,plain,(
% 4.21/1.02    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,X2)) )),
% 4.21/1.02    inference(superposition,[],[f386,f1838])).
% 4.21/1.02  fof(f386,plain,(
% 4.21/1.02    ( ! [X9] : (k1_xboole_0 = k4_xboole_0(X9,k4_xboole_0(X9,k1_xboole_0))) )),
% 4.21/1.02    inference(resolution,[],[f328,f101])).
% 4.21/1.02  fof(f402,plain,(
% 4.21/1.02    ( ! [X2,X3,X1] : (r1_tarski(k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X3)))),X3)) )),
% 4.21/1.02    inference(forward_demodulation,[],[f392,f51])).
% 4.21/1.02  fof(f51,plain,(
% 4.21/1.02    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 4.21/1.02    inference(cnf_transformation,[],[f9])).
% 4.21/1.02  fof(f9,axiom,(
% 4.21/1.02    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 4.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 4.21/1.02  fof(f392,plain,(
% 4.21/1.02    ( ! [X2,X3,X1] : (r1_tarski(k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k2_xboole_0(X2,X3))),X3)) )),
% 4.21/1.02    inference(superposition,[],[f328,f51])).
% 4.21/1.02  fof(f751,plain,(
% 4.21/1.02    ~r1_tarski(k2_xboole_0(sK1,sK2),sK0) | spl4_21),
% 4.21/1.02    inference(avatar_component_clause,[],[f749])).
% 4.21/1.02  fof(f749,plain,(
% 4.21/1.02    spl4_21 <=> r1_tarski(k2_xboole_0(sK1,sK2),sK0)),
% 4.21/1.02    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 4.21/1.02  fof(f6271,plain,(
% 4.21/1.02    spl4_57 | ~spl4_73),
% 4.21/1.02    inference(avatar_contradiction_clause,[],[f6258])).
% 4.21/1.02  fof(f6258,plain,(
% 4.21/1.02    $false | (spl4_57 | ~spl4_73)),
% 4.21/1.02    inference(unit_resulting_resolution,[],[f56,f256,f5858,f53])).
% 4.21/1.02  fof(f5858,plain,(
% 4.21/1.02    ~r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1)) | (spl4_57 | ~spl4_73)),
% 4.21/1.02    inference(forward_demodulation,[],[f5577,f5836])).
% 4.21/1.02  fof(f5836,plain,(
% 4.21/1.02    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | ~spl4_73),
% 4.21/1.02    inference(avatar_component_clause,[],[f5834])).
% 4.21/1.02  fof(f5834,plain,(
% 4.21/1.02    spl4_73 <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 4.21/1.02    introduced(avatar_definition,[new_symbols(naming,[spl4_73])])).
% 4.21/1.02  fof(f5577,plain,(
% 4.21/1.02    ~r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_subset_1(sK0,sK1)) | spl4_57),
% 4.21/1.02    inference(avatar_component_clause,[],[f5575])).
% 4.21/1.02  fof(f5575,plain,(
% 4.21/1.02    spl4_57 <=> r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_subset_1(sK0,sK1))),
% 4.21/1.02    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).
% 4.21/1.02  fof(f256,plain,(
% 4.21/1.02    ( ! [X24,X23,X22] : (r1_tarski(k4_xboole_0(X22,k2_xboole_0(X23,X24)),k4_xboole_0(X22,X23))) )),
% 4.21/1.02    inference(superposition,[],[f33,f51])).
% 4.21/1.02  fof(f5850,plain,(
% 4.21/1.02    ~spl4_10 | ~spl4_72 | spl4_74),
% 4.21/1.02    inference(avatar_split_clause,[],[f5849,f5838,f5805,f226])).
% 4.21/1.02  fof(f226,plain,(
% 4.21/1.02    spl4_10 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 4.21/1.02    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 4.21/1.02  fof(f5805,plain,(
% 4.21/1.02    spl4_72 <=> r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))),
% 4.21/1.02    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).
% 4.21/1.02  fof(f5838,plain,(
% 4.21/1.02    spl4_74 <=> r1_tarski(k4_xboole_0(sK0,sK1),k3_subset_1(sK0,sK1))),
% 4.21/1.02    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).
% 4.21/1.02  fof(f5849,plain,(
% 4.21/1.02    ~r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl4_74),
% 4.21/1.02    inference(superposition,[],[f5840,f43])).
% 4.21/1.02  fof(f43,plain,(
% 4.21/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.21/1.02    inference(cnf_transformation,[],[f22])).
% 4.21/1.02  fof(f22,plain,(
% 4.21/1.02    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.21/1.02    inference(ennf_transformation,[],[f14])).
% 4.21/1.02  fof(f14,axiom,(
% 4.21/1.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 4.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 4.21/1.02  fof(f5840,plain,(
% 4.21/1.02    ~r1_tarski(k4_xboole_0(sK0,sK1),k3_subset_1(sK0,sK1)) | spl4_74),
% 4.21/1.02    inference(avatar_component_clause,[],[f5838])).
% 4.21/1.02  fof(f5841,plain,(
% 4.21/1.02    spl4_73 | ~spl4_74 | ~spl4_56),
% 4.21/1.02    inference(avatar_split_clause,[],[f5829,f5570,f5838,f5834])).
% 4.21/1.02  fof(f5570,plain,(
% 4.21/1.02    spl4_56 <=> r1_tarski(k3_subset_1(sK0,sK1),k4_xboole_0(sK0,sK1))),
% 4.21/1.02    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).
% 4.21/1.02  fof(f5829,plain,(
% 4.21/1.02    ~r1_tarski(k4_xboole_0(sK0,sK1),k3_subset_1(sK0,sK1)) | k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | ~spl4_56),
% 4.21/1.02    inference(resolution,[],[f5571,f46])).
% 4.21/1.02  fof(f5571,plain,(
% 4.21/1.02    r1_tarski(k3_subset_1(sK0,sK1),k4_xboole_0(sK0,sK1)) | ~spl4_56),
% 4.21/1.02    inference(avatar_component_clause,[],[f5570])).
% 4.21/1.02  fof(f5826,plain,(
% 4.21/1.02    spl4_72),
% 4.21/1.02    inference(avatar_contradiction_clause,[],[f5814])).
% 4.21/1.02  fof(f5814,plain,(
% 4.21/1.02    $false | spl4_72),
% 4.21/1.02    inference(unit_resulting_resolution,[],[f33,f5807,f470])).
% 4.21/1.02  fof(f5807,plain,(
% 4.21/1.02    ~r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) | spl4_72),
% 4.21/1.02    inference(avatar_component_clause,[],[f5805])).
% 4.21/1.02  fof(f5808,plain,(
% 4.21/1.02    ~spl4_10 | ~spl4_72 | spl4_56),
% 4.21/1.02    inference(avatar_split_clause,[],[f5801,f5570,f5805,f226])).
% 4.21/1.02  fof(f5801,plain,(
% 4.21/1.02    ~r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl4_56),
% 4.21/1.02    inference(superposition,[],[f5572,f43])).
% 4.21/1.02  fof(f5572,plain,(
% 4.21/1.02    ~r1_tarski(k3_subset_1(sK0,sK1),k4_xboole_0(sK0,sK1)) | spl4_56),
% 4.21/1.02    inference(avatar_component_clause,[],[f5570])).
% 4.21/1.02  fof(f5578,plain,(
% 4.21/1.02    ~spl4_13 | ~spl4_57 | spl4_14),
% 4.21/1.02    inference(avatar_split_clause,[],[f588,f555,f5575,f550])).
% 4.21/1.02  fof(f550,plain,(
% 4.21/1.02    spl4_13 <=> m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))),
% 4.21/1.02    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 4.21/1.02  fof(f555,plain,(
% 4.21/1.02    spl4_14 <=> r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k3_subset_1(sK0,sK1))),
% 4.21/1.02    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 4.21/1.02  fof(f588,plain,(
% 4.21/1.02    ~r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_subset_1(sK0,sK1)) | ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) | spl4_14),
% 4.21/1.02    inference(superposition,[],[f557,f43])).
% 4.21/1.02  fof(f557,plain,(
% 4.21/1.02    ~r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k3_subset_1(sK0,sK1)) | spl4_14),
% 4.21/1.02    inference(avatar_component_clause,[],[f555])).
% 4.21/1.02  fof(f798,plain,(
% 4.21/1.02    ~spl4_1),
% 4.21/1.02    inference(avatar_contradiction_clause,[],[f795])).
% 4.21/1.02  fof(f795,plain,(
% 4.21/1.02    $false | ~spl4_1),
% 4.21/1.02    inference(unit_resulting_resolution,[],[f31,f72])).
% 4.21/1.02  fof(f72,plain,(
% 4.21/1.02    v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl4_1),
% 4.21/1.02    inference(avatar_component_clause,[],[f70])).
% 4.21/1.02  fof(f70,plain,(
% 4.21/1.02    spl4_1 <=> v1_xboole_0(k1_zfmisc_1(sK0))),
% 4.21/1.02    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 4.21/1.02  fof(f31,plain,(
% 4.21/1.02    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 4.21/1.02    inference(cnf_transformation,[],[f15])).
% 4.21/1.02  fof(f15,axiom,(
% 4.21/1.02    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 4.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 4.21/1.02  fof(f794,plain,(
% 4.21/1.02    spl4_1 | spl4_3),
% 4.21/1.02    inference(avatar_split_clause,[],[f564,f79,f70])).
% 4.21/1.02  fof(f564,plain,(
% 4.21/1.02    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 4.21/1.02    inference(resolution,[],[f30,f41])).
% 4.21/1.02  fof(f41,plain,(
% 4.21/1.02    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 4.21/1.02    inference(cnf_transformation,[],[f20])).
% 4.21/1.02  fof(f20,plain,(
% 4.21/1.02    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 4.21/1.02    inference(ennf_transformation,[],[f13])).
% 4.21/1.02  fof(f13,axiom,(
% 4.21/1.02    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 4.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 4.21/1.02  fof(f30,plain,(
% 4.21/1.02    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 4.21/1.02    inference(cnf_transformation,[],[f19])).
% 4.21/1.02  fof(f19,plain,(
% 4.21/1.02    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.21/1.02    inference(ennf_transformation,[],[f18])).
% 4.21/1.02  fof(f18,negated_conjecture,(
% 4.21/1.02    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 4.21/1.02    inference(negated_conjecture,[],[f17])).
% 4.21/1.02  fof(f17,conjecture,(
% 4.21/1.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 4.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).
% 4.21/1.02  fof(f752,plain,(
% 4.21/1.02    ~spl4_21 | spl4_1 | spl4_13),
% 4.21/1.02    inference(avatar_split_clause,[],[f741,f550,f70,f749])).
% 4.21/1.02  fof(f741,plain,(
% 4.21/1.02    v1_xboole_0(k1_zfmisc_1(sK0)) | ~r1_tarski(k2_xboole_0(sK1,sK2),sK0) | spl4_13),
% 4.21/1.02    inference(resolution,[],[f65,f552])).
% 4.21/1.02  fof(f552,plain,(
% 4.21/1.02    ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) | spl4_13),
% 4.21/1.02    inference(avatar_component_clause,[],[f550])).
% 4.21/1.02  fof(f65,plain,(
% 4.21/1.02    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(k1_zfmisc_1(X0)) | ~r1_tarski(X1,X0)) )),
% 4.21/1.02    inference(resolution,[],[f40,f59])).
% 4.21/1.02  fof(f59,plain,(
% 4.21/1.02    ( ! [X2,X0] : (r2_hidden(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X2,X0)) )),
% 4.21/1.02    inference(equality_resolution,[],[f47])).
% 4.21/1.02  fof(f47,plain,(
% 4.21/1.02    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 4.21/1.02    inference(cnf_transformation,[],[f12])).
% 4.21/1.02  fof(f40,plain,(
% 4.21/1.02    ( ! [X0,X1] : (~r2_hidden(X1,X0) | v1_xboole_0(X0) | m1_subset_1(X1,X0)) )),
% 4.21/1.02    inference(cnf_transformation,[],[f20])).
% 4.21/1.02  fof(f570,plain,(
% 4.21/1.02    spl4_12),
% 4.21/1.02    inference(avatar_contradiction_clause,[],[f566])).
% 4.21/1.02  fof(f566,plain,(
% 4.21/1.02    $false | spl4_12),
% 4.21/1.02    inference(subsumption_resolution,[],[f28,f548])).
% 4.21/1.02  fof(f548,plain,(
% 4.21/1.02    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | spl4_12),
% 4.21/1.02    inference(avatar_component_clause,[],[f546])).
% 4.21/1.02  fof(f546,plain,(
% 4.21/1.02    spl4_12 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 4.21/1.02    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 4.21/1.02  fof(f28,plain,(
% 4.21/1.02    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 4.21/1.02    inference(cnf_transformation,[],[f19])).
% 4.21/1.02  fof(f563,plain,(
% 4.21/1.02    spl4_10),
% 4.21/1.02    inference(avatar_contradiction_clause,[],[f559])).
% 4.21/1.02  fof(f559,plain,(
% 4.21/1.02    $false | spl4_10),
% 4.21/1.02    inference(subsumption_resolution,[],[f30,f228])).
% 4.21/1.02  fof(f228,plain,(
% 4.21/1.02    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl4_10),
% 4.21/1.02    inference(avatar_component_clause,[],[f226])).
% 4.21/1.02  fof(f558,plain,(
% 4.21/1.02    ~spl4_10 | ~spl4_12 | ~spl4_14),
% 4.21/1.02    inference(avatar_split_clause,[],[f544,f555,f546,f226])).
% 4.21/1.02  fof(f544,plain,(
% 4.21/1.02    ~r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k3_subset_1(sK0,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 4.21/1.02    inference(superposition,[],[f29,f54])).
% 4.21/1.02  fof(f54,plain,(
% 4.21/1.02    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.21/1.02    inference(cnf_transformation,[],[f27])).
% 4.21/1.02  fof(f27,plain,(
% 4.21/1.02    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.21/1.02    inference(flattening,[],[f26])).
% 4.21/1.02  fof(f26,plain,(
% 4.21/1.02    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 4.21/1.02    inference(ennf_transformation,[],[f16])).
% 4.21/1.02  fof(f16,axiom,(
% 4.21/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 4.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 4.21/1.02  fof(f29,plain,(
% 4.21/1.02    ~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))),
% 4.21/1.02    inference(cnf_transformation,[],[f19])).
% 4.21/1.02  fof(f77,plain,(
% 4.21/1.02    spl4_1 | spl4_2),
% 4.21/1.02    inference(avatar_split_clause,[],[f66,f74,f70])).
% 4.21/1.02  fof(f66,plain,(
% 4.21/1.02    r2_hidden(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 4.21/1.02    inference(resolution,[],[f41,f28])).
% 4.21/1.02  % SZS output end Proof for theBenchmark
% 4.21/1.02  % (13546)------------------------------
% 4.21/1.02  % (13546)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.21/1.02  % (13546)Termination reason: Refutation
% 4.21/1.02  
% 4.21/1.02  % (13546)Memory used [KB]: 11641
% 4.21/1.02  % (13546)Time elapsed: 0.608 s
% 4.21/1.02  % (13546)------------------------------
% 4.21/1.02  % (13546)------------------------------
% 4.21/1.02  % (13532)Success in time 0.657 s
%------------------------------------------------------------------------------
