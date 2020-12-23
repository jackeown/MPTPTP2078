%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t126_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:59 EDT 2019

% Result     : Theorem 0.73s
% Output     : Refutation 0.73s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 190 expanded)
%              Number of leaves         :   25 (  71 expanded)
%              Depth                    :   12
%              Number of atoms          :  188 ( 354 expanded)
%              Number of equality atoms :   44 ( 111 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8622,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f104,f121,f154,f1824,f1831,f1840,f1847,f1917,f2509,f8511,f8513])).

fof(f8513,plain,(
    spl11_9 ),
    inference(avatar_contradiction_clause,[],[f8512])).

fof(f8512,plain,
    ( $false
    | ~ spl11_9 ),
    inference(subsumption_resolution,[],[f8509,f91])).

fof(f91,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t126_zfmisc_1.p',d10_xboole_0)).

fof(f8509,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)),k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))
    | ~ spl11_9 ),
    inference(backward_demodulation,[],[f8421,f1823])).

fof(f1823,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))
    | ~ spl11_9 ),
    inference(avatar_component_clause,[],[f1822])).

fof(f1822,plain,
    ( spl11_9
  <=> ~ r1_tarski(k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f8421,plain,(
    ! [X10,X8,X7,X9] : k4_xboole_0(k2_zfmisc_1(X9,X10),k2_zfmisc_1(X7,X8)) = k4_xboole_0(k2_zfmisc_1(X9,X10),k2_zfmisc_1(k3_xboole_0(X9,X7),k3_xboole_0(X10,X8))) ),
    inference(superposition,[],[f821,f238])).

fof(f238,plain,(
    ! [X6,X8,X7,X9] : k2_zfmisc_1(k3_xboole_0(X6,X8),k3_xboole_0(X7,X9)) = k3_xboole_0(k2_zfmisc_1(X8,X9),k2_zfmisc_1(X6,X7)) ),
    inference(superposition,[],[f43,f63])).

fof(f63,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t126_zfmisc_1.p',commutativity_k3_xboole_0)).

fof(f43,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t126_zfmisc_1.p',t123_zfmisc_1)).

fof(f821,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f806,f71])).

fof(f71,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t126_zfmisc_1.p',t1_boole)).

fof(f806,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[],[f58,f509])).

fof(f509,plain,(
    ! [X27] : k4_xboole_0(X27,X27) = k1_xboole_0 ),
    inference(resolution,[],[f283,f132])).

fof(f132,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f130,f123])).

fof(f123,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k1_xboole_0)
      | r2_hidden(X3,X2) ) ),
    inference(superposition,[],[f85,f71])).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t126_zfmisc_1.p',d3_xboole_0)).

fof(f130,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f89,f68])).

fof(f68,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t126_zfmisc_1.p',t4_boole)).

fof(f89,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t126_zfmisc_1.p',d5_xboole_0)).

fof(f283,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK5(X2,X2,X3),X3)
      | k4_xboole_0(X2,X2) = X3 ) ),
    inference(duplicate_literal_removal,[],[f279])).

fof(f279,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK5(X2,X2,X3),X3)
      | k4_xboole_0(X2,X2) = X3
      | r2_hidden(sK5(X2,X2,X3),X3)
      | k4_xboole_0(X2,X2) = X3 ) ),
    inference(resolution,[],[f52,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X2)
      | r2_hidden(sK5(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1,X2),X1)
      | r2_hidden(sK5(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f58,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t126_zfmisc_1.p',t54_xboole_1)).

fof(f8511,plain,(
    spl11_11 ),
    inference(avatar_contradiction_clause,[],[f8510])).

fof(f8510,plain,
    ( $false
    | ~ spl11_11 ),
    inference(subsumption_resolution,[],[f8508,f91])).

fof(f8508,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)),k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))
    | ~ spl11_11 ),
    inference(backward_demodulation,[],[f8421,f1830])).

fof(f1830,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)),k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3))))
    | ~ spl11_11 ),
    inference(avatar_component_clause,[],[f1829])).

fof(f1829,plain,
    ( spl11_11
  <=> ~ r1_tarski(k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)),k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f2509,plain,
    ( ~ spl11_21
    | ~ spl11_23
    | spl11_15 ),
    inference(avatar_split_clause,[],[f1849,f1845,f2507,f2501])).

fof(f2501,plain,
    ( spl11_21
  <=> ~ r1_tarski(k3_xboole_0(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_21])])).

fof(f2507,plain,
    ( spl11_23
  <=> ~ r1_tarski(k3_xboole_0(sK1,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_23])])).

fof(f1845,plain,
    ( spl11_15
  <=> ~ r1_tarski(k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).

fof(f1849,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK3),sK3)
    | ~ r1_tarski(k3_xboole_0(sK0,sK2),sK2)
    | ~ spl11_15 ),
    inference(resolution,[],[f1846,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t126_zfmisc_1.p',t119_zfmisc_1)).

fof(f1846,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK2,sK3))
    | ~ spl11_15 ),
    inference(avatar_component_clause,[],[f1845])).

fof(f1917,plain,
    ( ~ spl11_17
    | ~ spl11_19
    | spl11_13 ),
    inference(avatar_split_clause,[],[f1848,f1838,f1915,f1909])).

fof(f1909,plain,
    ( spl11_17
  <=> ~ r1_tarski(sK2,k3_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).

fof(f1915,plain,
    ( spl11_19
  <=> ~ r1_tarski(sK3,k3_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).

fof(f1838,plain,
    ( spl11_13
  <=> ~ r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).

fof(f1848,plain,
    ( ~ r1_tarski(sK3,k3_xboole_0(sK1,sK3))
    | ~ r1_tarski(sK2,k3_xboole_0(sK0,sK2))
    | ~ spl11_13 ),
    inference(resolution,[],[f1839,f76])).

fof(f1839,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3)))
    | ~ spl11_13 ),
    inference(avatar_component_clause,[],[f1838])).

fof(f1847,plain,
    ( ~ spl11_15
    | spl11_11 ),
    inference(avatar_split_clause,[],[f1833,f1829,f1845])).

fof(f1833,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK2,sK3))
    | ~ spl11_11 ),
    inference(resolution,[],[f1830,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t126_zfmisc_1.p',t34_xboole_1)).

fof(f1840,plain,
    ( ~ spl11_13
    | spl11_9 ),
    inference(avatar_split_clause,[],[f1832,f1822,f1838])).

fof(f1832,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3)))
    | ~ spl11_9 ),
    inference(resolution,[],[f1823,f72])).

fof(f1831,plain,
    ( ~ spl11_11
    | spl11_7 ),
    inference(avatar_split_clause,[],[f1807,f152,f1829])).

fof(f152,plain,
    ( spl11_7
  <=> ~ r1_tarski(k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)),k2_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)),k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f1807,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)),k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3))))
    | ~ spl11_7 ),
    inference(forward_demodulation,[],[f1805,f63])).

fof(f1805,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)),k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK3,sK1))))
    | ~ spl11_7 ),
    inference(backward_demodulation,[],[f1803,f153])).

fof(f153,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)),k2_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)),k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1)))
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f152])).

fof(f1803,plain,(
    ! [X2,X0,X3,X1] : k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k3_xboole_0(X0,X2),k3_xboole_0(X3,X1))) = k2_xboole_0(k2_zfmisc_1(X0,k4_xboole_0(X1,X3)),k2_zfmisc_1(k4_xboole_0(X0,X2),X1)) ),
    inference(forward_demodulation,[],[f1769,f43])).

fof(f1769,plain,(
    ! [X2,X0,X3,X1] : k4_xboole_0(k2_zfmisc_1(X0,X1),k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X2,X1))) = k2_xboole_0(k2_zfmisc_1(X0,k4_xboole_0(X1,X3)),k2_zfmisc_1(k4_xboole_0(X0,X2),X1)) ),
    inference(superposition,[],[f209,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t126_zfmisc_1.p',t125_zfmisc_1)).

fof(f209,plain,(
    ! [X10,X8,X11,X9] : k4_xboole_0(k2_zfmisc_1(X8,X9),k3_xboole_0(k2_zfmisc_1(X8,X10),X11)) = k2_xboole_0(k2_zfmisc_1(X8,k4_xboole_0(X9,X10)),k4_xboole_0(k2_zfmisc_1(X8,X9),X11)) ),
    inference(superposition,[],[f58,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f1824,plain,
    ( ~ spl11_9
    | spl11_5 ),
    inference(avatar_split_clause,[],[f1806,f146,f1822])).

fof(f146,plain,
    ( spl11_5
  <=> ~ r1_tarski(k2_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)),k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1)),k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f1806,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))
    | ~ spl11_5 ),
    inference(forward_demodulation,[],[f1804,f63])).

fof(f1804,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK3,sK1))),k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))
    | ~ spl11_5 ),
    inference(backward_demodulation,[],[f1803,f147])).

fof(f147,plain,
    ( ~ r1_tarski(k2_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)),k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1)),k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f146])).

fof(f154,plain,
    ( ~ spl11_5
    | ~ spl11_7
    | spl11_1 ),
    inference(avatar_split_clause,[],[f139,f102,f152,f146])).

fof(f102,plain,
    ( spl11_1
  <=> k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) != k2_xboole_0(k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1),k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f139,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)),k2_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)),k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1)))
    | ~ r1_tarski(k2_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)),k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1)),k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))
    | ~ spl11_1 ),
    inference(forward_demodulation,[],[f138,f64])).

fof(f64,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t126_zfmisc_1.p',commutativity_k2_xboole_0)).

fof(f138,plain,
    ( ~ r1_tarski(k2_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)),k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1)),k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))
    | ~ r1_tarski(k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)),k2_xboole_0(k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1),k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))))
    | ~ spl11_1 ),
    inference(forward_demodulation,[],[f135,f64])).

fof(f135,plain,
    ( ~ r1_tarski(k2_xboole_0(k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1),k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))
    | ~ r1_tarski(k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)),k2_xboole_0(k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1),k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))))
    | ~ spl11_1 ),
    inference(extensionality_resolution,[],[f62,f103])).

fof(f103,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) != k2_xboole_0(k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1),k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)))
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f102])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f121,plain,
    ( ~ spl11_3
    | spl11_1 ),
    inference(avatar_split_clause,[],[f111,f102,f119])).

fof(f119,plain,
    ( spl11_3
  <=> k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) != k2_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)),k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f111,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) != k2_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)),k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1))
    | ~ spl11_1 ),
    inference(superposition,[],[f103,f64])).

fof(f104,plain,(
    ~ spl11_1 ),
    inference(avatar_split_clause,[],[f42,f102])).

fof(f42,plain,(
    k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) != k2_xboole_0(k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1),k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ? [X0,X1,X2,X3] : k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) != k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X2),X1),k2_zfmisc_1(X0,k4_xboole_0(X1,X3))) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X2),X1),k2_zfmisc_1(X0,k4_xboole_0(X1,X3))) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] : k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X2),X1),k2_zfmisc_1(X0,k4_xboole_0(X1,X3))) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t126_zfmisc_1.p',t126_zfmisc_1)).
%------------------------------------------------------------------------------
