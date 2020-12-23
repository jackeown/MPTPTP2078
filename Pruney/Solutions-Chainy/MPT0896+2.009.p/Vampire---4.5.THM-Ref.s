%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:13 EST 2020

% Result     : Theorem 1.43s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 349 expanded)
%              Number of leaves         :    7 ( 126 expanded)
%              Depth                    :   20
%              Number of atoms          :  223 (1314 expanded)
%              Number of equality atoms :  120 (1102 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f101,plain,(
    $false ),
    inference(subsumption_resolution,[],[f100,f45])).

fof(f45,plain,(
    ~ sQ8_eqProxy(k1_xboole_0,sK2) ),
    inference(equality_proxy_replacement,[],[f18,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( sQ8_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ8_eqProxy])])).

fof(f18,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
       => ( ( X3 = X7
            & X2 = X6
            & X1 = X5
            & X0 = X4 )
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
     => ( ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 )
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_mcart_1)).

fof(f100,plain,(
    sQ8_eqProxy(k1_xboole_0,sK2) ),
    inference(subsumption_resolution,[],[f99,f46])).

fof(f46,plain,(
    ~ sQ8_eqProxy(k1_xboole_0,sK1) ),
    inference(equality_proxy_replacement,[],[f17,f43])).

fof(f17,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f9])).

fof(f99,plain,
    ( sQ8_eqProxy(k1_xboole_0,sK1)
    | sQ8_eqProxy(k1_xboole_0,sK2) ),
    inference(subsumption_resolution,[],[f98,f47])).

fof(f47,plain,(
    ~ sQ8_eqProxy(k1_xboole_0,sK0) ),
    inference(equality_proxy_replacement,[],[f16,f43])).

fof(f16,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f9])).

fof(f98,plain,
    ( sQ8_eqProxy(k1_xboole_0,sK0)
    | sQ8_eqProxy(k1_xboole_0,sK1)
    | sQ8_eqProxy(k1_xboole_0,sK2) ),
    inference(subsumption_resolution,[],[f97,f96])).

fof(f96,plain,(
    ~ sQ8_eqProxy(sK0,sK4) ),
    inference(resolution,[],[f95,f91])).

fof(f91,plain,
    ( ~ sQ8_eqProxy(sK1,sK5)
    | ~ sQ8_eqProxy(sK0,sK4) ),
    inference(resolution,[],[f90,f71])).

fof(f71,plain,
    ( ~ sQ8_eqProxy(sK2,sK6)
    | ~ sQ8_eqProxy(sK1,sK5)
    | ~ sQ8_eqProxy(sK0,sK4) ),
    inference(resolution,[],[f70,f49])).

fof(f49,plain,
    ( ~ sQ8_eqProxy(sK3,sK7)
    | ~ sQ8_eqProxy(sK1,sK5)
    | ~ sQ8_eqProxy(sK2,sK6)
    | ~ sQ8_eqProxy(sK0,sK4) ),
    inference(equality_proxy_replacement,[],[f14,f43,f43,f43,f43])).

fof(f14,plain,
    ( sK0 != sK4
    | sK1 != sK5
    | sK2 != sK6
    | sK3 != sK7 ),
    inference(cnf_transformation,[],[f9])).

fof(f70,plain,(
    sQ8_eqProxy(sK3,sK7) ),
    inference(subsumption_resolution,[],[f69,f45])).

fof(f69,plain,
    ( sQ8_eqProxy(sK3,sK7)
    | sQ8_eqProxy(k1_xboole_0,sK2) ),
    inference(subsumption_resolution,[],[f68,f46])).

fof(f68,plain,
    ( sQ8_eqProxy(sK3,sK7)
    | sQ8_eqProxy(k1_xboole_0,sK1)
    | sQ8_eqProxy(k1_xboole_0,sK2) ),
    inference(subsumption_resolution,[],[f67,f47])).

fof(f67,plain,
    ( sQ8_eqProxy(sK3,sK7)
    | sQ8_eqProxy(k1_xboole_0,sK0)
    | sQ8_eqProxy(k1_xboole_0,sK1)
    | sQ8_eqProxy(k1_xboole_0,sK2) ),
    inference(resolution,[],[f66,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ sQ8_eqProxy(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | sQ8_eqProxy(k1_xboole_0,X0)
      | sQ8_eqProxy(k1_xboole_0,X1)
      | sQ8_eqProxy(k1_xboole_0,X2) ) ),
    inference(equality_proxy_replacement,[],[f39,f43,f43,f43,f43])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2 ) ),
    inference(definition_unfolding,[],[f23,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).

fof(f66,plain,
    ( sQ8_eqProxy(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | sQ8_eqProxy(sK3,sK7) ),
    inference(subsumption_resolution,[],[f64,f44])).

fof(f44,plain,(
    ~ sQ8_eqProxy(k1_xboole_0,sK3) ),
    inference(equality_proxy_replacement,[],[f19,f43])).

fof(f19,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f9])).

fof(f64,plain,
    ( sQ8_eqProxy(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | sQ8_eqProxy(k1_xboole_0,sK3)
    | sQ8_eqProxy(sK3,sK7) ),
    inference(resolution,[],[f48,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sQ8_eqProxy(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
      | sQ8_eqProxy(k1_xboole_0,X0)
      | sQ8_eqProxy(k1_xboole_0,X1)
      | sQ8_eqProxy(X1,X3) ) ),
    inference(equality_proxy_replacement,[],[f29,f43,f43,f43,f43])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f48,plain,(
    sQ8_eqProxy(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(equality_proxy_replacement,[],[f32,f43])).

fof(f32,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) ),
    inference(definition_unfolding,[],[f15,f31,f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f27,f30])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f15,plain,(
    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f9])).

fof(f90,plain,(
    sQ8_eqProxy(sK2,sK6) ),
    inference(subsumption_resolution,[],[f89,f45])).

fof(f89,plain,
    ( sQ8_eqProxy(sK2,sK6)
    | sQ8_eqProxy(k1_xboole_0,sK2) ),
    inference(subsumption_resolution,[],[f88,f46])).

fof(f88,plain,
    ( sQ8_eqProxy(sK2,sK6)
    | sQ8_eqProxy(k1_xboole_0,sK1)
    | sQ8_eqProxy(k1_xboole_0,sK2) ),
    inference(subsumption_resolution,[],[f87,f47])).

fof(f87,plain,
    ( sQ8_eqProxy(sK2,sK6)
    | sQ8_eqProxy(k1_xboole_0,sK0)
    | sQ8_eqProxy(k1_xboole_0,sK1)
    | sQ8_eqProxy(k1_xboole_0,sK2) ),
    inference(resolution,[],[f84,f56])).

fof(f84,plain,
    ( sQ8_eqProxy(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | sQ8_eqProxy(sK2,sK6) ),
    inference(duplicate_literal_removal,[],[f81])).

fof(f81,plain,
    ( sQ8_eqProxy(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | sQ8_eqProxy(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | sQ8_eqProxy(sK2,sK6) ),
    inference(resolution,[],[f65,f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ sQ8_eqProxy(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5))
      | sQ8_eqProxy(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | sQ8_eqProxy(X2,X5) ) ),
    inference(equality_proxy_replacement,[],[f33,f43,f43,f43])).

fof(f33,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | X2 = X5 ) ),
    inference(definition_unfolding,[],[f22,f30,f30,f30])).

fof(f22,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | X2 = X5 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_mcart_1)).

fof(f65,plain,
    ( sQ8_eqProxy(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
    | sQ8_eqProxy(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(subsumption_resolution,[],[f63,f44])).

fof(f63,plain,
    ( sQ8_eqProxy(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | sQ8_eqProxy(k1_xboole_0,sK3)
    | sQ8_eqProxy(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(resolution,[],[f48,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sQ8_eqProxy(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
      | sQ8_eqProxy(k1_xboole_0,X0)
      | sQ8_eqProxy(k1_xboole_0,X1)
      | sQ8_eqProxy(X0,X2) ) ),
    inference(equality_proxy_replacement,[],[f28,f43,f43,f43,f43])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f95,plain,(
    sQ8_eqProxy(sK1,sK5) ),
    inference(subsumption_resolution,[],[f94,f45])).

fof(f94,plain,
    ( sQ8_eqProxy(sK1,sK5)
    | sQ8_eqProxy(k1_xboole_0,sK2) ),
    inference(subsumption_resolution,[],[f93,f46])).

fof(f93,plain,
    ( sQ8_eqProxy(sK1,sK5)
    | sQ8_eqProxy(k1_xboole_0,sK1)
    | sQ8_eqProxy(k1_xboole_0,sK2) ),
    inference(subsumption_resolution,[],[f92,f47])).

fof(f92,plain,
    ( sQ8_eqProxy(sK1,sK5)
    | sQ8_eqProxy(k1_xboole_0,sK0)
    | sQ8_eqProxy(k1_xboole_0,sK1)
    | sQ8_eqProxy(k1_xboole_0,sK2) ),
    inference(resolution,[],[f85,f56])).

fof(f85,plain,
    ( sQ8_eqProxy(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | sQ8_eqProxy(sK1,sK5) ),
    inference(duplicate_literal_removal,[],[f80])).

fof(f80,plain,
    ( sQ8_eqProxy(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | sQ8_eqProxy(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | sQ8_eqProxy(sK1,sK5) ),
    inference(resolution,[],[f65,f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ sQ8_eqProxy(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5))
      | sQ8_eqProxy(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | sQ8_eqProxy(X1,X4) ) ),
    inference(equality_proxy_replacement,[],[f34,f43,f43,f43])).

fof(f34,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | X1 = X4 ) ),
    inference(definition_unfolding,[],[f21,f30,f30,f30])).

fof(f21,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | X1 = X4 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f97,plain,
    ( sQ8_eqProxy(sK0,sK4)
    | sQ8_eqProxy(k1_xboole_0,sK0)
    | sQ8_eqProxy(k1_xboole_0,sK1)
    | sQ8_eqProxy(k1_xboole_0,sK2) ),
    inference(resolution,[],[f86,f56])).

fof(f86,plain,
    ( sQ8_eqProxy(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | sQ8_eqProxy(sK0,sK4) ),
    inference(duplicate_literal_removal,[],[f79])).

fof(f79,plain,
    ( sQ8_eqProxy(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | sQ8_eqProxy(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | sQ8_eqProxy(sK0,sK4) ),
    inference(resolution,[],[f65,f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ sQ8_eqProxy(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5))
      | sQ8_eqProxy(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | sQ8_eqProxy(X0,X3) ) ),
    inference(equality_proxy_replacement,[],[f35,f43,f43,f43])).

fof(f35,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | X0 = X3 ) ),
    inference(definition_unfolding,[],[f20,f30,f30,f30])).

fof(f20,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:16:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (20606)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (20623)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.52  % (20604)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.52  % (20616)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.53  % (20616)Refutation not found, incomplete strategy% (20616)------------------------------
% 0.22/0.53  % (20616)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (20624)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (20608)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.53  % (20617)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.53  % (20616)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (20616)Memory used [KB]: 1663
% 0.22/0.53  % (20616)Time elapsed: 0.115 s
% 0.22/0.53  % (20607)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (20616)------------------------------
% 0.22/0.53  % (20616)------------------------------
% 0.22/0.53  % (20603)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (20615)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.54  % (20609)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.54  % (20627)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.54  % (20621)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.54  % (20629)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.54  % (20605)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (20602)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.43/0.54  % (20618)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.43/0.55  % (20601)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.43/0.55  % (20628)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.43/0.55  % (20614)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.43/0.55  % (20628)Refutation not found, incomplete strategy% (20628)------------------------------
% 1.43/0.55  % (20628)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (20628)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (20628)Memory used [KB]: 6268
% 1.43/0.55  % (20628)Time elapsed: 0.137 s
% 1.43/0.55  % (20628)------------------------------
% 1.43/0.55  % (20628)------------------------------
% 1.43/0.55  % (20614)Refutation not found, incomplete strategy% (20614)------------------------------
% 1.43/0.55  % (20614)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (20614)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (20614)Memory used [KB]: 10618
% 1.43/0.55  % (20614)Time elapsed: 0.141 s
% 1.43/0.55  % (20614)------------------------------
% 1.43/0.55  % (20614)------------------------------
% 1.43/0.55  % (20630)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.43/0.55  % (20625)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.43/0.55  % (20620)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.43/0.55  % (20611)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.43/0.55  % (20620)Refutation not found, incomplete strategy% (20620)------------------------------
% 1.43/0.55  % (20620)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (20620)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (20620)Memory used [KB]: 1663
% 1.43/0.55  % (20620)Time elapsed: 0.139 s
% 1.43/0.55  % (20620)------------------------------
% 1.43/0.55  % (20620)------------------------------
% 1.43/0.55  % (20613)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.43/0.55  % (20612)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.43/0.55  % (20632)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.43/0.56  % (20632)Refutation found. Thanks to Tanya!
% 1.43/0.56  % SZS status Theorem for theBenchmark
% 1.43/0.56  % SZS output start Proof for theBenchmark
% 1.43/0.56  fof(f101,plain,(
% 1.43/0.56    $false),
% 1.43/0.56    inference(subsumption_resolution,[],[f100,f45])).
% 1.43/0.56  fof(f45,plain,(
% 1.43/0.56    ~sQ8_eqProxy(k1_xboole_0,sK2)),
% 1.43/0.56    inference(equality_proxy_replacement,[],[f18,f43])).
% 1.43/0.56  fof(f43,plain,(
% 1.43/0.56    ! [X1,X0] : (sQ8_eqProxy(X0,X1) <=> X0 = X1)),
% 1.43/0.56    introduced(equality_proxy_definition,[new_symbols(naming,[sQ8_eqProxy])])).
% 1.43/0.56  fof(f18,plain,(
% 1.43/0.56    k1_xboole_0 != sK2),
% 1.43/0.56    inference(cnf_transformation,[],[f9])).
% 1.43/0.56  fof(f9,plain,(
% 1.43/0.56    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 1.43/0.56    inference(flattening,[],[f8])).
% 1.43/0.56  fof(f8,plain,(
% 1.43/0.56    ? [X0,X1,X2,X3,X4,X5,X6,X7] : (((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 1.43/0.56    inference(ennf_transformation,[],[f7])).
% 1.43/0.56  fof(f7,negated_conjecture,(
% 1.43/0.56    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.43/0.56    inference(negated_conjecture,[],[f6])).
% 1.43/0.56  fof(f6,conjecture,(
% 1.43/0.56    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_mcart_1)).
% 1.43/0.56  fof(f100,plain,(
% 1.43/0.56    sQ8_eqProxy(k1_xboole_0,sK2)),
% 1.43/0.56    inference(subsumption_resolution,[],[f99,f46])).
% 1.43/0.56  fof(f46,plain,(
% 1.43/0.56    ~sQ8_eqProxy(k1_xboole_0,sK1)),
% 1.43/0.56    inference(equality_proxy_replacement,[],[f17,f43])).
% 1.43/0.56  fof(f17,plain,(
% 1.43/0.56    k1_xboole_0 != sK1),
% 1.43/0.56    inference(cnf_transformation,[],[f9])).
% 1.43/0.56  fof(f99,plain,(
% 1.43/0.56    sQ8_eqProxy(k1_xboole_0,sK1) | sQ8_eqProxy(k1_xboole_0,sK2)),
% 1.43/0.56    inference(subsumption_resolution,[],[f98,f47])).
% 1.43/0.56  fof(f47,plain,(
% 1.43/0.56    ~sQ8_eqProxy(k1_xboole_0,sK0)),
% 1.43/0.56    inference(equality_proxy_replacement,[],[f16,f43])).
% 1.43/0.56  fof(f16,plain,(
% 1.43/0.56    k1_xboole_0 != sK0),
% 1.43/0.56    inference(cnf_transformation,[],[f9])).
% 1.43/0.56  fof(f98,plain,(
% 1.43/0.56    sQ8_eqProxy(k1_xboole_0,sK0) | sQ8_eqProxy(k1_xboole_0,sK1) | sQ8_eqProxy(k1_xboole_0,sK2)),
% 1.43/0.56    inference(subsumption_resolution,[],[f97,f96])).
% 1.43/0.56  fof(f96,plain,(
% 1.43/0.56    ~sQ8_eqProxy(sK0,sK4)),
% 1.43/0.56    inference(resolution,[],[f95,f91])).
% 1.43/0.56  fof(f91,plain,(
% 1.43/0.56    ~sQ8_eqProxy(sK1,sK5) | ~sQ8_eqProxy(sK0,sK4)),
% 1.43/0.56    inference(resolution,[],[f90,f71])).
% 1.43/0.56  fof(f71,plain,(
% 1.43/0.56    ~sQ8_eqProxy(sK2,sK6) | ~sQ8_eqProxy(sK1,sK5) | ~sQ8_eqProxy(sK0,sK4)),
% 1.43/0.56    inference(resolution,[],[f70,f49])).
% 1.43/0.56  fof(f49,plain,(
% 1.43/0.56    ~sQ8_eqProxy(sK3,sK7) | ~sQ8_eqProxy(sK1,sK5) | ~sQ8_eqProxy(sK2,sK6) | ~sQ8_eqProxy(sK0,sK4)),
% 1.43/0.56    inference(equality_proxy_replacement,[],[f14,f43,f43,f43,f43])).
% 1.43/0.56  fof(f14,plain,(
% 1.43/0.56    sK0 != sK4 | sK1 != sK5 | sK2 != sK6 | sK3 != sK7),
% 1.43/0.56    inference(cnf_transformation,[],[f9])).
% 1.43/0.56  fof(f70,plain,(
% 1.43/0.56    sQ8_eqProxy(sK3,sK7)),
% 1.43/0.56    inference(subsumption_resolution,[],[f69,f45])).
% 1.43/0.56  fof(f69,plain,(
% 1.43/0.56    sQ8_eqProxy(sK3,sK7) | sQ8_eqProxy(k1_xboole_0,sK2)),
% 1.43/0.56    inference(subsumption_resolution,[],[f68,f46])).
% 1.43/0.56  fof(f68,plain,(
% 1.43/0.56    sQ8_eqProxy(sK3,sK7) | sQ8_eqProxy(k1_xboole_0,sK1) | sQ8_eqProxy(k1_xboole_0,sK2)),
% 1.43/0.56    inference(subsumption_resolution,[],[f67,f47])).
% 1.43/0.56  fof(f67,plain,(
% 1.43/0.56    sQ8_eqProxy(sK3,sK7) | sQ8_eqProxy(k1_xboole_0,sK0) | sQ8_eqProxy(k1_xboole_0,sK1) | sQ8_eqProxy(k1_xboole_0,sK2)),
% 1.43/0.56    inference(resolution,[],[f66,f56])).
% 1.43/0.56  fof(f56,plain,(
% 1.43/0.56    ( ! [X2,X0,X1] : (~sQ8_eqProxy(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | sQ8_eqProxy(k1_xboole_0,X0) | sQ8_eqProxy(k1_xboole_0,X1) | sQ8_eqProxy(k1_xboole_0,X2)) )),
% 1.43/0.56    inference(equality_proxy_replacement,[],[f39,f43,f43,f43,f43])).
% 1.43/0.56  fof(f39,plain,(
% 1.43/0.56    ( ! [X2,X0,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2) )),
% 1.43/0.56    inference(definition_unfolding,[],[f23,f30])).
% 1.43/0.56  fof(f30,plain,(
% 1.43/0.56    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f2])).
% 1.43/0.56  fof(f2,axiom,(
% 1.43/0.56    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.43/0.56  fof(f23,plain,(
% 1.43/0.56    ( ! [X2,X0,X1] : (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2) )),
% 1.43/0.56    inference(cnf_transformation,[],[f4])).
% 1.43/0.56  fof(f4,axiom,(
% 1.43/0.56    ! [X0,X1,X2] : ((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2))),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).
% 1.43/0.56  fof(f66,plain,(
% 1.43/0.56    sQ8_eqProxy(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | sQ8_eqProxy(sK3,sK7)),
% 1.43/0.56    inference(subsumption_resolution,[],[f64,f44])).
% 1.43/0.56  fof(f44,plain,(
% 1.43/0.56    ~sQ8_eqProxy(k1_xboole_0,sK3)),
% 1.43/0.56    inference(equality_proxy_replacement,[],[f19,f43])).
% 1.43/0.56  fof(f19,plain,(
% 1.43/0.56    k1_xboole_0 != sK3),
% 1.43/0.56    inference(cnf_transformation,[],[f9])).
% 1.43/0.56  fof(f64,plain,(
% 1.43/0.56    sQ8_eqProxy(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | sQ8_eqProxy(k1_xboole_0,sK3) | sQ8_eqProxy(sK3,sK7)),
% 1.43/0.56    inference(resolution,[],[f48,f57])).
% 1.43/0.56  fof(f57,plain,(
% 1.43/0.56    ( ! [X2,X0,X3,X1] : (~sQ8_eqProxy(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) | sQ8_eqProxy(k1_xboole_0,X0) | sQ8_eqProxy(k1_xboole_0,X1) | sQ8_eqProxy(X1,X3)) )),
% 1.43/0.56    inference(equality_proxy_replacement,[],[f29,f43,f43,f43,f43])).
% 1.43/0.56  fof(f29,plain,(
% 1.43/0.56    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | X1 = X3) )),
% 1.43/0.56    inference(cnf_transformation,[],[f13])).
% 1.43/0.56  fof(f13,plain,(
% 1.43/0.56    ! [X0,X1,X2,X3] : ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3))),
% 1.43/0.56    inference(flattening,[],[f12])).
% 1.43/0.56  fof(f12,plain,(
% 1.43/0.56    ! [X0,X1,X2,X3] : (((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3))),
% 1.43/0.56    inference(ennf_transformation,[],[f1])).
% 1.43/0.56  fof(f1,axiom,(
% 1.43/0.56    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 1.43/0.56  fof(f48,plain,(
% 1.43/0.56    sQ8_eqProxy(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 1.43/0.56    inference(equality_proxy_replacement,[],[f32,f43])).
% 1.43/0.56  fof(f32,plain,(
% 1.43/0.56    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)),
% 1.43/0.56    inference(definition_unfolding,[],[f15,f31,f31])).
% 1.43/0.56  fof(f31,plain,(
% 1.43/0.56    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 1.43/0.56    inference(definition_unfolding,[],[f27,f30])).
% 1.43/0.56  fof(f27,plain,(
% 1.43/0.56    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f3])).
% 1.43/0.56  fof(f3,axiom,(
% 1.43/0.56    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 1.43/0.56  fof(f15,plain,(
% 1.43/0.56    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7)),
% 1.43/0.56    inference(cnf_transformation,[],[f9])).
% 1.43/0.56  fof(f90,plain,(
% 1.43/0.56    sQ8_eqProxy(sK2,sK6)),
% 1.43/0.56    inference(subsumption_resolution,[],[f89,f45])).
% 1.43/0.56  fof(f89,plain,(
% 1.43/0.56    sQ8_eqProxy(sK2,sK6) | sQ8_eqProxy(k1_xboole_0,sK2)),
% 1.43/0.56    inference(subsumption_resolution,[],[f88,f46])).
% 1.43/0.56  fof(f88,plain,(
% 1.43/0.56    sQ8_eqProxy(sK2,sK6) | sQ8_eqProxy(k1_xboole_0,sK1) | sQ8_eqProxy(k1_xboole_0,sK2)),
% 1.43/0.56    inference(subsumption_resolution,[],[f87,f47])).
% 1.43/0.56  fof(f87,plain,(
% 1.43/0.56    sQ8_eqProxy(sK2,sK6) | sQ8_eqProxy(k1_xboole_0,sK0) | sQ8_eqProxy(k1_xboole_0,sK1) | sQ8_eqProxy(k1_xboole_0,sK2)),
% 1.43/0.56    inference(resolution,[],[f84,f56])).
% 1.43/0.56  fof(f84,plain,(
% 1.43/0.56    sQ8_eqProxy(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | sQ8_eqProxy(sK2,sK6)),
% 1.43/0.56    inference(duplicate_literal_removal,[],[f81])).
% 1.43/0.56  fof(f81,plain,(
% 1.43/0.56    sQ8_eqProxy(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | sQ8_eqProxy(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | sQ8_eqProxy(sK2,sK6)),
% 1.43/0.56    inference(resolution,[],[f65,f50])).
% 1.43/0.56  fof(f50,plain,(
% 1.43/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (~sQ8_eqProxy(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)) | sQ8_eqProxy(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | sQ8_eqProxy(X2,X5)) )),
% 1.43/0.56    inference(equality_proxy_replacement,[],[f33,f43,f43,f43])).
% 1.43/0.56  fof(f33,plain,(
% 1.43/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | X2 = X5) )),
% 1.43/0.56    inference(definition_unfolding,[],[f22,f30,f30,f30])).
% 1.43/0.56  fof(f22,plain,(
% 1.43/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | X2 = X5) )),
% 1.43/0.56    inference(cnf_transformation,[],[f11])).
% 1.43/0.56  fof(f11,plain,(
% 1.43/0.56    ! [X0,X1,X2,X3,X4,X5] : ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 1.43/0.56    inference(flattening,[],[f10])).
% 1.43/0.56  fof(f10,plain,(
% 1.43/0.56    ! [X0,X1,X2,X3,X4,X5] : (((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 1.43/0.56    inference(ennf_transformation,[],[f5])).
% 1.43/0.56  fof(f5,axiom,(
% 1.43/0.56    ! [X0,X1,X2,X3,X4,X5] : (k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) => ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)))),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_mcart_1)).
% 1.43/0.56  fof(f65,plain,(
% 1.43/0.56    sQ8_eqProxy(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) | sQ8_eqProxy(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.43/0.56    inference(subsumption_resolution,[],[f63,f44])).
% 1.43/0.56  fof(f63,plain,(
% 1.43/0.56    sQ8_eqProxy(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | sQ8_eqProxy(k1_xboole_0,sK3) | sQ8_eqProxy(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))),
% 1.43/0.56    inference(resolution,[],[f48,f58])).
% 1.43/0.56  fof(f58,plain,(
% 1.43/0.56    ( ! [X2,X0,X3,X1] : (~sQ8_eqProxy(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) | sQ8_eqProxy(k1_xboole_0,X0) | sQ8_eqProxy(k1_xboole_0,X1) | sQ8_eqProxy(X0,X2)) )),
% 1.43/0.56    inference(equality_proxy_replacement,[],[f28,f43,f43,f43,f43])).
% 1.43/0.56  fof(f28,plain,(
% 1.43/0.56    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | X0 = X2) )),
% 1.43/0.56    inference(cnf_transformation,[],[f13])).
% 1.43/0.56  fof(f95,plain,(
% 1.43/0.56    sQ8_eqProxy(sK1,sK5)),
% 1.43/0.56    inference(subsumption_resolution,[],[f94,f45])).
% 1.43/0.56  fof(f94,plain,(
% 1.43/0.56    sQ8_eqProxy(sK1,sK5) | sQ8_eqProxy(k1_xboole_0,sK2)),
% 1.43/0.56    inference(subsumption_resolution,[],[f93,f46])).
% 1.43/0.56  fof(f93,plain,(
% 1.43/0.56    sQ8_eqProxy(sK1,sK5) | sQ8_eqProxy(k1_xboole_0,sK1) | sQ8_eqProxy(k1_xboole_0,sK2)),
% 1.43/0.56    inference(subsumption_resolution,[],[f92,f47])).
% 1.43/0.56  fof(f92,plain,(
% 1.43/0.56    sQ8_eqProxy(sK1,sK5) | sQ8_eqProxy(k1_xboole_0,sK0) | sQ8_eqProxy(k1_xboole_0,sK1) | sQ8_eqProxy(k1_xboole_0,sK2)),
% 1.43/0.56    inference(resolution,[],[f85,f56])).
% 1.43/0.56  fof(f85,plain,(
% 1.43/0.56    sQ8_eqProxy(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | sQ8_eqProxy(sK1,sK5)),
% 1.43/0.56    inference(duplicate_literal_removal,[],[f80])).
% 1.43/0.56  fof(f80,plain,(
% 1.43/0.56    sQ8_eqProxy(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | sQ8_eqProxy(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | sQ8_eqProxy(sK1,sK5)),
% 1.43/0.56    inference(resolution,[],[f65,f51])).
% 1.43/0.56  fof(f51,plain,(
% 1.43/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (~sQ8_eqProxy(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)) | sQ8_eqProxy(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | sQ8_eqProxy(X1,X4)) )),
% 1.43/0.56    inference(equality_proxy_replacement,[],[f34,f43,f43,f43])).
% 1.43/0.56  fof(f34,plain,(
% 1.43/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | X1 = X4) )),
% 1.43/0.56    inference(definition_unfolding,[],[f21,f30,f30,f30])).
% 1.43/0.56  fof(f21,plain,(
% 1.43/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | X1 = X4) )),
% 1.43/0.56    inference(cnf_transformation,[],[f11])).
% 1.43/0.56  fof(f97,plain,(
% 1.43/0.56    sQ8_eqProxy(sK0,sK4) | sQ8_eqProxy(k1_xboole_0,sK0) | sQ8_eqProxy(k1_xboole_0,sK1) | sQ8_eqProxy(k1_xboole_0,sK2)),
% 1.43/0.56    inference(resolution,[],[f86,f56])).
% 1.43/0.56  fof(f86,plain,(
% 1.43/0.56    sQ8_eqProxy(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | sQ8_eqProxy(sK0,sK4)),
% 1.43/0.56    inference(duplicate_literal_removal,[],[f79])).
% 1.43/0.56  fof(f79,plain,(
% 1.43/0.56    sQ8_eqProxy(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | sQ8_eqProxy(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | sQ8_eqProxy(sK0,sK4)),
% 1.43/0.56    inference(resolution,[],[f65,f52])).
% 1.43/0.56  fof(f52,plain,(
% 1.43/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (~sQ8_eqProxy(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)) | sQ8_eqProxy(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | sQ8_eqProxy(X0,X3)) )),
% 1.43/0.56    inference(equality_proxy_replacement,[],[f35,f43,f43,f43])).
% 1.43/0.56  fof(f35,plain,(
% 1.43/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | X0 = X3) )),
% 1.43/0.56    inference(definition_unfolding,[],[f20,f30,f30,f30])).
% 1.43/0.56  fof(f20,plain,(
% 1.43/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | X0 = X3) )),
% 1.43/0.56    inference(cnf_transformation,[],[f11])).
% 1.43/0.56  % SZS output end Proof for theBenchmark
% 1.43/0.56  % (20632)------------------------------
% 1.43/0.56  % (20632)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.56  % (20632)Termination reason: Refutation
% 1.43/0.56  
% 1.43/0.56  % (20632)Memory used [KB]: 1663
% 1.43/0.56  % (20632)Time elapsed: 0.151 s
% 1.43/0.56  % (20632)------------------------------
% 1.43/0.56  % (20632)------------------------------
% 1.43/0.56  % (20597)Success in time 0.193 s
%------------------------------------------------------------------------------
