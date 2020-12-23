%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t52_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:10 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 114 expanded)
%              Number of leaves         :   13 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :  129 ( 255 expanded)
%              Number of equality atoms :    2 (  12 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f170,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f25,f44,f52,f68,f79,f88,f91,f162,f167])).

fof(f167,plain,
    ( spl6_1
    | ~ spl6_6 ),
    inference(avatar_contradiction_clause,[],[f166])).

fof(f166,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f163,f43])).

fof(f43,plain,
    ( r1_xboole_0(sK2,sK5)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl6_6
  <=> r1_xboole_0(sK2,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f163,plain,
    ( ~ r1_xboole_0(sK2,sK5)
    | ~ spl6_1 ),
    inference(resolution,[],[f134,f24])).

fof(f24,plain,
    ( ~ r1_xboole_0(k3_zfmisc_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f23])).

fof(f23,plain,
    ( spl6_1
  <=> ~ r1_xboole_0(k3_zfmisc_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f134,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_xboole_0(k3_zfmisc_1(X3,X4,X5),k3_zfmisc_1(X0,X1,X2))
      | ~ r1_xboole_0(X5,X2) ) ),
    inference(superposition,[],[f110,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t52_mcart_1.p',d3_zfmisc_1)).

fof(f110,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r1_xboole_0(k3_zfmisc_1(X0,X1,X2),k2_zfmisc_1(X3,X4))
      | ~ r1_xboole_0(X2,X4) ) ),
    inference(superposition,[],[f18,f16])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ( ~ r1_xboole_0(X2,X3)
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t52_mcart_1.p',t127_zfmisc_1)).

fof(f162,plain,
    ( ~ spl6_11
    | spl6_1 ),
    inference(avatar_split_clause,[],[f157,f23,f74])).

fof(f74,plain,
    ( spl6_11
  <=> ~ r1_xboole_0(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f157,plain,
    ( ~ r1_xboole_0(sK4,sK1)
    | ~ spl6_1 ),
    inference(resolution,[],[f119,f24])).

fof(f119,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_xboole_0(k3_zfmisc_1(X2,X1,X3),k3_zfmisc_1(X4,X0,X5))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(forward_demodulation,[],[f118,f16])).

fof(f118,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X2,X1),X3),k3_zfmisc_1(X4,X0,X5))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(forward_demodulation,[],[f114,f16])).

fof(f114,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X2,X1),X3),k2_zfmisc_1(k2_zfmisc_1(X4,X0),X5)) ) ),
    inference(resolution,[],[f109,f17])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f109,plain,(
    ! [X6,X8,X7,X9] :
      ( r1_xboole_0(k2_zfmisc_1(X8,X7),k2_zfmisc_1(X9,X6))
      | ~ r1_xboole_0(X6,X7) ) ),
    inference(resolution,[],[f18,f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t52_mcart_1.p',symmetry_r1_xboole_0)).

fof(f91,plain,
    ( spl6_2
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f53,f50,f30])).

fof(f30,plain,
    ( spl6_2
  <=> r1_xboole_0(sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f50,plain,
    ( spl6_8
  <=> r1_xboole_0(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f53,plain,
    ( r1_xboole_0(sK0,sK3)
    | ~ spl6_8 ),
    inference(resolution,[],[f51,f15])).

fof(f51,plain,
    ( r1_xboole_0(sK3,sK0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f50])).

fof(f88,plain,
    ( spl6_12
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f81,f42,f86])).

fof(f86,plain,
    ( spl6_12
  <=> r1_xboole_0(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f81,plain,
    ( r1_xboole_0(sK5,sK2)
    | ~ spl6_6 ),
    inference(resolution,[],[f43,f15])).

fof(f79,plain,
    ( spl6_10
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f72,f36,f77])).

fof(f77,plain,
    ( spl6_10
  <=> r1_xboole_0(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f36,plain,
    ( spl6_4
  <=> r1_xboole_0(sK1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f72,plain,
    ( r1_xboole_0(sK4,sK1)
    | ~ spl6_4 ),
    inference(resolution,[],[f37,f15])).

fof(f37,plain,
    ( r1_xboole_0(sK1,sK4)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f36])).

fof(f68,plain,
    ( spl6_1
    | ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f65])).

fof(f65,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(resolution,[],[f60,f24])).

fof(f60,plain,
    ( ! [X2,X0,X3,X1] : r1_xboole_0(k3_zfmisc_1(sK0,X0,X1),k3_zfmisc_1(sK3,X2,X3))
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f59,f16])).

fof(f59,plain,
    ( ! [X2,X0,X3,X1] : r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1),k3_zfmisc_1(sK3,X2,X3))
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f57,f16])).

fof(f57,plain,
    ( ! [X2,X0,X3,X1] : r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1),k2_zfmisc_1(k2_zfmisc_1(sK3,X2),X3))
    | ~ spl6_2 ),
    inference(resolution,[],[f55,f17])).

fof(f55,plain,
    ( ! [X0,X1] : r1_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK3,X1))
    | ~ spl6_2 ),
    inference(resolution,[],[f17,f31])).

fof(f31,plain,
    ( r1_xboole_0(sK0,sK3)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f52,plain,
    ( spl6_8
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f45,f30,f50])).

fof(f45,plain,
    ( r1_xboole_0(sK3,sK0)
    | ~ spl6_2 ),
    inference(resolution,[],[f31,f15])).

fof(f44,plain,
    ( spl6_2
    | spl6_4
    | spl6_6 ),
    inference(avatar_split_clause,[],[f14,f42,f36,f30])).

fof(f14,plain,
    ( r1_xboole_0(sK2,sK5)
    | r1_xboole_0(sK1,sK4)
    | r1_xboole_0(sK0,sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ( r1_xboole_0(sK2,sK5)
      | r1_xboole_0(sK1,sK4)
      | r1_xboole_0(sK0,sK3) )
    & ~ r1_xboole_0(k3_zfmisc_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f8,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ( r1_xboole_0(X2,X5)
          | r1_xboole_0(X1,X4)
          | r1_xboole_0(X0,X3) )
        & ~ r1_xboole_0(k3_zfmisc_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) )
   => ( ( r1_xboole_0(sK2,sK5)
        | r1_xboole_0(sK1,sK4)
        | r1_xboole_0(sK0,sK3) )
      & ~ r1_xboole_0(k3_zfmisc_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( r1_xboole_0(X2,X5)
        | r1_xboole_0(X1,X4)
        | r1_xboole_0(X0,X3) )
      & ~ r1_xboole_0(k3_zfmisc_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( ~ r1_xboole_0(k3_zfmisc_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
       => ( ~ r1_xboole_0(X2,X5)
          & ~ r1_xboole_0(X1,X4)
          & ~ r1_xboole_0(X0,X3) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_xboole_0(k3_zfmisc_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
     => ( ~ r1_xboole_0(X2,X5)
        & ~ r1_xboole_0(X1,X4)
        & ~ r1_xboole_0(X0,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t52_mcart_1.p',t52_mcart_1)).

fof(f25,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f13,f23])).

fof(f13,plain,(
    ~ r1_xboole_0(k3_zfmisc_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
