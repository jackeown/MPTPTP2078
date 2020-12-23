%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t127_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:59 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 240 expanded)
%              Number of leaves         :   24 (  83 expanded)
%              Depth                    :   10
%              Number of atoms          :  210 ( 607 expanded)
%              Number of equality atoms :   13 (  36 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f488,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f66,f79,f87,f95,f155,f157,f166,f167,f405,f453,f474,f476,f483,f487])).

fof(f487,plain,
    ( ~ spl7_4
    | spl7_9 ),
    inference(avatar_contradiction_clause,[],[f484])).

fof(f484,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_9 ),
    inference(resolution,[],[f462,f86])).

fof(f86,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl7_9
  <=> ~ r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f462,plain,
    ( ! [X0,X1] : r1_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK1,X1))
    | ~ spl7_4 ),
    inference(resolution,[],[f454,f130])).

fof(f130,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK5(sK4(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)),X0,X1,X2,X3),k3_xboole_0(X0,X2))
      | r1_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(resolution,[],[f50,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t127_zfmisc_1.p',t4_xboole_0)).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)))
      | r2_hidden(sK5(X0,X1,X2,X3,X4),k3_xboole_0(X1,X3)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( r2_hidden(sK6(X0,X1,X2,X3,X4),k3_xboole_0(X2,X4))
        & r2_hidden(sK5(X0,X1,X2,X3,X4),k3_xboole_0(X1,X3))
        & k4_tarski(sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4)) = X0 )
      | ~ r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f28,f33])).

fof(f33,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5,X6] :
          ( r2_hidden(X6,k3_xboole_0(X2,X4))
          & r2_hidden(X5,k3_xboole_0(X1,X3))
          & k4_tarski(X5,X6) = X0 )
     => ( r2_hidden(sK6(X0,X1,X2,X3,X4),k3_xboole_0(X2,X4))
        & r2_hidden(sK5(X0,X1,X2,X3,X4),k3_xboole_0(X1,X3))
        & k4_tarski(sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4)) = X0 ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ? [X5,X6] :
          ( r2_hidden(X6,k3_xboole_0(X2,X4))
          & r2_hidden(X5,k3_xboole_0(X1,X3))
          & k4_tarski(X5,X6) = X0 )
      | ~ r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ~ ( ! [X5,X6] :
            ~ ( r2_hidden(X6,k3_xboole_0(X2,X4))
              & r2_hidden(X5,k3_xboole_0(X1,X3))
              & k4_tarski(X5,X6) = X0 )
        & r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t127_zfmisc_1.p',t104_zfmisc_1)).

fof(f454,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK0,sK1))
    | ~ spl7_4 ),
    inference(resolution,[],[f72,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f72,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl7_4
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f483,plain,
    ( spl7_18
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f461,f71,f481])).

fof(f481,plain,
    ( spl7_18
  <=> r1_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f461,plain,
    ( r1_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))
    | ~ spl7_4 ),
    inference(resolution,[],[f454,f113])).

fof(f113,plain,(
    ! [X1] :
      ( r2_hidden(sK4(X1,X1),X1)
      | r1_xboole_0(X1,X1) ) ),
    inference(superposition,[],[f43,f41])).

fof(f41,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t127_zfmisc_1.p',idempotence_k3_xboole_0)).

fof(f476,plain,
    ( spl7_11
    | ~ spl7_12 ),
    inference(avatar_contradiction_clause,[],[f475])).

fof(f475,plain,
    ( $false
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f467,f91])).

fof(f91,plain,
    ( ~ r1_xboole_0(sK3,sK2)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl7_11
  <=> ~ r1_xboole_0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f467,plain,
    ( r1_xboole_0(sK3,sK2)
    | ~ spl7_12 ),
    inference(resolution,[],[f174,f114])).

fof(f114,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK4(X2,X3),k3_xboole_0(X3,X2))
      | r1_xboole_0(X2,X3) ) ),
    inference(superposition,[],[f43,f42])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t127_zfmisc_1.p',commutativity_k3_xboole_0)).

fof(f174,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK2,sK3))
    | ~ spl7_12 ),
    inference(forward_demodulation,[],[f172,f41])).

fof(f172,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK3)))
    | ~ spl7_12 ),
    inference(resolution,[],[f154,f44])).

fof(f154,plain,
    ( r1_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK3))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl7_12
  <=> r1_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f474,plain,
    ( spl7_7
    | ~ spl7_12 ),
    inference(avatar_contradiction_clause,[],[f473])).

fof(f473,plain,
    ( $false
    | ~ spl7_7
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f466,f75])).

fof(f75,plain,
    ( ~ r1_xboole_0(sK2,sK3)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl7_7
  <=> ~ r1_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f466,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ spl7_12 ),
    inference(resolution,[],[f174,f43])).

fof(f453,plain,
    ( spl7_9
    | ~ spl7_10 ),
    inference(avatar_contradiction_clause,[],[f450])).

fof(f450,plain,
    ( $false
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(resolution,[],[f440,f86])).

fof(f440,plain,
    ( ! [X61,X60] : r1_xboole_0(k2_zfmisc_1(X60,sK2),k2_zfmisc_1(X61,sK3))
    | ~ spl7_10 ),
    inference(resolution,[],[f198,f108])).

fof(f108,plain,
    ( ! [X1] : ~ r2_hidden(X1,k3_xboole_0(sK2,sK3))
    | ~ spl7_10 ),
    inference(forward_demodulation,[],[f107,f42])).

fof(f107,plain,
    ( ! [X1] : ~ r2_hidden(X1,k3_xboole_0(sK3,sK2))
    | ~ spl7_10 ),
    inference(resolution,[],[f44,f94])).

fof(f94,plain,
    ( r1_xboole_0(sK3,sK2)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl7_10
  <=> r1_xboole_0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f198,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK6(sK4(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)),X0,X1,X2,X3),k3_xboole_0(X1,X3))
      | r1_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(resolution,[],[f51,f43])).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)))
      | r2_hidden(sK6(X0,X1,X2,X3,X4),k3_xboole_0(X2,X4)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f405,plain,
    ( ~ spl7_17
    | spl7_9 ),
    inference(avatar_split_clause,[],[f396,f85,f403])).

fof(f403,plain,
    ( spl7_17
  <=> ~ v1_xboole_0(k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f396,plain,
    ( ~ v1_xboole_0(k3_xboole_0(sK0,sK1))
    | ~ spl7_9 ),
    inference(resolution,[],[f323,f86])).

fof(f323,plain,(
    ! [X39,X37,X38,X36] :
      ( r1_xboole_0(k2_zfmisc_1(X36,X37),k2_zfmisc_1(X38,X39))
      | ~ v1_xboole_0(k3_xboole_0(X36,X38)) ) ),
    inference(resolution,[],[f130,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t127_zfmisc_1.p',t7_boole)).

fof(f167,plain,
    ( spl7_6
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f96,f93,f77])).

fof(f77,plain,
    ( spl7_6
  <=> r1_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f96,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ spl7_10 ),
    inference(resolution,[],[f94,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t127_zfmisc_1.p',symmetry_r1_xboole_0)).

fof(f166,plain,
    ( spl7_14
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f159,f71,f164])).

fof(f164,plain,
    ( spl7_14
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f159,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl7_4 ),
    inference(resolution,[],[f72,f46])).

fof(f157,plain,
    ( spl7_7
    | ~ spl7_10 ),
    inference(avatar_contradiction_clause,[],[f156])).

fof(f156,plain,
    ( $false
    | ~ spl7_7
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f75,f96])).

fof(f155,plain,
    ( spl7_12
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f146,f77,f153])).

fof(f146,plain,
    ( r1_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK3))
    | ~ spl7_6 ),
    inference(resolution,[],[f113,f106])).

fof(f106,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK2,sK3))
    | ~ spl7_6 ),
    inference(resolution,[],[f44,f78])).

fof(f78,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f77])).

fof(f95,plain,
    ( spl7_10
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f88,f77,f93])).

fof(f88,plain,
    ( r1_xboole_0(sK3,sK2)
    | ~ spl7_6 ),
    inference(resolution,[],[f46,f78])).

fof(f87,plain,(
    ~ spl7_9 ),
    inference(avatar_split_clause,[],[f36,f85])).

fof(f36,plain,(
    ~ r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))
    & ( r1_xboole_0(sK2,sK3)
      | r1_xboole_0(sK0,sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
        & ( r1_xboole_0(X2,X3)
          | r1_xboole_0(X0,X1) ) )
   => ( ~ r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))
      & ( r1_xboole_0(sK2,sK3)
        | r1_xboole_0(sK0,sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      & ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X3)
          | r1_xboole_0(X0,X1) )
       => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t127_zfmisc_1.p',t127_zfmisc_1)).

fof(f79,plain,
    ( spl7_4
    | spl7_6 ),
    inference(avatar_split_clause,[],[f35,f77,f71])).

fof(f35,plain,
    ( r1_xboole_0(sK2,sK3)
    | r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f66,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f38,f64])).

fof(f64,plain,
    ( spl7_2
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f38,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t127_zfmisc_1.p',d2_xboole_0)).

fof(f59,plain,(
    spl7_0 ),
    inference(avatar_split_clause,[],[f52,f57])).

fof(f57,plain,
    ( spl7_0
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_0])])).

fof(f52,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f37,f38])).

fof(f37,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t127_zfmisc_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
