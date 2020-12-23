%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:02 EST 2020

% Result     : Theorem 5.70s
% Output     : Refutation 5.70s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 126 expanded)
%              Number of leaves         :   24 (  46 expanded)
%              Depth                    :    8
%              Number of atoms          :  195 ( 305 expanded)
%              Number of equality atoms :   15 (  17 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18531,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f8247,f8303,f13422,f13426,f17301,f18524,f18526,f18530])).

fof(f18530,plain,(
    spl2_14 ),
    inference(avatar_contradiction_clause,[],[f18527])).

fof(f18527,plain,
    ( $false
    | spl2_14 ),
    inference(resolution,[],[f18523,f4077])).

fof(f4077,plain,(
    ! [X2,X0] : r1_tarski(k3_xboole_0(X2,X0),X0) ),
    inference(forward_demodulation,[],[f4076,f1160])).

fof(f1160,plain,(
    ! [X8,X7,X9] : k3_xboole_0(X7,X8) = k2_xboole_0(k3_xboole_0(X7,k3_xboole_0(X8,X9)),k4_xboole_0(k3_xboole_0(X7,X8),X9)) ),
    inference(superposition,[],[f46,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f4076,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X2,k3_xboole_0(X0,X1)),k4_xboole_0(k3_xboole_0(X2,X0),X1)),X0) ),
    inference(forward_demodulation,[],[f4052,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f4052,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X2,k3_xboole_0(X0,X1)),k3_xboole_0(X2,k4_xboole_0(X0,X1))),X0) ),
    inference(superposition,[],[f55,f46])).

fof(f55,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

fof(f18523,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK1)
    | spl2_14 ),
    inference(avatar_component_clause,[],[f18521])).

fof(f18521,plain,
    ( spl2_14
  <=> r1_tarski(k3_xboole_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f18526,plain,(
    spl2_13 ),
    inference(avatar_contradiction_clause,[],[f18525])).

fof(f18525,plain,
    ( $false
    | spl2_13 ),
    inference(subsumption_resolution,[],[f35,f18519])).

fof(f18519,plain,
    ( ~ v1_relat_1(sK1)
    | spl2_13 ),
    inference(avatar_component_clause,[],[f18517])).

fof(f18517,plain,
    ( spl2_13
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f35,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_relat_1)).

fof(f18524,plain,
    ( ~ spl2_5
    | ~ spl2_13
    | ~ spl2_14
    | spl2_10 ),
    inference(avatar_split_clause,[],[f18513,f17298,f18521,f18517,f8270])).

fof(f8270,plain,
    ( spl2_5
  <=> v1_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f17298,plain,
    ( spl2_10
  <=> r1_xboole_0(k2_relat_1(k3_xboole_0(sK0,sK1)),k4_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f18513,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | spl2_10 ),
    inference(resolution,[],[f18504,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f18504,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK1))
    | spl2_10 ),
    inference(superposition,[],[f17391,f68])).

fof(f68,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(resolution,[],[f62,f40])).

fof(f40,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f62,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X3,X2)
      | k4_xboole_0(X2,X3) = X2 ) ),
    inference(resolution,[],[f48,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f17391,plain,
    ( ! [X0] : ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k4_xboole_0(X0,k4_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))))
    | spl2_10 ),
    inference(resolution,[],[f17300,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f17300,plain,
    ( ~ r1_xboole_0(k2_relat_1(k3_xboole_0(sK0,sK1)),k4_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))
    | spl2_10 ),
    inference(avatar_component_clause,[],[f17298])).

fof(f17301,plain,
    ( ~ spl2_1
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f17274,f17298,f5691])).

fof(f5691,plain,
    ( spl2_1
  <=> r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f17274,plain,
    ( ~ r1_xboole_0(k2_relat_1(k3_xboole_0(sK0,sK1)),k4_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))
    | ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK0)) ),
    inference(resolution,[],[f5683,f36])).

fof(f36,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f31])).

fof(f5683,plain,(
    ! [X19,X20,X18] :
      ( r1_tarski(X20,k3_xboole_0(X18,X19))
      | ~ r1_xboole_0(X20,k4_xboole_0(X18,X19))
      | ~ r1_tarski(X20,X18) ) ),
    inference(superposition,[],[f58,f45])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f13426,plain,(
    spl2_9 ),
    inference(avatar_contradiction_clause,[],[f13423])).

fof(f13423,plain,
    ( $false
    | spl2_9 ),
    inference(resolution,[],[f13421,f41])).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f13421,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0)
    | spl2_9 ),
    inference(avatar_component_clause,[],[f13419])).

fof(f13419,plain,
    ( spl2_9
  <=> r1_tarski(k3_xboole_0(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f13422,plain,
    ( ~ spl2_5
    | ~ spl2_3
    | ~ spl2_9
    | spl2_1 ),
    inference(avatar_split_clause,[],[f13415,f5691,f13419,f8239,f8270])).

fof(f8239,plain,
    ( spl2_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f13415,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | spl2_1 ),
    inference(resolution,[],[f5693,f38])).

fof(f5693,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f5691])).

fof(f8303,plain,(
    spl2_5 ),
    inference(avatar_contradiction_clause,[],[f8302])).

fof(f8302,plain,
    ( $false
    | spl2_5 ),
    inference(subsumption_resolution,[],[f34,f8279])).

fof(f8279,plain,
    ( ~ v1_relat_1(sK0)
    | spl2_5 ),
    inference(resolution,[],[f8278,f41])).

fof(f8278,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k3_xboole_0(sK0,sK1),X0)
        | ~ v1_relat_1(X0) )
    | spl2_5 ),
    inference(resolution,[],[f8277,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f8277,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k3_xboole_0(sK0,sK1),k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl2_5 ),
    inference(resolution,[],[f8272,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f8272,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f8270])).

fof(f34,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f8247,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f8246])).

fof(f8246,plain,
    ( $false
    | spl2_3 ),
    inference(subsumption_resolution,[],[f34,f8241])).

fof(f8241,plain,
    ( ~ v1_relat_1(sK0)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f8239])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:36:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.44  % (26830)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.44  % (26833)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.45  % (26831)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.46  % (26827)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.46  % (26839)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.47  % (26828)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (26834)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.48  % (26829)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (26824)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.48  % (26832)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.48  % (26837)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.49  % (26835)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.50  % (26840)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.50  % (26825)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.51  % (26836)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.51  % (26835)Refutation not found, incomplete strategy% (26835)------------------------------
% 0.22/0.51  % (26835)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (26835)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (26835)Memory used [KB]: 10618
% 0.22/0.51  % (26835)Time elapsed: 0.090 s
% 0.22/0.51  % (26835)------------------------------
% 0.22/0.51  % (26835)------------------------------
% 0.22/0.51  % (26841)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.51  % (26826)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.52  % (26838)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 5.08/1.03  % (26828)Time limit reached!
% 5.08/1.03  % (26828)------------------------------
% 5.08/1.03  % (26828)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.08/1.03  % (26828)Termination reason: Time limit
% 5.08/1.03  
% 5.08/1.03  % (26828)Memory used [KB]: 15095
% 5.08/1.03  % (26828)Time elapsed: 0.610 s
% 5.08/1.03  % (26828)------------------------------
% 5.08/1.03  % (26828)------------------------------
% 5.70/1.12  % (26840)Refutation found. Thanks to Tanya!
% 5.70/1.12  % SZS status Theorem for theBenchmark
% 5.70/1.13  % SZS output start Proof for theBenchmark
% 5.70/1.13  fof(f18531,plain,(
% 5.70/1.13    $false),
% 5.70/1.13    inference(avatar_sat_refutation,[],[f8247,f8303,f13422,f13426,f17301,f18524,f18526,f18530])).
% 5.70/1.13  fof(f18530,plain,(
% 5.70/1.13    spl2_14),
% 5.70/1.13    inference(avatar_contradiction_clause,[],[f18527])).
% 5.70/1.13  fof(f18527,plain,(
% 5.70/1.13    $false | spl2_14),
% 5.70/1.13    inference(resolution,[],[f18523,f4077])).
% 5.70/1.13  fof(f4077,plain,(
% 5.70/1.13    ( ! [X2,X0] : (r1_tarski(k3_xboole_0(X2,X0),X0)) )),
% 5.70/1.13    inference(forward_demodulation,[],[f4076,f1160])).
% 5.70/1.13  fof(f1160,plain,(
% 5.70/1.13    ( ! [X8,X7,X9] : (k3_xboole_0(X7,X8) = k2_xboole_0(k3_xboole_0(X7,k3_xboole_0(X8,X9)),k4_xboole_0(k3_xboole_0(X7,X8),X9))) )),
% 5.70/1.13    inference(superposition,[],[f46,f54])).
% 5.70/1.13  fof(f54,plain,(
% 5.70/1.13    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 5.70/1.13    inference(cnf_transformation,[],[f3])).
% 5.70/1.13  fof(f3,axiom,(
% 5.70/1.13    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 5.70/1.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 5.70/1.13  fof(f46,plain,(
% 5.70/1.13    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 5.70/1.13    inference(cnf_transformation,[],[f8])).
% 5.70/1.13  fof(f8,axiom,(
% 5.70/1.13    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 5.70/1.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 5.70/1.13  fof(f4076,plain,(
% 5.70/1.13    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X2,k3_xboole_0(X0,X1)),k4_xboole_0(k3_xboole_0(X2,X0),X1)),X0)) )),
% 5.70/1.13    inference(forward_demodulation,[],[f4052,f53])).
% 5.70/1.13  fof(f53,plain,(
% 5.70/1.13    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 5.70/1.13    inference(cnf_transformation,[],[f7])).
% 5.70/1.13  fof(f7,axiom,(
% 5.70/1.13    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 5.70/1.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 5.70/1.13  fof(f4052,plain,(
% 5.70/1.13    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X2,k3_xboole_0(X0,X1)),k3_xboole_0(X2,k4_xboole_0(X0,X1))),X0)) )),
% 5.70/1.13    inference(superposition,[],[f55,f46])).
% 5.70/1.13  fof(f55,plain,(
% 5.70/1.13    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 5.70/1.13    inference(cnf_transformation,[],[f5])).
% 5.70/1.13  fof(f5,axiom,(
% 5.70/1.13    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 5.70/1.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).
% 5.70/1.13  fof(f18523,plain,(
% 5.70/1.13    ~r1_tarski(k3_xboole_0(sK0,sK1),sK1) | spl2_14),
% 5.70/1.13    inference(avatar_component_clause,[],[f18521])).
% 5.70/1.13  fof(f18521,plain,(
% 5.70/1.13    spl2_14 <=> r1_tarski(k3_xboole_0(sK0,sK1),sK1)),
% 5.70/1.13    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 5.70/1.13  fof(f18526,plain,(
% 5.70/1.13    spl2_13),
% 5.70/1.13    inference(avatar_contradiction_clause,[],[f18525])).
% 5.70/1.13  fof(f18525,plain,(
% 5.70/1.13    $false | spl2_13),
% 5.70/1.13    inference(subsumption_resolution,[],[f35,f18519])).
% 5.70/1.13  fof(f18519,plain,(
% 5.70/1.13    ~v1_relat_1(sK1) | spl2_13),
% 5.70/1.13    inference(avatar_component_clause,[],[f18517])).
% 5.70/1.13  fof(f18517,plain,(
% 5.70/1.13    spl2_13 <=> v1_relat_1(sK1)),
% 5.70/1.13    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 5.70/1.13  fof(f35,plain,(
% 5.70/1.13    v1_relat_1(sK1)),
% 5.70/1.13    inference(cnf_transformation,[],[f31])).
% 5.70/1.13  fof(f31,plain,(
% 5.70/1.13    (~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 5.70/1.13    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f30,f29])).
% 5.70/1.13  fof(f29,plain,(
% 5.70/1.13    ? [X0] : (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 5.70/1.13    introduced(choice_axiom,[])).
% 5.70/1.13  fof(f30,plain,(
% 5.70/1.13    ? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) & v1_relat_1(sK1))),
% 5.70/1.13    introduced(choice_axiom,[])).
% 5.70/1.13  fof(f21,plain,(
% 5.70/1.13    ? [X0] : (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 5.70/1.13    inference(ennf_transformation,[],[f20])).
% 5.70/1.13  fof(f20,negated_conjecture,(
% 5.70/1.13    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))))),
% 5.70/1.13    inference(negated_conjecture,[],[f19])).
% 5.70/1.13  fof(f19,conjecture,(
% 5.70/1.13    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))))),
% 5.70/1.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_relat_1)).
% 5.70/1.13  fof(f18524,plain,(
% 5.70/1.13    ~spl2_5 | ~spl2_13 | ~spl2_14 | spl2_10),
% 5.70/1.13    inference(avatar_split_clause,[],[f18513,f17298,f18521,f18517,f8270])).
% 5.70/1.13  fof(f8270,plain,(
% 5.70/1.13    spl2_5 <=> v1_relat_1(k3_xboole_0(sK0,sK1))),
% 5.70/1.13    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 5.70/1.13  fof(f17298,plain,(
% 5.70/1.13    spl2_10 <=> r1_xboole_0(k2_relat_1(k3_xboole_0(sK0,sK1)),k4_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))),
% 5.70/1.13    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 5.70/1.13  fof(f18513,plain,(
% 5.70/1.13    ~r1_tarski(k3_xboole_0(sK0,sK1),sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(k3_xboole_0(sK0,sK1)) | spl2_10),
% 5.70/1.13    inference(resolution,[],[f18504,f38])).
% 5.70/1.13  fof(f38,plain,(
% 5.70/1.13    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 5.70/1.13    inference(cnf_transformation,[],[f23])).
% 5.70/1.13  fof(f23,plain,(
% 5.70/1.13    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 5.70/1.13    inference(flattening,[],[f22])).
% 5.70/1.13  fof(f22,plain,(
% 5.70/1.13    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 5.70/1.13    inference(ennf_transformation,[],[f18])).
% 5.70/1.13  fof(f18,axiom,(
% 5.70/1.13    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 5.70/1.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 5.70/1.13  fof(f18504,plain,(
% 5.70/1.13    ~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK1)) | spl2_10),
% 5.70/1.13    inference(superposition,[],[f17391,f68])).
% 5.70/1.13  fof(f68,plain,(
% 5.70/1.13    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0) )),
% 5.70/1.13    inference(resolution,[],[f62,f40])).
% 5.70/1.13  fof(f40,plain,(
% 5.70/1.13    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 5.70/1.13    inference(cnf_transformation,[],[f9])).
% 5.70/1.13  fof(f9,axiom,(
% 5.70/1.13    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 5.70/1.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 5.70/1.13  fof(f62,plain,(
% 5.70/1.13    ( ! [X2,X3] : (~r1_xboole_0(X3,X2) | k4_xboole_0(X2,X3) = X2) )),
% 5.70/1.13    inference(resolution,[],[f48,f47])).
% 5.70/1.13  fof(f47,plain,(
% 5.70/1.13    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 5.70/1.13    inference(cnf_transformation,[],[f25])).
% 5.70/1.13  fof(f25,plain,(
% 5.70/1.13    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 5.70/1.13    inference(ennf_transformation,[],[f1])).
% 5.70/1.13  fof(f1,axiom,(
% 5.70/1.13    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 5.70/1.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 5.70/1.13  fof(f48,plain,(
% 5.70/1.13    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 5.70/1.13    inference(cnf_transformation,[],[f32])).
% 5.70/1.13  fof(f32,plain,(
% 5.70/1.13    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 5.70/1.13    inference(nnf_transformation,[],[f10])).
% 5.70/1.13  fof(f10,axiom,(
% 5.70/1.13    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 5.70/1.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 5.70/1.13  fof(f17391,plain,(
% 5.70/1.13    ( ! [X0] : (~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k4_xboole_0(X0,k4_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))))) ) | spl2_10),
% 5.70/1.13    inference(resolution,[],[f17300,f57])).
% 5.70/1.13  fof(f57,plain,(
% 5.70/1.13    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 5.70/1.13    inference(cnf_transformation,[],[f26])).
% 5.70/1.13  fof(f26,plain,(
% 5.70/1.13    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 5.70/1.13    inference(ennf_transformation,[],[f2])).
% 5.70/1.13  fof(f2,axiom,(
% 5.70/1.13    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 5.70/1.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 5.70/1.13  fof(f17300,plain,(
% 5.70/1.13    ~r1_xboole_0(k2_relat_1(k3_xboole_0(sK0,sK1)),k4_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) | spl2_10),
% 5.70/1.13    inference(avatar_component_clause,[],[f17298])).
% 5.70/1.13  fof(f17301,plain,(
% 5.70/1.13    ~spl2_1 | ~spl2_10),
% 5.70/1.13    inference(avatar_split_clause,[],[f17274,f17298,f5691])).
% 5.70/1.13  fof(f5691,plain,(
% 5.70/1.13    spl2_1 <=> r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK0))),
% 5.70/1.13    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 5.70/1.13  fof(f17274,plain,(
% 5.70/1.13    ~r1_xboole_0(k2_relat_1(k3_xboole_0(sK0,sK1)),k4_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) | ~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK0))),
% 5.70/1.13    inference(resolution,[],[f5683,f36])).
% 5.70/1.13  fof(f36,plain,(
% 5.70/1.13    ~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))),
% 5.70/1.13    inference(cnf_transformation,[],[f31])).
% 5.70/1.13  fof(f5683,plain,(
% 5.70/1.13    ( ! [X19,X20,X18] : (r1_tarski(X20,k3_xboole_0(X18,X19)) | ~r1_xboole_0(X20,k4_xboole_0(X18,X19)) | ~r1_tarski(X20,X18)) )),
% 5.70/1.13    inference(superposition,[],[f58,f45])).
% 5.70/1.13  fof(f45,plain,(
% 5.70/1.13    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 5.70/1.13    inference(cnf_transformation,[],[f6])).
% 5.70/1.13  fof(f6,axiom,(
% 5.70/1.13    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 5.70/1.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 5.70/1.13  fof(f58,plain,(
% 5.70/1.13    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 5.70/1.13    inference(cnf_transformation,[],[f28])).
% 5.70/1.13  fof(f28,plain,(
% 5.70/1.13    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 5.70/1.13    inference(flattening,[],[f27])).
% 5.70/1.13  fof(f27,plain,(
% 5.70/1.13    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 5.70/1.13    inference(ennf_transformation,[],[f11])).
% 5.70/1.13  fof(f11,axiom,(
% 5.70/1.13    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 5.70/1.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).
% 5.70/1.13  fof(f13426,plain,(
% 5.70/1.13    spl2_9),
% 5.70/1.13    inference(avatar_contradiction_clause,[],[f13423])).
% 5.70/1.13  fof(f13423,plain,(
% 5.70/1.13    $false | spl2_9),
% 5.70/1.13    inference(resolution,[],[f13421,f41])).
% 5.70/1.13  fof(f41,plain,(
% 5.70/1.13    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 5.70/1.13    inference(cnf_transformation,[],[f4])).
% 5.70/1.13  fof(f4,axiom,(
% 5.70/1.13    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 5.70/1.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 5.70/1.13  fof(f13421,plain,(
% 5.70/1.13    ~r1_tarski(k3_xboole_0(sK0,sK1),sK0) | spl2_9),
% 5.70/1.13    inference(avatar_component_clause,[],[f13419])).
% 5.70/1.13  fof(f13419,plain,(
% 5.70/1.13    spl2_9 <=> r1_tarski(k3_xboole_0(sK0,sK1),sK0)),
% 5.70/1.13    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 5.70/1.13  fof(f13422,plain,(
% 5.70/1.13    ~spl2_5 | ~spl2_3 | ~spl2_9 | spl2_1),
% 5.70/1.13    inference(avatar_split_clause,[],[f13415,f5691,f13419,f8239,f8270])).
% 5.70/1.13  fof(f8239,plain,(
% 5.70/1.13    spl2_3 <=> v1_relat_1(sK0)),
% 5.70/1.13    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 5.70/1.13  fof(f13415,plain,(
% 5.70/1.13    ~r1_tarski(k3_xboole_0(sK0,sK1),sK0) | ~v1_relat_1(sK0) | ~v1_relat_1(k3_xboole_0(sK0,sK1)) | spl2_1),
% 5.70/1.13    inference(resolution,[],[f5693,f38])).
% 5.70/1.13  fof(f5693,plain,(
% 5.70/1.13    ~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK0)) | spl2_1),
% 5.70/1.13    inference(avatar_component_clause,[],[f5691])).
% 5.70/1.13  fof(f8303,plain,(
% 5.70/1.13    spl2_5),
% 5.70/1.13    inference(avatar_contradiction_clause,[],[f8302])).
% 5.70/1.13  fof(f8302,plain,(
% 5.70/1.13    $false | spl2_5),
% 5.70/1.13    inference(subsumption_resolution,[],[f34,f8279])).
% 5.70/1.13  fof(f8279,plain,(
% 5.70/1.13    ~v1_relat_1(sK0) | spl2_5),
% 5.70/1.13    inference(resolution,[],[f8278,f41])).
% 5.70/1.13  fof(f8278,plain,(
% 5.70/1.13    ( ! [X0] : (~r1_tarski(k3_xboole_0(sK0,sK1),X0) | ~v1_relat_1(X0)) ) | spl2_5),
% 5.70/1.13    inference(resolution,[],[f8277,f51])).
% 5.70/1.13  fof(f51,plain,(
% 5.70/1.13    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 5.70/1.13    inference(cnf_transformation,[],[f33])).
% 5.70/1.13  fof(f33,plain,(
% 5.70/1.13    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 5.70/1.13    inference(nnf_transformation,[],[f16])).
% 5.70/1.13  fof(f16,axiom,(
% 5.70/1.13    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 5.70/1.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 5.70/1.13  fof(f8277,plain,(
% 5.70/1.13    ( ! [X0] : (~m1_subset_1(k3_xboole_0(sK0,sK1),k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl2_5),
% 5.70/1.13    inference(resolution,[],[f8272,f39])).
% 5.70/1.13  fof(f39,plain,(
% 5.70/1.13    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 5.70/1.13    inference(cnf_transformation,[],[f24])).
% 5.70/1.13  fof(f24,plain,(
% 5.70/1.13    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 5.70/1.13    inference(ennf_transformation,[],[f17])).
% 5.70/1.13  fof(f17,axiom,(
% 5.70/1.13    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 5.70/1.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 5.70/1.13  fof(f8272,plain,(
% 5.70/1.13    ~v1_relat_1(k3_xboole_0(sK0,sK1)) | spl2_5),
% 5.70/1.13    inference(avatar_component_clause,[],[f8270])).
% 5.70/1.13  fof(f34,plain,(
% 5.70/1.13    v1_relat_1(sK0)),
% 5.70/1.13    inference(cnf_transformation,[],[f31])).
% 5.70/1.13  fof(f8247,plain,(
% 5.70/1.13    spl2_3),
% 5.70/1.13    inference(avatar_contradiction_clause,[],[f8246])).
% 5.70/1.13  fof(f8246,plain,(
% 5.70/1.13    $false | spl2_3),
% 5.70/1.13    inference(subsumption_resolution,[],[f34,f8241])).
% 5.70/1.13  fof(f8241,plain,(
% 5.70/1.13    ~v1_relat_1(sK0) | spl2_3),
% 5.70/1.13    inference(avatar_component_clause,[],[f8239])).
% 5.70/1.13  % SZS output end Proof for theBenchmark
% 5.70/1.13  % (26840)------------------------------
% 5.70/1.13  % (26840)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.70/1.13  % (26840)Termination reason: Refutation
% 5.70/1.13  
% 5.70/1.13  % (26840)Memory used [KB]: 12409
% 5.70/1.13  % (26840)Time elapsed: 0.702 s
% 5.70/1.13  % (26840)------------------------------
% 5.70/1.13  % (26840)------------------------------
% 5.70/1.13  % (26823)Success in time 0.767 s
%------------------------------------------------------------------------------
