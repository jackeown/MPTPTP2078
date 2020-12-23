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
% DateTime   : Thu Dec  3 12:51:25 EST 2020

% Result     : Theorem 1.79s
% Output     : Refutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 225 expanded)
%              Number of leaves         :   12 (  67 expanded)
%              Depth                    :   25
%              Number of atoms          :  257 ( 938 expanded)
%              Number of equality atoms :   72 ( 223 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1036,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f57,f86,f1033])).

fof(f1033,plain,
    ( ~ spl3_2
    | spl3_3 ),
    inference(avatar_contradiction_clause,[],[f1028])).

fof(f1028,plain,
    ( $false
    | ~ spl3_2
    | spl3_3 ),
    inference(unit_resulting_resolution,[],[f85,f1025])).

fof(f1025,plain,
    ( ! [X0] : k6_subset_1(k1_relat_1(sK1),X0) = k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X0)))
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f990,f67])).

fof(f67,plain,
    ( ! [X1] : k6_subset_1(k1_relat_1(sK1),X1) = k5_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X1)))
    | ~ spl3_2 ),
    inference(superposition,[],[f36,f59])).

fof(f59,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f56,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f28,f25])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f56,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl3_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f36,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f26,f24,f25])).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f990,plain,
    ( ! [X0] : k5_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X0))) = k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X0)))
    | ~ spl3_2 ),
    inference(superposition,[],[f67,f984])).

fof(f984,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_relat_1(k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0))))
    | ~ spl3_2 ),
    inference(duplicate_literal_removal,[],[f956])).

fof(f956,plain,
    ( ! [X0] :
        ( k1_relat_1(k7_relat_1(sK1,X0)) = k1_relat_1(k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0))))
        | k1_relat_1(k7_relat_1(sK1,X0)) = k1_relat_1(k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0)))) )
    | ~ spl3_2 ),
    inference(resolution,[],[f758,f302])).

fof(f302,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2(k1_relat_1(sK1),X0,k1_relat_1(k7_relat_1(sK1,X1))),k1_relat_1(sK1))
        | k1_relat_1(k7_relat_1(sK1,X1)) = k1_relat_1(k7_relat_1(sK1,X0)) )
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f296,f59])).

fof(f296,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2(k1_relat_1(sK1),X0,k1_relat_1(k7_relat_1(sK1,X1))),k1_relat_1(sK1))
        | k1_relat_1(k7_relat_1(sK1,X1)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0)) )
    | ~ spl3_2 ),
    inference(factoring,[],[f102])).

fof(f102,plain,
    ( ! [X4,X5,X3] :
        ( r2_hidden(sK2(X3,X4,k1_relat_1(k7_relat_1(sK1,X5))),k1_relat_1(sK1))
        | r2_hidden(sK2(X3,X4,k1_relat_1(k7_relat_1(sK1,X5))),X3)
        | k1_relat_1(k7_relat_1(sK1,X5)) = k1_setfam_1(k2_tarski(X3,X4)) )
    | ~ spl3_2 ),
    inference(resolution,[],[f73,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f33,f25])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f19])).

fof(f19,plain,(
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

fof(f18,plain,(
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
    inference(rectify,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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

fof(f73,plain,
    ( ! [X12,X13] :
        ( ~ r2_hidden(X13,k1_relat_1(k7_relat_1(sK1,X12)))
        | r2_hidden(X13,k1_relat_1(sK1)) )
    | ~ spl3_2 ),
    inference(superposition,[],[f47,f59])).

fof(f47,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f30,f25])).

fof(f30,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f758,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2(k1_relat_1(sK1),X0,X0),k1_relat_1(sK1))
        | k1_relat_1(k7_relat_1(sK1,X0)) = X0 )
    | ~ spl3_2 ),
    inference(duplicate_literal_removal,[],[f757])).

fof(f757,plain,
    ( ! [X0] :
        ( k1_relat_1(k7_relat_1(sK1,X0)) = X0
        | k1_relat_1(k7_relat_1(sK1,X0)) = X0
        | ~ r2_hidden(sK2(k1_relat_1(sK1),X0,X0),k1_relat_1(sK1)) )
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f756,f59])).

fof(f756,plain,
    ( ! [X0] :
        ( k1_relat_1(k7_relat_1(sK1,X0)) = X0
        | k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0)) = X0
        | ~ r2_hidden(sK2(k1_relat_1(sK1),X0,X0),k1_relat_1(sK1)) )
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f731,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f34,f25])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f731,plain,
    ( ! [X0] :
        ( k1_relat_1(k7_relat_1(sK1,X0)) = X0
        | k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0)) = X0
        | ~ r2_hidden(sK2(k1_relat_1(sK1),X0,X0),k1_relat_1(sK1))
        | ~ r2_hidden(sK2(k1_relat_1(sK1),X0,X0),X0) )
    | ~ spl3_2 ),
    inference(resolution,[],[f674,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f35,f25])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f674,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(k1_relat_1(sK1),X0,X0),X0)
        | k1_relat_1(k7_relat_1(sK1,X0)) = X0 )
    | ~ spl3_2 ),
    inference(factoring,[],[f624])).

fof(f624,plain,
    ( ! [X4,X3] :
        ( r2_hidden(sK2(k1_relat_1(sK1),X3,X4),X4)
        | r2_hidden(sK2(k1_relat_1(sK1),X3,X4),X3)
        | k1_relat_1(k7_relat_1(sK1,X3)) = X4 )
    | ~ spl3_2 ),
    inference(resolution,[],[f415,f72])).

fof(f72,plain,
    ( ! [X10,X11] :
        ( ~ r2_hidden(X11,k1_relat_1(k7_relat_1(sK1,X10)))
        | r2_hidden(X11,X10) )
    | ~ spl3_2 ),
    inference(superposition,[],[f46,f59])).

fof(f46,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f31,f25])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f415,plain,
    ( ! [X6,X7] :
        ( r2_hidden(sK2(k1_relat_1(sK1),X6,X7),k1_relat_1(k7_relat_1(sK1,X6)))
        | r2_hidden(sK2(k1_relat_1(sK1),X6,X7),X7)
        | k1_relat_1(k7_relat_1(sK1,X6)) = X7 )
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f410,f59])).

fof(f410,plain,
    ( ! [X6,X7] :
        ( r2_hidden(sK2(k1_relat_1(sK1),X6,X7),k1_relat_1(k7_relat_1(sK1,X6)))
        | k1_setfam_1(k2_tarski(k1_relat_1(sK1),X6)) = X7
        | r2_hidden(sK2(k1_relat_1(sK1),X6,X7),X7) )
    | ~ spl3_2 ),
    inference(duplicate_literal_removal,[],[f370])).

fof(f370,plain,
    ( ! [X6,X7] :
        ( r2_hidden(sK2(k1_relat_1(sK1),X6,X7),k1_relat_1(k7_relat_1(sK1,X6)))
        | k1_setfam_1(k2_tarski(k1_relat_1(sK1),X6)) = X7
        | r2_hidden(sK2(k1_relat_1(sK1),X6,X7),X7)
        | k1_setfam_1(k2_tarski(k1_relat_1(sK1),X6)) = X7
        | r2_hidden(sK2(k1_relat_1(sK1),X6,X7),X7) )
    | ~ spl3_2 ),
    inference(resolution,[],[f107,f41])).

fof(f107,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK2(X0,X1,X2),k1_relat_1(sK1))
        | r2_hidden(sK2(X0,X1,X2),k1_relat_1(k7_relat_1(sK1,X1)))
        | k1_setfam_1(k2_tarski(X0,X1)) = X2
        | r2_hidden(sK2(X0,X1,X2),X2) )
    | ~ spl3_2 ),
    inference(resolution,[],[f71,f40])).

fof(f71,plain,
    ( ! [X8,X9] :
        ( ~ r2_hidden(X9,X8)
        | r2_hidden(X9,k1_relat_1(k7_relat_1(sK1,X8)))
        | ~ r2_hidden(X9,k1_relat_1(sK1)) )
    | ~ spl3_2 ),
    inference(superposition,[],[f45,f59])).

fof(f45,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f32,f25])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f85,plain,
    ( k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),sK0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl3_3
  <=> k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) = k6_subset_1(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f86,plain,
    ( ~ spl3_3
    | spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f80,f54,f49,f83])).

fof(f49,plain,
    ( spl3_1
  <=> k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) = k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f80,plain,
    ( k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),sK0)
    | spl3_1
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f51,f58])).

fof(f58,plain,
    ( ! [X0] : k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,X0))) = k6_subset_1(k1_relat_1(sK1),X0)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f56,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t212_relat_1)).

fof(f51,plain,
    ( k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0)))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f57,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f21,f54])).

fof(f21,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0)))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) != k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0)))
        & v1_relat_1(X1) )
   => ( k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) != k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0)))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t213_relat_1)).

fof(f52,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f22,f49])).

fof(f22,plain,(
    k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:28:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (30972)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.50  % (30961)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (30961)Refutation not found, incomplete strategy% (30961)------------------------------
% 0.21/0.50  % (30961)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (30961)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (30961)Memory used [KB]: 6140
% 0.21/0.50  % (30961)Time elapsed: 0.108 s
% 0.21/0.50  % (30961)------------------------------
% 0.21/0.50  % (30961)------------------------------
% 0.21/0.50  % (30963)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (30974)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.51  % (30984)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.51  % (30957)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (30966)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (30960)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (30980)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (30967)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (30981)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (30973)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (30980)Refutation not found, incomplete strategy% (30980)------------------------------
% 0.21/0.53  % (30980)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (30980)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (30980)Memory used [KB]: 10618
% 0.21/0.53  % (30980)Time elapsed: 0.128 s
% 0.21/0.53  % (30980)------------------------------
% 0.21/0.53  % (30980)------------------------------
% 0.21/0.53  % (30969)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (30959)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (30971)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (30973)Refutation not found, incomplete strategy% (30973)------------------------------
% 0.21/0.53  % (30973)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (30973)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (30973)Memory used [KB]: 6140
% 0.21/0.53  % (30973)Time elapsed: 0.003 s
% 0.21/0.53  % (30973)------------------------------
% 0.21/0.53  % (30973)------------------------------
% 0.21/0.53  % (30986)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (30983)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (30958)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (30975)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (30965)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (30985)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (30987)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (30975)Refutation not found, incomplete strategy% (30975)------------------------------
% 0.21/0.54  % (30975)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (30962)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (30975)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (30975)Memory used [KB]: 10618
% 0.21/0.54  % (30975)Time elapsed: 0.105 s
% 0.21/0.54  % (30975)------------------------------
% 0.21/0.54  % (30975)------------------------------
% 0.21/0.54  % (30968)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (30978)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (30968)Refutation not found, incomplete strategy% (30968)------------------------------
% 0.21/0.54  % (30968)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (30968)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (30968)Memory used [KB]: 10618
% 0.21/0.54  % (30968)Time elapsed: 0.148 s
% 0.21/0.54  % (30968)------------------------------
% 0.21/0.54  % (30968)------------------------------
% 0.21/0.54  % (30977)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (30978)Refutation not found, incomplete strategy% (30978)------------------------------
% 0.21/0.55  % (30978)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (30978)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (30978)Memory used [KB]: 10746
% 0.21/0.55  % (30978)Time elapsed: 0.149 s
% 0.21/0.55  % (30978)------------------------------
% 0.21/0.55  % (30978)------------------------------
% 0.21/0.55  % (30976)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (30988)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (30970)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (30979)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (30979)Refutation not found, incomplete strategy% (30979)------------------------------
% 0.21/0.55  % (30979)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (30979)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (30979)Memory used [KB]: 1663
% 0.21/0.55  % (30979)Time elapsed: 0.150 s
% 0.21/0.55  % (30979)------------------------------
% 0.21/0.55  % (30979)------------------------------
% 0.21/0.55  % (30969)Refutation not found, incomplete strategy% (30969)------------------------------
% 0.21/0.55  % (30969)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (30969)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (30969)Memory used [KB]: 10618
% 0.21/0.56  % (30969)Time elapsed: 0.150 s
% 0.21/0.56  % (30969)------------------------------
% 0.21/0.56  % (30969)------------------------------
% 1.79/0.59  % (30984)Refutation found. Thanks to Tanya!
% 1.79/0.59  % SZS status Theorem for theBenchmark
% 1.79/0.59  % SZS output start Proof for theBenchmark
% 1.79/0.59  fof(f1036,plain,(
% 1.79/0.59    $false),
% 1.79/0.59    inference(avatar_sat_refutation,[],[f52,f57,f86,f1033])).
% 1.79/0.59  fof(f1033,plain,(
% 1.79/0.59    ~spl3_2 | spl3_3),
% 1.79/0.59    inference(avatar_contradiction_clause,[],[f1028])).
% 1.79/0.59  fof(f1028,plain,(
% 1.79/0.59    $false | (~spl3_2 | spl3_3)),
% 1.79/0.59    inference(unit_resulting_resolution,[],[f85,f1025])).
% 1.79/0.59  fof(f1025,plain,(
% 1.79/0.59    ( ! [X0] : (k6_subset_1(k1_relat_1(sK1),X0) = k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X0)))) ) | ~spl3_2),
% 1.79/0.59    inference(forward_demodulation,[],[f990,f67])).
% 1.79/0.59  fof(f67,plain,(
% 1.79/0.59    ( ! [X1] : (k6_subset_1(k1_relat_1(sK1),X1) = k5_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X1)))) ) | ~spl3_2),
% 1.79/0.59    inference(superposition,[],[f36,f59])).
% 1.79/0.59  fof(f59,plain,(
% 1.79/0.59    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0))) ) | ~spl3_2),
% 1.79/0.59    inference(unit_resulting_resolution,[],[f56,f38])).
% 1.79/0.59  fof(f38,plain,(
% 1.79/0.59    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 1.79/0.59    inference(definition_unfolding,[],[f28,f25])).
% 1.79/0.59  fof(f25,plain,(
% 1.79/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.79/0.59    inference(cnf_transformation,[],[f6])).
% 1.79/0.59  fof(f6,axiom,(
% 1.79/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.79/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.79/0.59  fof(f28,plain,(
% 1.79/0.59    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.79/0.59    inference(cnf_transformation,[],[f12])).
% 1.79/0.59  fof(f12,plain,(
% 1.79/0.59    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.79/0.59    inference(ennf_transformation,[],[f8])).
% 1.79/0.59  fof(f8,axiom,(
% 1.79/0.59    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 1.79/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 1.79/0.59  fof(f56,plain,(
% 1.79/0.59    v1_relat_1(sK1) | ~spl3_2),
% 1.79/0.59    inference(avatar_component_clause,[],[f54])).
% 1.79/0.59  fof(f54,plain,(
% 1.79/0.59    spl3_2 <=> v1_relat_1(sK1)),
% 1.79/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.79/0.59  fof(f36,plain,(
% 1.79/0.59    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.79/0.59    inference(definition_unfolding,[],[f26,f24,f25])).
% 1.79/0.59  fof(f24,plain,(
% 1.79/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.79/0.59    inference(cnf_transformation,[],[f5])).
% 1.79/0.59  fof(f5,axiom,(
% 1.79/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.79/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.79/0.59  fof(f26,plain,(
% 1.79/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.79/0.59    inference(cnf_transformation,[],[f2])).
% 1.79/0.59  fof(f2,axiom,(
% 1.79/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.79/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.79/0.59  fof(f990,plain,(
% 1.79/0.59    ( ! [X0] : (k5_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X0))) = k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X0)))) ) | ~spl3_2),
% 1.79/0.59    inference(superposition,[],[f67,f984])).
% 1.79/0.59  fof(f984,plain,(
% 1.79/0.59    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_relat_1(k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0))))) ) | ~spl3_2),
% 1.79/0.59    inference(duplicate_literal_removal,[],[f956])).
% 1.79/0.59  fof(f956,plain,(
% 1.79/0.59    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_relat_1(k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0)))) | k1_relat_1(k7_relat_1(sK1,X0)) = k1_relat_1(k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0))))) ) | ~spl3_2),
% 1.79/0.59    inference(resolution,[],[f758,f302])).
% 1.79/0.59  fof(f302,plain,(
% 1.79/0.59    ( ! [X0,X1] : (r2_hidden(sK2(k1_relat_1(sK1),X0,k1_relat_1(k7_relat_1(sK1,X1))),k1_relat_1(sK1)) | k1_relat_1(k7_relat_1(sK1,X1)) = k1_relat_1(k7_relat_1(sK1,X0))) ) | ~spl3_2),
% 1.79/0.59    inference(forward_demodulation,[],[f296,f59])).
% 1.79/0.59  fof(f296,plain,(
% 1.79/0.59    ( ! [X0,X1] : (r2_hidden(sK2(k1_relat_1(sK1),X0,k1_relat_1(k7_relat_1(sK1,X1))),k1_relat_1(sK1)) | k1_relat_1(k7_relat_1(sK1,X1)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0))) ) | ~spl3_2),
% 1.79/0.59    inference(factoring,[],[f102])).
% 1.79/0.59  fof(f102,plain,(
% 1.79/0.59    ( ! [X4,X5,X3] : (r2_hidden(sK2(X3,X4,k1_relat_1(k7_relat_1(sK1,X5))),k1_relat_1(sK1)) | r2_hidden(sK2(X3,X4,k1_relat_1(k7_relat_1(sK1,X5))),X3) | k1_relat_1(k7_relat_1(sK1,X5)) = k1_setfam_1(k2_tarski(X3,X4))) ) | ~spl3_2),
% 1.79/0.59    inference(resolution,[],[f73,f41])).
% 1.79/0.59  fof(f41,plain,(
% 1.79/0.59    ( ! [X2,X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.79/0.59    inference(definition_unfolding,[],[f33,f25])).
% 1.79/0.59  fof(f33,plain,(
% 1.79/0.59    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.79/0.59    inference(cnf_transformation,[],[f20])).
% 1.79/0.59  fof(f20,plain,(
% 1.79/0.59    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.79/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f19])).
% 1.79/0.59  fof(f19,plain,(
% 1.79/0.59    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 1.79/0.59    introduced(choice_axiom,[])).
% 1.79/0.59  fof(f18,plain,(
% 1.79/0.59    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.79/0.59    inference(rectify,[],[f17])).
% 1.79/0.59  fof(f17,plain,(
% 1.79/0.59    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.79/0.59    inference(flattening,[],[f16])).
% 1.79/0.59  fof(f16,plain,(
% 1.79/0.59    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.79/0.59    inference(nnf_transformation,[],[f1])).
% 1.79/0.59  fof(f1,axiom,(
% 1.79/0.59    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.79/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.79/0.59  fof(f73,plain,(
% 1.79/0.59    ( ! [X12,X13] : (~r2_hidden(X13,k1_relat_1(k7_relat_1(sK1,X12))) | r2_hidden(X13,k1_relat_1(sK1))) ) | ~spl3_2),
% 1.79/0.59    inference(superposition,[],[f47,f59])).
% 1.79/0.59  fof(f47,plain,(
% 1.79/0.59    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.79/0.59    inference(equality_resolution,[],[f44])).
% 1.79/0.59  fof(f44,plain,(
% 1.79/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 1.79/0.59    inference(definition_unfolding,[],[f30,f25])).
% 1.79/0.59  fof(f30,plain,(
% 1.79/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.79/0.59    inference(cnf_transformation,[],[f20])).
% 1.79/0.59  fof(f758,plain,(
% 1.79/0.59    ( ! [X0] : (~r2_hidden(sK2(k1_relat_1(sK1),X0,X0),k1_relat_1(sK1)) | k1_relat_1(k7_relat_1(sK1,X0)) = X0) ) | ~spl3_2),
% 1.79/0.59    inference(duplicate_literal_removal,[],[f757])).
% 1.79/0.59  fof(f757,plain,(
% 1.79/0.59    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = X0 | k1_relat_1(k7_relat_1(sK1,X0)) = X0 | ~r2_hidden(sK2(k1_relat_1(sK1),X0,X0),k1_relat_1(sK1))) ) | ~spl3_2),
% 1.79/0.59    inference(forward_demodulation,[],[f756,f59])).
% 1.79/0.59  fof(f756,plain,(
% 1.79/0.59    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = X0 | k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0)) = X0 | ~r2_hidden(sK2(k1_relat_1(sK1),X0,X0),k1_relat_1(sK1))) ) | ~spl3_2),
% 1.79/0.59    inference(subsumption_resolution,[],[f731,f40])).
% 1.79/0.59  fof(f40,plain,(
% 1.79/0.59    ( ! [X2,X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.79/0.59    inference(definition_unfolding,[],[f34,f25])).
% 1.79/0.59  fof(f34,plain,(
% 1.79/0.59    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.79/0.59    inference(cnf_transformation,[],[f20])).
% 1.79/0.59  fof(f731,plain,(
% 1.79/0.59    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = X0 | k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0)) = X0 | ~r2_hidden(sK2(k1_relat_1(sK1),X0,X0),k1_relat_1(sK1)) | ~r2_hidden(sK2(k1_relat_1(sK1),X0,X0),X0)) ) | ~spl3_2),
% 1.79/0.59    inference(resolution,[],[f674,f39])).
% 1.79/0.59  fof(f39,plain,(
% 1.79/0.59    ( ! [X2,X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.79/0.59    inference(definition_unfolding,[],[f35,f25])).
% 1.79/0.59  fof(f35,plain,(
% 1.79/0.59    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.79/0.59    inference(cnf_transformation,[],[f20])).
% 1.79/0.59  fof(f674,plain,(
% 1.79/0.59    ( ! [X0] : (r2_hidden(sK2(k1_relat_1(sK1),X0,X0),X0) | k1_relat_1(k7_relat_1(sK1,X0)) = X0) ) | ~spl3_2),
% 1.79/0.59    inference(factoring,[],[f624])).
% 1.79/0.59  fof(f624,plain,(
% 1.79/0.59    ( ! [X4,X3] : (r2_hidden(sK2(k1_relat_1(sK1),X3,X4),X4) | r2_hidden(sK2(k1_relat_1(sK1),X3,X4),X3) | k1_relat_1(k7_relat_1(sK1,X3)) = X4) ) | ~spl3_2),
% 1.79/0.59    inference(resolution,[],[f415,f72])).
% 1.79/0.59  fof(f72,plain,(
% 1.79/0.59    ( ! [X10,X11] : (~r2_hidden(X11,k1_relat_1(k7_relat_1(sK1,X10))) | r2_hidden(X11,X10)) ) | ~spl3_2),
% 1.79/0.59    inference(superposition,[],[f46,f59])).
% 1.79/0.59  fof(f46,plain,(
% 1.79/0.59    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.79/0.59    inference(equality_resolution,[],[f43])).
% 1.79/0.59  fof(f43,plain,(
% 1.79/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 1.79/0.59    inference(definition_unfolding,[],[f31,f25])).
% 1.79/0.59  fof(f31,plain,(
% 1.79/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.79/0.59    inference(cnf_transformation,[],[f20])).
% 1.79/0.59  fof(f415,plain,(
% 1.79/0.59    ( ! [X6,X7] : (r2_hidden(sK2(k1_relat_1(sK1),X6,X7),k1_relat_1(k7_relat_1(sK1,X6))) | r2_hidden(sK2(k1_relat_1(sK1),X6,X7),X7) | k1_relat_1(k7_relat_1(sK1,X6)) = X7) ) | ~spl3_2),
% 1.79/0.59    inference(forward_demodulation,[],[f410,f59])).
% 1.79/0.59  fof(f410,plain,(
% 1.79/0.59    ( ! [X6,X7] : (r2_hidden(sK2(k1_relat_1(sK1),X6,X7),k1_relat_1(k7_relat_1(sK1,X6))) | k1_setfam_1(k2_tarski(k1_relat_1(sK1),X6)) = X7 | r2_hidden(sK2(k1_relat_1(sK1),X6,X7),X7)) ) | ~spl3_2),
% 1.79/0.59    inference(duplicate_literal_removal,[],[f370])).
% 1.79/0.59  fof(f370,plain,(
% 1.79/0.59    ( ! [X6,X7] : (r2_hidden(sK2(k1_relat_1(sK1),X6,X7),k1_relat_1(k7_relat_1(sK1,X6))) | k1_setfam_1(k2_tarski(k1_relat_1(sK1),X6)) = X7 | r2_hidden(sK2(k1_relat_1(sK1),X6,X7),X7) | k1_setfam_1(k2_tarski(k1_relat_1(sK1),X6)) = X7 | r2_hidden(sK2(k1_relat_1(sK1),X6,X7),X7)) ) | ~spl3_2),
% 1.79/0.59    inference(resolution,[],[f107,f41])).
% 1.79/0.59  fof(f107,plain,(
% 1.79/0.59    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),k1_relat_1(sK1)) | r2_hidden(sK2(X0,X1,X2),k1_relat_1(k7_relat_1(sK1,X1))) | k1_setfam_1(k2_tarski(X0,X1)) = X2 | r2_hidden(sK2(X0,X1,X2),X2)) ) | ~spl3_2),
% 1.79/0.59    inference(resolution,[],[f71,f40])).
% 1.79/0.59  fof(f71,plain,(
% 1.79/0.59    ( ! [X8,X9] : (~r2_hidden(X9,X8) | r2_hidden(X9,k1_relat_1(k7_relat_1(sK1,X8))) | ~r2_hidden(X9,k1_relat_1(sK1))) ) | ~spl3_2),
% 1.79/0.59    inference(superposition,[],[f45,f59])).
% 1.79/0.59  fof(f45,plain,(
% 1.79/0.59    ( ! [X4,X0,X1] : (r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1))) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.79/0.59    inference(equality_resolution,[],[f42])).
% 1.79/0.59  fof(f42,plain,(
% 1.79/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 1.79/0.59    inference(definition_unfolding,[],[f32,f25])).
% 1.79/0.59  fof(f32,plain,(
% 1.79/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 1.79/0.59    inference(cnf_transformation,[],[f20])).
% 1.79/0.59  fof(f85,plain,(
% 1.79/0.59    k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),sK0) | spl3_3),
% 1.79/0.59    inference(avatar_component_clause,[],[f83])).
% 1.79/0.59  fof(f83,plain,(
% 1.79/0.59    spl3_3 <=> k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) = k6_subset_1(k1_relat_1(sK1),sK0)),
% 1.79/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.79/0.59  fof(f86,plain,(
% 1.79/0.59    ~spl3_3 | spl3_1 | ~spl3_2),
% 1.79/0.59    inference(avatar_split_clause,[],[f80,f54,f49,f83])).
% 1.79/0.59  fof(f49,plain,(
% 1.79/0.59    spl3_1 <=> k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) = k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0)))),
% 1.79/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.79/0.59  fof(f80,plain,(
% 1.79/0.59    k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),sK0) | (spl3_1 | ~spl3_2)),
% 1.79/0.59    inference(backward_demodulation,[],[f51,f58])).
% 1.79/0.59  fof(f58,plain,(
% 1.79/0.59    ( ! [X0] : (k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,X0))) = k6_subset_1(k1_relat_1(sK1),X0)) ) | ~spl3_2),
% 1.79/0.59    inference(unit_resulting_resolution,[],[f56,f29])).
% 1.79/0.59  fof(f29,plain,(
% 1.79/0.59    ( ! [X0,X1] : (k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.79/0.59    inference(cnf_transformation,[],[f13])).
% 1.79/0.59  fof(f13,plain,(
% 1.79/0.59    ! [X0,X1] : (k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.79/0.59    inference(ennf_transformation,[],[f7])).
% 1.79/0.59  fof(f7,axiom,(
% 1.79/0.59    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0))),
% 1.79/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t212_relat_1)).
% 1.79/0.59  fof(f51,plain,(
% 1.79/0.59    k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) | spl3_1),
% 1.79/0.59    inference(avatar_component_clause,[],[f49])).
% 1.79/0.59  fof(f57,plain,(
% 1.79/0.59    spl3_2),
% 1.79/0.59    inference(avatar_split_clause,[],[f21,f54])).
% 1.79/0.59  fof(f21,plain,(
% 1.79/0.59    v1_relat_1(sK1)),
% 1.79/0.59    inference(cnf_transformation,[],[f15])).
% 1.79/0.59  fof(f15,plain,(
% 1.79/0.59    k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) & v1_relat_1(sK1)),
% 1.79/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f14])).
% 1.79/0.59  fof(f14,plain,(
% 1.79/0.59    ? [X0,X1] : (k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) != k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) & v1_relat_1(X1)) => (k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) & v1_relat_1(sK1))),
% 1.79/0.59    introduced(choice_axiom,[])).
% 1.79/0.59  fof(f11,plain,(
% 1.79/0.59    ? [X0,X1] : (k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) != k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) & v1_relat_1(X1))),
% 1.79/0.59    inference(ennf_transformation,[],[f10])).
% 1.79/0.59  fof(f10,negated_conjecture,(
% 1.79/0.59    ~! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))))),
% 1.79/0.59    inference(negated_conjecture,[],[f9])).
% 1.79/0.59  fof(f9,conjecture,(
% 1.79/0.59    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))))),
% 1.79/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t213_relat_1)).
% 1.79/0.59  fof(f52,plain,(
% 1.79/0.59    ~spl3_1),
% 1.79/0.59    inference(avatar_split_clause,[],[f22,f49])).
% 1.79/0.59  fof(f22,plain,(
% 1.79/0.59    k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0)))),
% 1.79/0.59    inference(cnf_transformation,[],[f15])).
% 1.79/0.59  % SZS output end Proof for theBenchmark
% 1.79/0.59  % (30984)------------------------------
% 1.79/0.59  % (30984)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.79/0.59  % (30984)Termination reason: Refutation
% 1.79/0.59  
% 1.79/0.59  % (30984)Memory used [KB]: 6908
% 1.79/0.59  % (30984)Time elapsed: 0.179 s
% 1.79/0.59  % (30984)------------------------------
% 1.79/0.59  % (30984)------------------------------
% 1.79/0.59  % (30953)Success in time 0.227 s
%------------------------------------------------------------------------------
