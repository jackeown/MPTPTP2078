%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:52 EST 2020

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 114 expanded)
%              Number of leaves         :   18 (  53 expanded)
%              Depth                    :    7
%              Number of atoms          :  165 ( 409 expanded)
%              Number of equality atoms :   54 ( 157 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f181,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f33,f38,f43,f48,f52,f60,f69,f99,f103,f121,f174])).

fof(f174,plain,
    ( spl4_5
    | ~ spl4_13
    | ~ spl4_16 ),
    inference(avatar_contradiction_clause,[],[f173])).

fof(f173,plain,
    ( $false
    | spl4_5
    | ~ spl4_13
    | ~ spl4_16 ),
    inference(subsumption_resolution,[],[f47,f165])).

fof(f165,plain,
    ( k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | ~ spl4_13
    | ~ spl4_16 ),
    inference(superposition,[],[f98,f120])).

fof(f120,plain,
    ( sK2 = k3_xboole_0(sK3,sK2)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl4_16
  <=> sK2 = k3_xboole_0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f98,plain,
    ( ! [X0] : k7_relat_1(sK1,k3_xboole_0(sK3,X0)) = k7_relat_1(sK0,k3_xboole_0(sK3,X0))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl4_13
  <=> ! [X0] : k7_relat_1(sK1,k3_xboole_0(sK3,X0)) = k7_relat_1(sK0,k3_xboole_0(sK3,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f47,plain,
    ( k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl4_5
  <=> k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f121,plain,
    ( spl4_16
    | ~ spl4_3
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f104,f101,f35,f118])).

fof(f35,plain,
    ( spl4_3
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f101,plain,
    ( spl4_14
  <=> ! [X3,X2] :
        ( k3_xboole_0(X3,X2) = X2
        | ~ r1_tarski(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f104,plain,
    ( sK2 = k3_xboole_0(sK3,sK2)
    | ~ spl4_3
    | ~ spl4_14 ),
    inference(unit_resulting_resolution,[],[f37,f102])).

fof(f102,plain,
    ( ! [X2,X3] :
        ( k3_xboole_0(X3,X2) = X2
        | ~ r1_tarski(X2,X3) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f101])).

fof(f37,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f103,plain,
    ( spl4_14
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f62,f58,f50,f101])).

fof(f50,plain,
    ( spl4_6
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f58,plain,
    ( spl4_8
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f62,plain,
    ( ! [X2,X3] :
        ( k3_xboole_0(X3,X2) = X2
        | ~ r1_tarski(X2,X3) )
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(superposition,[],[f59,f51])).

fof(f51,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f50])).

fof(f59,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f58])).

fof(f99,plain,
    ( ~ spl4_2
    | spl4_13
    | ~ spl4_1
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f74,f67,f40,f25,f97,f30])).

fof(f30,plain,
    ( spl4_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f25,plain,
    ( spl4_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f40,plain,
    ( spl4_4
  <=> k7_relat_1(sK0,sK3) = k7_relat_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f67,plain,
    ( spl4_9
  <=> ! [X1,X0,X2] :
        ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f74,plain,
    ( ! [X0] :
        ( k7_relat_1(sK1,k3_xboole_0(sK3,X0)) = k7_relat_1(sK0,k3_xboole_0(sK3,X0))
        | ~ v1_relat_1(sK1) )
    | ~ spl4_1
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f72,f70])).

fof(f70,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK0,X0),X1) = k7_relat_1(sK0,k3_xboole_0(X0,X1))
    | ~ spl4_1
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f27,f68])).

fof(f68,plain,
    ( ! [X2,X0,X1] :
        ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
        | ~ v1_relat_1(X2) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f67])).

fof(f27,plain,
    ( v1_relat_1(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f72,plain,
    ( ! [X0] :
        ( k7_relat_1(sK1,k3_xboole_0(sK3,X0)) = k7_relat_1(k7_relat_1(sK0,sK3),X0)
        | ~ v1_relat_1(sK1) )
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(superposition,[],[f68,f42])).

fof(f42,plain,
    ( k7_relat_1(sK0,sK3) = k7_relat_1(sK1,sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f40])).

fof(f69,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f23,f67])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(f60,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f22,f58])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f52,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f20,f50])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f48,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f19,f45])).

fof(f19,plain,(
    k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)
    & k7_relat_1(sK0,sK3) = k7_relat_1(sK1,sK3)
    & r1_tarski(sK2,sK3)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f13,f12,f11])).

fof(f11,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2,X3] :
                ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
                & k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
                & r1_tarski(X2,X3) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X3,X2] :
              ( k7_relat_1(X1,X2) != k7_relat_1(sK0,X2)
              & k7_relat_1(X1,X3) = k7_relat_1(sK0,X3)
              & r1_tarski(X2,X3) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X1] :
        ( ? [X3,X2] :
            ( k7_relat_1(X1,X2) != k7_relat_1(sK0,X2)
            & k7_relat_1(X1,X3) = k7_relat_1(sK0,X3)
            & r1_tarski(X2,X3) )
        & v1_relat_1(X1) )
   => ( ? [X3,X2] :
          ( k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2)
          & k7_relat_1(sK0,X3) = k7_relat_1(sK1,X3)
          & r1_tarski(X2,X3) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X3,X2] :
        ( k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2)
        & k7_relat_1(sK0,X3) = k7_relat_1(sK1,X3)
        & r1_tarski(X2,X3) )
   => ( k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)
      & k7_relat_1(sK0,sK3) = k7_relat_1(sK1,sK3)
      & r1_tarski(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
              & k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
              & r1_tarski(X2,X3) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
              & k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
              & r1_tarski(X2,X3) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2,X3] :
                ( ( k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
                  & r1_tarski(X2,X3) )
               => k7_relat_1(X0,X2) = k7_relat_1(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2,X3] :
              ( ( k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
                & r1_tarski(X2,X3) )
             => k7_relat_1(X0,X2) = k7_relat_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t188_relat_1)).

fof(f43,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f18,f40])).

fof(f18,plain,(
    k7_relat_1(sK0,sK3) = k7_relat_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f38,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f17,f35])).

fof(f17,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f33,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f16,f30])).

fof(f16,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f28,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f15,f25])).

fof(f15,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:06:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.38  ipcrm: permission denied for id (797114369)
% 0.15/0.38  ipcrm: permission denied for id (797212674)
% 0.15/0.38  ipcrm: permission denied for id (801472516)
% 0.15/0.38  ipcrm: permission denied for id (797310981)
% 0.15/0.38  ipcrm: permission denied for id (803766278)
% 0.15/0.38  ipcrm: permission denied for id (801538055)
% 0.15/0.38  ipcrm: permission denied for id (797409288)
% 0.15/0.39  ipcrm: permission denied for id (797474826)
% 0.15/0.39  ipcrm: permission denied for id (797540364)
% 0.15/0.39  ipcrm: permission denied for id (797573133)
% 0.15/0.39  ipcrm: permission denied for id (797605902)
% 0.15/0.40  ipcrm: permission denied for id (803897360)
% 0.15/0.40  ipcrm: permission denied for id (797704209)
% 0.15/0.40  ipcrm: permission denied for id (797736978)
% 0.15/0.40  ipcrm: permission denied for id (801767445)
% 0.15/0.40  ipcrm: permission denied for id (801800214)
% 0.15/0.40  ipcrm: permission denied for id (801832983)
% 0.15/0.41  ipcrm: permission denied for id (797933592)
% 0.15/0.41  ipcrm: permission denied for id (801865753)
% 0.15/0.41  ipcrm: permission denied for id (801898522)
% 0.15/0.41  ipcrm: permission denied for id (798064667)
% 0.15/0.41  ipcrm: permission denied for id (801931292)
% 0.15/0.41  ipcrm: permission denied for id (798162974)
% 0.15/0.41  ipcrm: permission denied for id (798195743)
% 0.15/0.42  ipcrm: permission denied for id (804028448)
% 0.15/0.42  ipcrm: permission denied for id (802029601)
% 0.15/0.42  ipcrm: permission denied for id (798294050)
% 0.15/0.42  ipcrm: permission denied for id (798359588)
% 0.15/0.42  ipcrm: permission denied for id (798392357)
% 0.15/0.42  ipcrm: permission denied for id (802095142)
% 0.15/0.43  ipcrm: permission denied for id (802127911)
% 0.15/0.43  ipcrm: permission denied for id (804093992)
% 0.15/0.43  ipcrm: permission denied for id (798523433)
% 0.15/0.43  ipcrm: permission denied for id (804126762)
% 0.22/0.43  ipcrm: permission denied for id (802226219)
% 0.22/0.43  ipcrm: permission denied for id (798621740)
% 0.22/0.43  ipcrm: permission denied for id (798654509)
% 0.22/0.43  ipcrm: permission denied for id (802258990)
% 0.22/0.44  ipcrm: permission denied for id (798720047)
% 0.22/0.44  ipcrm: permission denied for id (802291760)
% 0.22/0.44  ipcrm: permission denied for id (798785585)
% 0.22/0.44  ipcrm: permission denied for id (798818354)
% 0.22/0.44  ipcrm: permission denied for id (798851123)
% 0.22/0.44  ipcrm: permission denied for id (798883892)
% 0.22/0.44  ipcrm: permission denied for id (802324533)
% 0.22/0.44  ipcrm: permission denied for id (798949430)
% 0.22/0.45  ipcrm: permission denied for id (802357303)
% 0.22/0.45  ipcrm: permission denied for id (799014968)
% 0.22/0.45  ipcrm: permission denied for id (802390073)
% 0.22/0.45  ipcrm: permission denied for id (799080506)
% 0.22/0.45  ipcrm: permission denied for id (799113275)
% 0.22/0.45  ipcrm: permission denied for id (799146044)
% 0.22/0.45  ipcrm: permission denied for id (804159549)
% 0.22/0.45  ipcrm: permission denied for id (802455614)
% 0.22/0.46  ipcrm: permission denied for id (799244351)
% 0.22/0.46  ipcrm: permission denied for id (802488384)
% 0.22/0.46  ipcrm: permission denied for id (799309889)
% 0.22/0.46  ipcrm: permission denied for id (799342658)
% 0.22/0.46  ipcrm: permission denied for id (799375427)
% 0.22/0.46  ipcrm: permission denied for id (799408196)
% 0.22/0.46  ipcrm: permission denied for id (802521157)
% 0.22/0.47  ipcrm: permission denied for id (802553926)
% 0.22/0.47  ipcrm: permission denied for id (802586695)
% 0.22/0.47  ipcrm: permission denied for id (804192328)
% 0.22/0.47  ipcrm: permission denied for id (804225097)
% 0.22/0.47  ipcrm: permission denied for id (804290635)
% 0.22/0.47  ipcrm: permission denied for id (799670348)
% 0.22/0.47  ipcrm: permission denied for id (799703117)
% 0.22/0.48  ipcrm: permission denied for id (804323406)
% 0.22/0.48  ipcrm: permission denied for id (799768655)
% 0.22/0.48  ipcrm: permission denied for id (799801424)
% 0.22/0.48  ipcrm: permission denied for id (799834193)
% 0.22/0.48  ipcrm: permission denied for id (804356178)
% 0.22/0.48  ipcrm: permission denied for id (804421716)
% 0.22/0.49  ipcrm: permission denied for id (799998038)
% 0.22/0.49  ipcrm: permission denied for id (800063576)
% 0.22/0.49  ipcrm: permission denied for id (802947161)
% 0.22/0.49  ipcrm: permission denied for id (802979930)
% 0.22/0.49  ipcrm: permission denied for id (803012699)
% 0.22/0.49  ipcrm: permission denied for id (800227421)
% 0.22/0.50  ipcrm: permission denied for id (800260190)
% 0.22/0.50  ipcrm: permission denied for id (800292959)
% 0.22/0.50  ipcrm: permission denied for id (803143776)
% 0.22/0.50  ipcrm: permission denied for id (800358497)
% 0.22/0.50  ipcrm: permission denied for id (804552802)
% 0.22/0.50  ipcrm: permission denied for id (803176547)
% 0.22/0.50  ipcrm: permission denied for id (800456804)
% 0.22/0.50  ipcrm: permission denied for id (803209317)
% 0.22/0.51  ipcrm: permission denied for id (800555111)
% 0.22/0.51  ipcrm: permission denied for id (804618344)
% 0.22/0.51  ipcrm: permission denied for id (800620649)
% 0.22/0.51  ipcrm: permission denied for id (804651114)
% 0.22/0.51  ipcrm: permission denied for id (803340395)
% 0.22/0.51  ipcrm: permission denied for id (803373164)
% 0.22/0.51  ipcrm: permission denied for id (800751725)
% 0.22/0.52  ipcrm: permission denied for id (800784494)
% 0.22/0.52  ipcrm: permission denied for id (800850032)
% 0.22/0.52  ipcrm: permission denied for id (800882801)
% 0.22/0.52  ipcrm: permission denied for id (800915570)
% 0.22/0.52  ipcrm: permission denied for id (803438707)
% 0.22/0.52  ipcrm: permission denied for id (801046645)
% 0.22/0.53  ipcrm: permission denied for id (801079414)
% 0.22/0.53  ipcrm: permission denied for id (801144952)
% 0.22/0.53  ipcrm: permission denied for id (804782201)
% 0.22/0.53  ipcrm: permission denied for id (804814970)
% 0.22/0.53  ipcrm: permission denied for id (803602555)
% 0.22/0.53  ipcrm: permission denied for id (803635324)
% 0.22/0.53  ipcrm: permission denied for id (801308797)
% 0.22/0.54  ipcrm: permission denied for id (804847742)
% 0.22/0.54  ipcrm: permission denied for id (801374335)
% 0.74/0.63  % (18410)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.74/0.63  % (18410)Refutation found. Thanks to Tanya!
% 0.74/0.63  % SZS status Theorem for theBenchmark
% 0.74/0.63  % SZS output start Proof for theBenchmark
% 0.74/0.63  fof(f181,plain,(
% 0.74/0.63    $false),
% 0.74/0.63    inference(avatar_sat_refutation,[],[f28,f33,f38,f43,f48,f52,f60,f69,f99,f103,f121,f174])).
% 0.74/0.63  fof(f174,plain,(
% 0.74/0.63    spl4_5 | ~spl4_13 | ~spl4_16),
% 0.74/0.63    inference(avatar_contradiction_clause,[],[f173])).
% 0.74/0.63  fof(f173,plain,(
% 0.74/0.63    $false | (spl4_5 | ~spl4_13 | ~spl4_16)),
% 0.74/0.63    inference(subsumption_resolution,[],[f47,f165])).
% 0.74/0.63  fof(f165,plain,(
% 0.74/0.63    k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) | (~spl4_13 | ~spl4_16)),
% 0.74/0.63    inference(superposition,[],[f98,f120])).
% 0.74/0.63  fof(f120,plain,(
% 0.74/0.63    sK2 = k3_xboole_0(sK3,sK2) | ~spl4_16),
% 0.74/0.63    inference(avatar_component_clause,[],[f118])).
% 0.74/0.63  fof(f118,plain,(
% 0.74/0.63    spl4_16 <=> sK2 = k3_xboole_0(sK3,sK2)),
% 0.74/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.74/0.63  fof(f98,plain,(
% 0.74/0.63    ( ! [X0] : (k7_relat_1(sK1,k3_xboole_0(sK3,X0)) = k7_relat_1(sK0,k3_xboole_0(sK3,X0))) ) | ~spl4_13),
% 0.74/0.63    inference(avatar_component_clause,[],[f97])).
% 0.74/0.63  fof(f97,plain,(
% 0.74/0.63    spl4_13 <=> ! [X0] : k7_relat_1(sK1,k3_xboole_0(sK3,X0)) = k7_relat_1(sK0,k3_xboole_0(sK3,X0))),
% 0.74/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.74/0.63  fof(f47,plain,(
% 0.74/0.63    k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) | spl4_5),
% 0.74/0.63    inference(avatar_component_clause,[],[f45])).
% 0.74/0.63  fof(f45,plain,(
% 0.74/0.63    spl4_5 <=> k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)),
% 0.74/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.74/0.63  fof(f121,plain,(
% 0.74/0.63    spl4_16 | ~spl4_3 | ~spl4_14),
% 0.74/0.63    inference(avatar_split_clause,[],[f104,f101,f35,f118])).
% 0.74/0.63  fof(f35,plain,(
% 0.74/0.63    spl4_3 <=> r1_tarski(sK2,sK3)),
% 0.74/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.74/0.63  fof(f101,plain,(
% 0.74/0.63    spl4_14 <=> ! [X3,X2] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3))),
% 0.74/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.74/0.63  fof(f104,plain,(
% 0.74/0.63    sK2 = k3_xboole_0(sK3,sK2) | (~spl4_3 | ~spl4_14)),
% 0.74/0.63    inference(unit_resulting_resolution,[],[f37,f102])).
% 0.74/0.63  fof(f102,plain,(
% 0.74/0.63    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3)) ) | ~spl4_14),
% 0.74/0.63    inference(avatar_component_clause,[],[f101])).
% 0.74/0.63  fof(f37,plain,(
% 0.74/0.63    r1_tarski(sK2,sK3) | ~spl4_3),
% 0.74/0.63    inference(avatar_component_clause,[],[f35])).
% 0.74/0.63  fof(f103,plain,(
% 0.74/0.63    spl4_14 | ~spl4_6 | ~spl4_8),
% 0.74/0.63    inference(avatar_split_clause,[],[f62,f58,f50,f101])).
% 0.74/0.63  fof(f50,plain,(
% 0.74/0.63    spl4_6 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.74/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.74/0.63  fof(f58,plain,(
% 0.74/0.63    spl4_8 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.74/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.74/0.63  fof(f62,plain,(
% 0.74/0.63    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3)) ) | (~spl4_6 | ~spl4_8)),
% 0.74/0.63    inference(superposition,[],[f59,f51])).
% 0.74/0.63  fof(f51,plain,(
% 0.74/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl4_6),
% 0.74/0.63    inference(avatar_component_clause,[],[f50])).
% 0.74/0.63  fof(f59,plain,(
% 0.74/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) ) | ~spl4_8),
% 0.74/0.63    inference(avatar_component_clause,[],[f58])).
% 0.74/0.63  fof(f99,plain,(
% 0.74/0.63    ~spl4_2 | spl4_13 | ~spl4_1 | ~spl4_4 | ~spl4_9),
% 0.74/0.63    inference(avatar_split_clause,[],[f74,f67,f40,f25,f97,f30])).
% 0.74/0.63  fof(f30,plain,(
% 0.74/0.63    spl4_2 <=> v1_relat_1(sK1)),
% 0.74/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.74/0.63  fof(f25,plain,(
% 0.74/0.63    spl4_1 <=> v1_relat_1(sK0)),
% 0.74/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.74/0.63  fof(f40,plain,(
% 0.74/0.63    spl4_4 <=> k7_relat_1(sK0,sK3) = k7_relat_1(sK1,sK3)),
% 0.74/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.74/0.63  fof(f67,plain,(
% 0.74/0.63    spl4_9 <=> ! [X1,X0,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.74/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.74/0.63  fof(f74,plain,(
% 0.74/0.63    ( ! [X0] : (k7_relat_1(sK1,k3_xboole_0(sK3,X0)) = k7_relat_1(sK0,k3_xboole_0(sK3,X0)) | ~v1_relat_1(sK1)) ) | (~spl4_1 | ~spl4_4 | ~spl4_9)),
% 0.74/0.63    inference(forward_demodulation,[],[f72,f70])).
% 0.74/0.63  fof(f70,plain,(
% 0.74/0.63    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK0,X0),X1) = k7_relat_1(sK0,k3_xboole_0(X0,X1))) ) | (~spl4_1 | ~spl4_9)),
% 0.74/0.63    inference(unit_resulting_resolution,[],[f27,f68])).
% 0.74/0.63  fof(f68,plain,(
% 0.74/0.63    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) ) | ~spl4_9),
% 0.74/0.63    inference(avatar_component_clause,[],[f67])).
% 0.74/0.63  fof(f27,plain,(
% 0.74/0.63    v1_relat_1(sK0) | ~spl4_1),
% 0.74/0.63    inference(avatar_component_clause,[],[f25])).
% 0.74/0.63  fof(f72,plain,(
% 0.74/0.63    ( ! [X0] : (k7_relat_1(sK1,k3_xboole_0(sK3,X0)) = k7_relat_1(k7_relat_1(sK0,sK3),X0) | ~v1_relat_1(sK1)) ) | (~spl4_4 | ~spl4_9)),
% 0.74/0.63    inference(superposition,[],[f68,f42])).
% 0.74/0.63  fof(f42,plain,(
% 0.74/0.63    k7_relat_1(sK0,sK3) = k7_relat_1(sK1,sK3) | ~spl4_4),
% 0.74/0.63    inference(avatar_component_clause,[],[f40])).
% 0.74/0.63  fof(f69,plain,(
% 0.74/0.63    spl4_9),
% 0.74/0.63    inference(avatar_split_clause,[],[f23,f67])).
% 0.74/0.63  fof(f23,plain,(
% 0.74/0.63    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 0.74/0.63    inference(cnf_transformation,[],[f10])).
% 0.74/0.63  fof(f10,plain,(
% 0.74/0.63    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.74/0.63    inference(ennf_transformation,[],[f4])).
% 0.74/0.63  fof(f4,axiom,(
% 0.74/0.63    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.74/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).
% 0.74/0.63  fof(f60,plain,(
% 0.74/0.63    spl4_8),
% 0.74/0.63    inference(avatar_split_clause,[],[f22,f58])).
% 0.74/0.63  fof(f22,plain,(
% 0.74/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.74/0.63    inference(cnf_transformation,[],[f9])).
% 0.74/0.63  fof(f9,plain,(
% 0.74/0.63    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.74/0.63    inference(ennf_transformation,[],[f2])).
% 0.74/0.63  fof(f2,axiom,(
% 0.74/0.63    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.74/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.74/0.63  fof(f52,plain,(
% 0.74/0.63    spl4_6),
% 0.74/0.63    inference(avatar_split_clause,[],[f20,f50])).
% 0.74/0.63  fof(f20,plain,(
% 0.74/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.74/0.63    inference(cnf_transformation,[],[f1])).
% 0.74/0.63  fof(f1,axiom,(
% 0.74/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.74/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.74/0.64  fof(f48,plain,(
% 0.74/0.64    ~spl4_5),
% 0.74/0.64    inference(avatar_split_clause,[],[f19,f45])).
% 0.74/0.64  fof(f19,plain,(
% 0.74/0.64    k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)),
% 0.74/0.64    inference(cnf_transformation,[],[f14])).
% 0.74/0.64  fof(f14,plain,(
% 0.74/0.64    ((k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) & k7_relat_1(sK0,sK3) = k7_relat_1(sK1,sK3) & r1_tarski(sK2,sK3)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.74/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f13,f12,f11])).
% 0.74/0.64  fof(f11,plain,(
% 0.74/0.64    ? [X0] : (? [X1] : (? [X2,X3] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & k7_relat_1(X0,X3) = k7_relat_1(X1,X3) & r1_tarski(X2,X3)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (? [X3,X2] : (k7_relat_1(X1,X2) != k7_relat_1(sK0,X2) & k7_relat_1(X1,X3) = k7_relat_1(sK0,X3) & r1_tarski(X2,X3)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.74/0.64    introduced(choice_axiom,[])).
% 0.74/0.64  fof(f12,plain,(
% 0.74/0.64    ? [X1] : (? [X3,X2] : (k7_relat_1(X1,X2) != k7_relat_1(sK0,X2) & k7_relat_1(X1,X3) = k7_relat_1(sK0,X3) & r1_tarski(X2,X3)) & v1_relat_1(X1)) => (? [X3,X2] : (k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2) & k7_relat_1(sK0,X3) = k7_relat_1(sK1,X3) & r1_tarski(X2,X3)) & v1_relat_1(sK1))),
% 0.74/0.64    introduced(choice_axiom,[])).
% 0.74/0.64  fof(f13,plain,(
% 0.74/0.64    ? [X3,X2] : (k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2) & k7_relat_1(sK0,X3) = k7_relat_1(sK1,X3) & r1_tarski(X2,X3)) => (k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) & k7_relat_1(sK0,sK3) = k7_relat_1(sK1,sK3) & r1_tarski(sK2,sK3))),
% 0.74/0.64    introduced(choice_axiom,[])).
% 0.74/0.64  fof(f8,plain,(
% 0.74/0.64    ? [X0] : (? [X1] : (? [X2,X3] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & k7_relat_1(X0,X3) = k7_relat_1(X1,X3) & r1_tarski(X2,X3)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.74/0.64    inference(flattening,[],[f7])).
% 0.74/0.64  fof(f7,plain,(
% 0.74/0.64    ? [X0] : (? [X1] : (? [X2,X3] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & (k7_relat_1(X0,X3) = k7_relat_1(X1,X3) & r1_tarski(X2,X3))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.74/0.64    inference(ennf_transformation,[],[f6])).
% 0.74/0.64  fof(f6,negated_conjecture,(
% 0.74/0.64    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2,X3] : ((k7_relat_1(X0,X3) = k7_relat_1(X1,X3) & r1_tarski(X2,X3)) => k7_relat_1(X0,X2) = k7_relat_1(X1,X2))))),
% 0.74/0.64    inference(negated_conjecture,[],[f5])).
% 0.74/0.64  fof(f5,conjecture,(
% 0.74/0.64    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2,X3] : ((k7_relat_1(X0,X3) = k7_relat_1(X1,X3) & r1_tarski(X2,X3)) => k7_relat_1(X0,X2) = k7_relat_1(X1,X2))))),
% 0.74/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t188_relat_1)).
% 0.74/0.64  fof(f43,plain,(
% 0.74/0.64    spl4_4),
% 0.74/0.64    inference(avatar_split_clause,[],[f18,f40])).
% 0.74/0.64  fof(f18,plain,(
% 0.74/0.64    k7_relat_1(sK0,sK3) = k7_relat_1(sK1,sK3)),
% 0.74/0.64    inference(cnf_transformation,[],[f14])).
% 0.74/0.64  fof(f38,plain,(
% 0.74/0.64    spl4_3),
% 0.74/0.64    inference(avatar_split_clause,[],[f17,f35])).
% 0.74/0.64  fof(f17,plain,(
% 0.74/0.64    r1_tarski(sK2,sK3)),
% 0.74/0.64    inference(cnf_transformation,[],[f14])).
% 0.74/0.64  fof(f33,plain,(
% 0.74/0.64    spl4_2),
% 0.74/0.64    inference(avatar_split_clause,[],[f16,f30])).
% 0.74/0.64  fof(f16,plain,(
% 0.74/0.64    v1_relat_1(sK1)),
% 0.74/0.64    inference(cnf_transformation,[],[f14])).
% 0.74/0.64  fof(f28,plain,(
% 0.74/0.64    spl4_1),
% 0.74/0.64    inference(avatar_split_clause,[],[f15,f25])).
% 0.74/0.64  fof(f15,plain,(
% 0.74/0.64    v1_relat_1(sK0)),
% 0.74/0.64    inference(cnf_transformation,[],[f14])).
% 0.74/0.64  % SZS output end Proof for theBenchmark
% 0.74/0.64  % (18410)------------------------------
% 0.74/0.64  % (18410)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.74/0.64  % (18410)Termination reason: Refutation
% 0.74/0.64  
% 0.74/0.64  % (18410)Memory used [KB]: 6268
% 0.74/0.64  % (18410)Time elapsed: 0.056 s
% 0.74/0.64  % (18410)------------------------------
% 0.74/0.64  % (18410)------------------------------
% 0.74/0.64  % (18208)Success in time 0.269 s
%------------------------------------------------------------------------------
