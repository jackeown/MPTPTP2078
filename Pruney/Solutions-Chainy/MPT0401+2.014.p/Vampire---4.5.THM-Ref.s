%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:15 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 177 expanded)
%              Number of leaves         :   21 (  68 expanded)
%              Depth                    :   10
%              Number of atoms          :  131 ( 279 expanded)
%              Number of equality atoms :   28 ( 108 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f163,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f55,f60,f66,f76,f83,f109,f157])).

fof(f157,plain,
    ( spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f156,f105,f80])).

fof(f80,plain,
    ( spl3_6
  <=> r1_tarski(sK2,k3_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f105,plain,
    ( spl3_7
  <=> sK1 = k3_tarski(k3_enumset1(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f156,plain,
    ( r1_tarski(sK2,k3_tarski(sK1))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f149,f42])).

fof(f42,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f27,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f29,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f30,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f34,f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f34,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f27,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f149,plain,
    ( r1_tarski(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k3_tarski(sK1))
    | ~ spl3_7 ),
    inference(superposition,[],[f96,f107])).

fof(f107,plain,
    ( sK1 = k3_tarski(k3_enumset1(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK1))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f105])).

fof(f96,plain,(
    ! [X2,X1] : r1_tarski(k3_tarski(X1),k3_tarski(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))) ),
    inference(superposition,[],[f43,f44])).

fof(f44,plain,(
    ! [X0,X1] : k3_tarski(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = k3_tarski(k3_enumset1(k3_tarski(X0),k3_tarski(X0),k3_tarski(X0),k3_tarski(X0),k3_tarski(X1))) ),
    inference(definition_unfolding,[],[f31,f39,f39])).

fof(f31,plain,(
    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_zfmisc_1)).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f28,f39])).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f109,plain,
    ( spl3_7
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f103,f52,f105])).

fof(f52,plain,
    ( spl3_2
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f103,plain,
    ( sK1 = k3_tarski(k3_enumset1(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK1))
    | ~ spl3_2 ),
    inference(resolution,[],[f45,f54])).

fof(f54,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k3_tarski(k3_enumset1(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0),X1)) = X1 ) ),
    inference(definition_unfolding,[],[f33,f39,f40])).

fof(f40,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f26,f38])).

fof(f26,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(f83,plain,
    ( ~ spl3_6
    | spl3_1
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f77,f73,f47,f80])).

fof(f47,plain,
    ( spl3_1
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f73,plain,
    ( spl3_5
  <=> r1_tarski(k3_tarski(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f77,plain,
    ( ~ r1_tarski(sK2,k3_tarski(sK1))
    | spl3_1
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f49,f75,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f75,plain,
    ( r1_tarski(k3_tarski(sK1),sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f73])).

fof(f49,plain,
    ( ~ r1_tarski(sK2,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f76,plain,
    ( spl3_5
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f69,f63,f73])).

fof(f63,plain,
    ( spl3_4
  <=> r1_tarski(k3_tarski(sK1),k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f69,plain,
    ( r1_tarski(k3_tarski(sK1),sK0)
    | ~ spl3_4 ),
    inference(backward_demodulation,[],[f65,f42])).

fof(f65,plain,
    ( r1_tarski(k3_tarski(sK1),k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f63])).

fof(f66,plain,
    ( spl3_4
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f61,f57,f63])).

fof(f57,plain,
    ( spl3_3
  <=> r1_setfam_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f61,plain,
    ( r1_tarski(k3_tarski(sK1),k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f59,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_setfam_1)).

fof(f59,plain,
    ( r1_setfam_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f60,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f41,f57])).

fof(f41,plain,(
    r1_setfam_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(definition_unfolding,[],[f23,f40])).

fof(f23,plain,(
    r1_setfam_1(sK1,k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ r1_tarski(sK2,sK0)
    & r2_hidden(sK2,sK1)
    & r1_setfam_1(sK1,k1_tarski(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f21,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X2,X0)
            & r2_hidden(X2,X1) )
        & r1_setfam_1(X1,k1_tarski(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(X2,sK0)
          & r2_hidden(X2,sK1) )
      & r1_setfam_1(sK1,k1_tarski(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X2] :
        ( ~ r1_tarski(X2,sK0)
        & r2_hidden(X2,sK1) )
   => ( ~ r1_tarski(sK2,sK0)
      & r2_hidden(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X0)
          & r2_hidden(X2,X1) )
      & r1_setfam_1(X1,k1_tarski(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_setfam_1(X1,k1_tarski(X0))
       => ! [X2] :
            ( r2_hidden(X2,X1)
           => r1_tarski(X2,X0) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( r1_setfam_1(X1,k1_tarski(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_setfam_1)).

fof(f55,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f24,f52])).

fof(f24,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f50,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f25,f47])).

fof(f25,plain,(
    ~ r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:17:50 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.37  ipcrm: permission denied for id (1206255617)
% 0.22/0.38  ipcrm: permission denied for id (1206452231)
% 0.22/0.38  ipcrm: permission denied for id (1206517769)
% 0.22/0.38  ipcrm: permission denied for id (1206550538)
% 0.22/0.38  ipcrm: permission denied for id (1206583307)
% 0.22/0.39  ipcrm: permission denied for id (1206616076)
% 0.22/0.39  ipcrm: permission denied for id (1206747152)
% 0.22/0.39  ipcrm: permission denied for id (1206779921)
% 0.22/0.39  ipcrm: permission denied for id (1206812690)
% 0.22/0.40  ipcrm: permission denied for id (1206878228)
% 0.22/0.40  ipcrm: permission denied for id (1206943766)
% 0.22/0.40  ipcrm: permission denied for id (1207009304)
% 0.22/0.40  ipcrm: permission denied for id (1207042073)
% 0.22/0.40  ipcrm: permission denied for id (1207074842)
% 0.22/0.41  ipcrm: permission denied for id (1207238687)
% 0.22/0.41  ipcrm: permission denied for id (1207271456)
% 0.22/0.42  ipcrm: permission denied for id (1207631915)
% 0.22/0.43  ipcrm: permission denied for id (1207697453)
% 0.22/0.43  ipcrm: permission denied for id (1207762991)
% 0.22/0.43  ipcrm: permission denied for id (1207795760)
% 0.22/0.43  ipcrm: permission denied for id (1207828529)
% 0.22/0.43  ipcrm: permission denied for id (1207861298)
% 0.22/0.43  ipcrm: permission denied for id (1207894067)
% 0.22/0.43  ipcrm: permission denied for id (1207926836)
% 0.22/0.44  ipcrm: permission denied for id (1207992374)
% 0.22/0.44  ipcrm: permission denied for id (1208057912)
% 0.22/0.44  ipcrm: permission denied for id (1208090681)
% 0.22/0.44  ipcrm: permission denied for id (1208188988)
% 0.22/0.45  ipcrm: permission denied for id (1208254526)
% 0.22/0.45  ipcrm: permission denied for id (1208418371)
% 0.22/0.46  ipcrm: permission denied for id (1208483909)
% 0.22/0.46  ipcrm: permission denied for id (1208647754)
% 0.22/0.46  ipcrm: permission denied for id (1208713292)
% 0.22/0.47  ipcrm: permission denied for id (1208746061)
% 0.22/0.47  ipcrm: permission denied for id (1208909906)
% 0.22/0.47  ipcrm: permission denied for id (1208942675)
% 0.22/0.48  ipcrm: permission denied for id (1209139288)
% 0.22/0.48  ipcrm: permission denied for id (1209204826)
% 0.22/0.48  ipcrm: permission denied for id (1209237595)
% 0.22/0.49  ipcrm: permission denied for id (1209401440)
% 0.22/0.49  ipcrm: permission denied for id (1209434209)
% 0.22/0.49  ipcrm: permission denied for id (1209499747)
% 0.22/0.49  ipcrm: permission denied for id (1209532516)
% 0.22/0.50  ipcrm: permission denied for id (1209598054)
% 0.22/0.50  ipcrm: permission denied for id (1209630823)
% 0.22/0.50  ipcrm: permission denied for id (1209696362)
% 0.22/0.50  ipcrm: permission denied for id (1209794669)
% 0.22/0.51  ipcrm: permission denied for id (1209892976)
% 0.22/0.51  ipcrm: permission denied for id (1209958515)
% 0.22/0.51  ipcrm: permission denied for id (1210024053)
% 0.22/0.52  ipcrm: permission denied for id (1210089591)
% 0.22/0.52  ipcrm: permission denied for id (1210220667)
% 0.22/0.52  ipcrm: permission denied for id (1210253436)
% 0.22/0.52  ipcrm: permission denied for id (1210286205)
% 0.22/0.53  ipcrm: permission denied for id (1210351743)
% 0.38/0.59  % (29266)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.38/0.61  % (29264)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.38/0.63  % (29258)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.38/0.64  % (29273)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.38/0.64  % (29256)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.38/0.65  % (29269)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.38/0.65  % (29262)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.38/0.65  % (29262)Refutation found. Thanks to Tanya!
% 0.38/0.65  % SZS status Theorem for theBenchmark
% 0.38/0.65  % SZS output start Proof for theBenchmark
% 0.38/0.65  fof(f163,plain,(
% 0.38/0.65    $false),
% 0.38/0.65    inference(avatar_sat_refutation,[],[f50,f55,f60,f66,f76,f83,f109,f157])).
% 0.38/0.65  fof(f157,plain,(
% 0.38/0.65    spl3_6 | ~spl3_7),
% 0.38/0.65    inference(avatar_split_clause,[],[f156,f105,f80])).
% 0.38/0.65  fof(f80,plain,(
% 0.38/0.65    spl3_6 <=> r1_tarski(sK2,k3_tarski(sK1))),
% 0.38/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.38/0.65  fof(f105,plain,(
% 0.38/0.65    spl3_7 <=> sK1 = k3_tarski(k3_enumset1(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK1))),
% 0.38/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.38/0.65  fof(f156,plain,(
% 0.38/0.65    r1_tarski(sK2,k3_tarski(sK1)) | ~spl3_7),
% 0.38/0.65    inference(forward_demodulation,[],[f149,f42])).
% 0.38/0.65  fof(f42,plain,(
% 0.38/0.65    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X0)) = X0) )),
% 0.38/0.65    inference(definition_unfolding,[],[f27,f39])).
% 0.38/0.65  fof(f39,plain,(
% 0.38/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.38/0.65    inference(definition_unfolding,[],[f29,f38])).
% 0.38/0.65  fof(f38,plain,(
% 0.38/0.65    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.38/0.65    inference(definition_unfolding,[],[f30,f37])).
% 0.38/0.65  fof(f37,plain,(
% 0.38/0.65    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.38/0.65    inference(definition_unfolding,[],[f34,f36])).
% 0.38/0.65  fof(f36,plain,(
% 0.38/0.65    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.38/0.65    inference(cnf_transformation,[],[f7])).
% 0.38/0.65  fof(f7,axiom,(
% 0.38/0.65    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.38/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.38/0.65  fof(f34,plain,(
% 0.38/0.65    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.38/0.65    inference(cnf_transformation,[],[f6])).
% 0.38/0.65  fof(f6,axiom,(
% 0.38/0.65    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.38/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.38/0.65  fof(f30,plain,(
% 0.38/0.65    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.38/0.65    inference(cnf_transformation,[],[f5])).
% 0.38/0.65  fof(f5,axiom,(
% 0.38/0.65    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.38/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.38/0.65  fof(f29,plain,(
% 0.38/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.38/0.65    inference(cnf_transformation,[],[f9])).
% 0.38/0.65  fof(f9,axiom,(
% 0.38/0.65    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.38/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.38/0.65  fof(f27,plain,(
% 0.38/0.65    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.38/0.65    inference(cnf_transformation,[],[f14])).
% 0.38/0.65  fof(f14,plain,(
% 0.38/0.65    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.38/0.65    inference(rectify,[],[f1])).
% 0.38/0.65  fof(f1,axiom,(
% 0.38/0.65    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.38/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.38/0.65  fof(f149,plain,(
% 0.38/0.65    r1_tarski(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k3_tarski(sK1)) | ~spl3_7),
% 0.38/0.65    inference(superposition,[],[f96,f107])).
% 0.38/0.65  fof(f107,plain,(
% 0.38/0.65    sK1 = k3_tarski(k3_enumset1(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK1)) | ~spl3_7),
% 0.38/0.65    inference(avatar_component_clause,[],[f105])).
% 0.38/0.65  fof(f96,plain,(
% 0.38/0.65    ( ! [X2,X1] : (r1_tarski(k3_tarski(X1),k3_tarski(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))))) )),
% 0.38/0.65    inference(superposition,[],[f43,f44])).
% 0.38/0.65  fof(f44,plain,(
% 0.38/0.65    ( ! [X0,X1] : (k3_tarski(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = k3_tarski(k3_enumset1(k3_tarski(X0),k3_tarski(X0),k3_tarski(X0),k3_tarski(X0),k3_tarski(X1)))) )),
% 0.38/0.65    inference(definition_unfolding,[],[f31,f39,f39])).
% 0.38/0.65  fof(f31,plain,(
% 0.38/0.65    ( ! [X0,X1] : (k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1))) )),
% 0.38/0.65    inference(cnf_transformation,[],[f10])).
% 0.38/0.65  fof(f10,axiom,(
% 0.38/0.65    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1))),
% 0.38/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_zfmisc_1)).
% 0.38/0.65  fof(f43,plain,(
% 0.38/0.65    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 0.38/0.65    inference(definition_unfolding,[],[f28,f39])).
% 0.38/0.65  fof(f28,plain,(
% 0.38/0.65    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.38/0.65    inference(cnf_transformation,[],[f3])).
% 0.38/0.65  fof(f3,axiom,(
% 0.38/0.65    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.38/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.38/0.65  fof(f109,plain,(
% 0.38/0.65    spl3_7 | ~spl3_2),
% 0.38/0.65    inference(avatar_split_clause,[],[f103,f52,f105])).
% 0.38/0.65  fof(f52,plain,(
% 0.38/0.65    spl3_2 <=> r2_hidden(sK2,sK1)),
% 0.38/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.38/0.65  fof(f103,plain,(
% 0.38/0.65    sK1 = k3_tarski(k3_enumset1(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK1)) | ~spl3_2),
% 0.38/0.65    inference(resolution,[],[f45,f54])).
% 0.38/0.65  fof(f54,plain,(
% 0.38/0.65    r2_hidden(sK2,sK1) | ~spl3_2),
% 0.38/0.65    inference(avatar_component_clause,[],[f52])).
% 0.38/0.65  fof(f45,plain,(
% 0.38/0.65    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k3_tarski(k3_enumset1(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0),X1)) = X1) )),
% 0.38/0.65    inference(definition_unfolding,[],[f33,f39,f40])).
% 0.38/0.65  fof(f40,plain,(
% 0.38/0.65    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.38/0.65    inference(definition_unfolding,[],[f26,f38])).
% 0.38/0.65  fof(f26,plain,(
% 0.38/0.65    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.38/0.65    inference(cnf_transformation,[],[f4])).
% 0.38/0.65  fof(f4,axiom,(
% 0.38/0.65    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.38/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.38/0.65  fof(f33,plain,(
% 0.38/0.65    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 0.38/0.65    inference(cnf_transformation,[],[f17])).
% 0.38/0.65  fof(f17,plain,(
% 0.38/0.65    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 0.38/0.65    inference(ennf_transformation,[],[f8])).
% 0.38/0.65  fof(f8,axiom,(
% 0.38/0.65    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.38/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).
% 0.38/0.65  fof(f83,plain,(
% 0.38/0.65    ~spl3_6 | spl3_1 | ~spl3_5),
% 0.38/0.65    inference(avatar_split_clause,[],[f77,f73,f47,f80])).
% 0.38/0.65  fof(f47,plain,(
% 0.38/0.65    spl3_1 <=> r1_tarski(sK2,sK0)),
% 0.38/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.38/0.65  fof(f73,plain,(
% 0.38/0.65    spl3_5 <=> r1_tarski(k3_tarski(sK1),sK0)),
% 0.38/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.38/0.65  fof(f77,plain,(
% 0.38/0.65    ~r1_tarski(sK2,k3_tarski(sK1)) | (spl3_1 | ~spl3_5)),
% 0.38/0.65    inference(unit_resulting_resolution,[],[f49,f75,f35])).
% 0.38/0.65  fof(f35,plain,(
% 0.38/0.65    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 0.38/0.65    inference(cnf_transformation,[],[f19])).
% 0.38/0.65  fof(f19,plain,(
% 0.38/0.65    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.38/0.65    inference(flattening,[],[f18])).
% 0.38/0.65  fof(f18,plain,(
% 0.38/0.65    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.38/0.65    inference(ennf_transformation,[],[f2])).
% 0.38/0.65  fof(f2,axiom,(
% 0.38/0.65    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.38/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.38/0.65  fof(f75,plain,(
% 0.38/0.65    r1_tarski(k3_tarski(sK1),sK0) | ~spl3_5),
% 0.38/0.65    inference(avatar_component_clause,[],[f73])).
% 0.38/0.65  fof(f49,plain,(
% 0.38/0.65    ~r1_tarski(sK2,sK0) | spl3_1),
% 0.38/0.65    inference(avatar_component_clause,[],[f47])).
% 0.38/0.65  fof(f76,plain,(
% 0.38/0.65    spl3_5 | ~spl3_4),
% 0.38/0.65    inference(avatar_split_clause,[],[f69,f63,f73])).
% 0.38/0.65  fof(f63,plain,(
% 0.38/0.65    spl3_4 <=> r1_tarski(k3_tarski(sK1),k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 0.38/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.38/0.65  fof(f69,plain,(
% 0.38/0.65    r1_tarski(k3_tarski(sK1),sK0) | ~spl3_4),
% 0.38/0.65    inference(backward_demodulation,[],[f65,f42])).
% 0.38/0.65  fof(f65,plain,(
% 0.38/0.65    r1_tarski(k3_tarski(sK1),k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | ~spl3_4),
% 0.38/0.65    inference(avatar_component_clause,[],[f63])).
% 0.38/0.65  fof(f66,plain,(
% 0.38/0.65    spl3_4 | ~spl3_3),
% 0.38/0.65    inference(avatar_split_clause,[],[f61,f57,f63])).
% 0.38/0.65  fof(f57,plain,(
% 0.38/0.65    spl3_3 <=> r1_setfam_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 0.38/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.38/0.65  fof(f61,plain,(
% 0.38/0.65    r1_tarski(k3_tarski(sK1),k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | ~spl3_3),
% 0.38/0.65    inference(unit_resulting_resolution,[],[f59,f32])).
% 0.38/0.65  fof(f32,plain,(
% 0.38/0.65    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_setfam_1(X0,X1)) )),
% 0.38/0.65    inference(cnf_transformation,[],[f16])).
% 0.38/0.65  fof(f16,plain,(
% 0.38/0.65    ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_setfam_1(X0,X1))),
% 0.38/0.65    inference(ennf_transformation,[],[f11])).
% 0.38/0.65  fof(f11,axiom,(
% 0.38/0.65    ! [X0,X1] : (r1_setfam_1(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 0.38/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_setfam_1)).
% 0.38/0.65  fof(f59,plain,(
% 0.38/0.65    r1_setfam_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~spl3_3),
% 0.38/0.65    inference(avatar_component_clause,[],[f57])).
% 0.38/0.65  fof(f60,plain,(
% 0.38/0.65    spl3_3),
% 0.38/0.65    inference(avatar_split_clause,[],[f41,f57])).
% 0.38/0.65  fof(f41,plain,(
% 0.38/0.65    r1_setfam_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 0.38/0.65    inference(definition_unfolding,[],[f23,f40])).
% 0.38/0.65  fof(f23,plain,(
% 0.38/0.65    r1_setfam_1(sK1,k1_tarski(sK0))),
% 0.38/0.65    inference(cnf_transformation,[],[f22])).
% 0.38/0.65  fof(f22,plain,(
% 0.38/0.65    (~r1_tarski(sK2,sK0) & r2_hidden(sK2,sK1)) & r1_setfam_1(sK1,k1_tarski(sK0))),
% 0.38/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f21,f20])).
% 0.38/0.65  fof(f20,plain,(
% 0.38/0.65    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,X0) & r2_hidden(X2,X1)) & r1_setfam_1(X1,k1_tarski(X0))) => (? [X2] : (~r1_tarski(X2,sK0) & r2_hidden(X2,sK1)) & r1_setfam_1(sK1,k1_tarski(sK0)))),
% 0.38/0.65    introduced(choice_axiom,[])).
% 0.38/0.65  fof(f21,plain,(
% 0.38/0.65    ? [X2] : (~r1_tarski(X2,sK0) & r2_hidden(X2,sK1)) => (~r1_tarski(sK2,sK0) & r2_hidden(sK2,sK1))),
% 0.38/0.65    introduced(choice_axiom,[])).
% 0.38/0.65  fof(f15,plain,(
% 0.38/0.65    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,X0) & r2_hidden(X2,X1)) & r1_setfam_1(X1,k1_tarski(X0)))),
% 0.38/0.65    inference(ennf_transformation,[],[f13])).
% 0.38/0.65  fof(f13,negated_conjecture,(
% 0.38/0.65    ~! [X0,X1] : (r1_setfam_1(X1,k1_tarski(X0)) => ! [X2] : (r2_hidden(X2,X1) => r1_tarski(X2,X0)))),
% 0.38/0.65    inference(negated_conjecture,[],[f12])).
% 0.38/0.65  fof(f12,conjecture,(
% 0.38/0.65    ! [X0,X1] : (r1_setfam_1(X1,k1_tarski(X0)) => ! [X2] : (r2_hidden(X2,X1) => r1_tarski(X2,X0)))),
% 0.38/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_setfam_1)).
% 0.38/0.65  fof(f55,plain,(
% 0.38/0.65    spl3_2),
% 0.38/0.65    inference(avatar_split_clause,[],[f24,f52])).
% 0.38/0.65  fof(f24,plain,(
% 0.38/0.65    r2_hidden(sK2,sK1)),
% 0.38/0.65    inference(cnf_transformation,[],[f22])).
% 0.38/0.65  fof(f50,plain,(
% 0.38/0.65    ~spl3_1),
% 0.38/0.65    inference(avatar_split_clause,[],[f25,f47])).
% 0.38/0.65  fof(f25,plain,(
% 0.38/0.65    ~r1_tarski(sK2,sK0)),
% 0.38/0.65    inference(cnf_transformation,[],[f22])).
% 0.38/0.65  % SZS output end Proof for theBenchmark
% 0.38/0.65  % (29262)------------------------------
% 0.38/0.65  % (29262)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.38/0.65  % (29262)Termination reason: Refutation
% 0.38/0.65  
% 0.38/0.65  % (29262)Memory used [KB]: 6268
% 0.38/0.65  % (29262)Time elapsed: 0.067 s
% 0.38/0.65  % (29262)------------------------------
% 0.38/0.65  % (29262)------------------------------
% 0.38/0.65  % (29259)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.38/0.65  % (29260)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.38/0.66  % (29117)Success in time 0.291 s
%------------------------------------------------------------------------------
