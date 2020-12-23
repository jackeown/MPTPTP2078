%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:54 EST 2020

% Result     : Theorem 1.48s
% Output     : Refutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 363 expanded)
%              Number of leaves         :   40 ( 132 expanded)
%              Depth                    :   11
%              Number of atoms          :  370 ( 723 expanded)
%              Number of equality atoms :  120 ( 342 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f972,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f114,f117,f139,f142,f257,f324,f329,f332,f637,f690,f692,f702,f760,f943,f945,f971])).

fof(f971,plain,
    ( ~ spl1_19
    | spl1_1
    | ~ spl1_60 ),
    inference(avatar_split_clause,[],[f970,f813,f81,f229])).

fof(f229,plain,
    ( spl1_19
  <=> v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_19])])).

fof(f81,plain,
    ( spl1_1
  <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f813,plain,
    ( spl1_60
  <=> k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_60])])).

fof(f970,plain,
    ( k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_60 ),
    inference(forward_demodulation,[],[f969,f73])).

fof(f73,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f47,f72])).

fof(f72,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f59,f70])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f60,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f65,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f66,f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f65,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f60,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f59,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f969,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k1_xboole_0))
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_60 ),
    inference(forward_demodulation,[],[f964,f79])).

% (27404)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
fof(f79,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f964,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0)))))
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_60 ),
    inference(superposition,[],[f74,f815])).

fof(f815,plain,
    ( k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_60 ),
    inference(avatar_component_clause,[],[f813])).

fof(f74,plain,(
    ! [X0] :
      ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f51,f72])).

fof(f51,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

fof(f945,plain,(
    spl1_65 ),
    inference(avatar_contradiction_clause,[],[f944])).

fof(f944,plain,
    ( $false
    | spl1_65 ),
    inference(resolution,[],[f942,f46])).

fof(f46,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f942,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK0))
    | spl1_65 ),
    inference(avatar_component_clause,[],[f940])).

fof(f940,plain,
    ( spl1_65
  <=> r1_tarski(k1_xboole_0,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_65])])).

fof(f943,plain,
    ( ~ spl1_5
    | ~ spl1_3
    | ~ spl1_65
    | spl1_60 ),
    inference(avatar_split_clause,[],[f938,f813,f940,f105,f124])).

fof(f124,plain,
    ( spl1_5
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f105,plain,
    ( spl1_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f938,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | spl1_60 ),
    inference(forward_demodulation,[],[f937,f45])).

fof(f45,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f937,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | spl1_60 ),
    inference(trivial_inequality_removal,[],[f936])).

fof(f936,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | spl1_60 ),
    inference(forward_demodulation,[],[f935,f44])).

fof(f44,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f22])).

fof(f935,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | spl1_60 ),
    inference(superposition,[],[f814,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

fof(f814,plain,
    ( k1_xboole_0 != k1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | spl1_60 ),
    inference(avatar_component_clause,[],[f813])).

fof(f760,plain,
    ( spl1_2
    | ~ spl1_4
    | ~ spl1_32
    | ~ spl1_55 ),
    inference(avatar_contradiction_clause,[],[f759])).

fof(f759,plain,
    ( $false
    | spl1_2
    | ~ spl1_4
    | ~ spl1_32
    | ~ spl1_55 ),
    inference(trivial_inequality_removal,[],[f755])).

fof(f755,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl1_2
    | ~ spl1_4
    | ~ spl1_32
    | ~ spl1_55 ),
    inference(superposition,[],[f87,f727])).

fof(f727,plain,
    ( k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | ~ spl1_4
    | ~ spl1_32
    | ~ spl1_55 ),
    inference(forward_demodulation,[],[f707,f111])).

fof(f111,plain,
    ( k1_xboole_0 = k4_relat_1(k1_xboole_0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl1_4
  <=> k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f707,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k1_xboole_0)
    | ~ spl1_32
    | ~ spl1_55 ),
    inference(backward_demodulation,[],[f323,f701])).

fof(f701,plain,
    ( k1_xboole_0 = k5_relat_1(k1_xboole_0,k4_relat_1(sK0))
    | ~ spl1_55 ),
    inference(avatar_component_clause,[],[f699])).

fof(f699,plain,
    ( spl1_55
  <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_55])])).

fof(f323,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))
    | ~ spl1_32 ),
    inference(avatar_component_clause,[],[f321])).

fof(f321,plain,
    ( spl1_32
  <=> k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_32])])).

fof(f87,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | spl1_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl1_2
  <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f702,plain,
    ( ~ spl1_33
    | spl1_55
    | ~ spl1_51 ),
    inference(avatar_split_clause,[],[f697,f610,f699,f326])).

fof(f326,plain,
    ( spl1_33
  <=> v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_33])])).

fof(f610,plain,
    ( spl1_51
  <=> k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_51])])).

fof(f697,plain,
    ( k1_xboole_0 = k5_relat_1(k1_xboole_0,k4_relat_1(sK0))
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))
    | ~ spl1_51 ),
    inference(forward_demodulation,[],[f696,f73])).

fof(f696,plain,
    ( k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k1_xboole_0))
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))
    | ~ spl1_51 ),
    inference(forward_demodulation,[],[f695,f79])).

fof(f695,plain,
    ( k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))))))
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))
    | ~ spl1_51 ),
    inference(superposition,[],[f74,f612])).

fof(f612,plain,
    ( k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))
    | ~ spl1_51 ),
    inference(avatar_component_clause,[],[f610])).

fof(f692,plain,(
    spl1_54 ),
    inference(avatar_contradiction_clause,[],[f691])).

fof(f691,plain,
    ( $false
    | spl1_54 ),
    inference(resolution,[],[f689,f46])).

fof(f689,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(k4_relat_1(sK0)))
    | spl1_54 ),
    inference(avatar_component_clause,[],[f687])).

fof(f687,plain,
    ( spl1_54
  <=> r1_tarski(k1_xboole_0,k1_relat_1(k4_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_54])])).

fof(f690,plain,
    ( ~ spl1_5
    | ~ spl1_53
    | ~ spl1_54
    | spl1_51 ),
    inference(avatar_split_clause,[],[f685,f610,f687,f624,f124])).

fof(f624,plain,
    ( spl1_53
  <=> v1_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_53])])).

fof(f685,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(k4_relat_1(sK0)))
    | ~ v1_relat_1(k4_relat_1(sK0))
    | ~ v1_relat_1(k1_xboole_0)
    | spl1_51 ),
    inference(forward_demodulation,[],[f684,f45])).

fof(f684,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(k4_relat_1(sK0)))
    | ~ v1_relat_1(k4_relat_1(sK0))
    | ~ v1_relat_1(k1_xboole_0)
    | spl1_51 ),
    inference(trivial_inequality_removal,[],[f683])).

fof(f683,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(k4_relat_1(sK0)))
    | ~ v1_relat_1(k4_relat_1(sK0))
    | ~ v1_relat_1(k1_xboole_0)
    | spl1_51 ),
    inference(forward_demodulation,[],[f682,f44])).

fof(f682,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(k4_relat_1(sK0)))
    | ~ v1_relat_1(k4_relat_1(sK0))
    | ~ v1_relat_1(k1_xboole_0)
    | spl1_51 ),
    inference(superposition,[],[f611,f54])).

fof(f611,plain,
    ( k1_xboole_0 != k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))
    | spl1_51 ),
    inference(avatar_component_clause,[],[f610])).

fof(f637,plain,(
    spl1_53 ),
    inference(avatar_contradiction_clause,[],[f635])).

fof(f635,plain,
    ( $false
    | spl1_53 ),
    inference(resolution,[],[f633,f41])).

fof(f41,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f37])).

fof(f37,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(f633,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_53 ),
    inference(resolution,[],[f626,f49])).

fof(f49,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f626,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | spl1_53 ),
    inference(avatar_component_clause,[],[f624])).

fof(f332,plain,
    ( ~ spl1_3
    | ~ spl1_5
    | spl1_28 ),
    inference(avatar_split_clause,[],[f330,f304,f124,f105])).

fof(f304,plain,
    ( spl1_28
  <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_28])])).

fof(f330,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK0)
    | spl1_28 ),
    inference(resolution,[],[f306,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f306,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | spl1_28 ),
    inference(avatar_component_clause,[],[f304])).

fof(f329,plain,
    ( ~ spl1_28
    | spl1_33
    | ~ spl1_8 ),
    inference(avatar_split_clause,[],[f302,f137,f326,f304])).

fof(f137,plain,
    ( spl1_8
  <=> ! [X1] :
        ( k4_relat_1(k5_relat_1(X1,k1_xboole_0)) = k5_relat_1(k1_xboole_0,k4_relat_1(X1))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f302,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))
    | ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_8 ),
    inference(superposition,[],[f49,f293])).

% (27409)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% (27418)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% (27395)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% (27421)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% (27401)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% (27422)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% (27418)Refutation not found, incomplete strategy% (27418)------------------------------
% (27418)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (27418)Termination reason: Refutation not found, incomplete strategy

% (27418)Memory used [KB]: 10746
% (27418)Time elapsed: 0.081 s
% (27418)------------------------------
% (27418)------------------------------
% (27425)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% (27413)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% (27412)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% (27412)Refutation not found, incomplete strategy% (27412)------------------------------
% (27412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (27412)Termination reason: Refutation not found, incomplete strategy

% (27412)Memory used [KB]: 10618
% (27412)Time elapsed: 0.160 s
% (27412)------------------------------
% (27412)------------------------------
% (27416)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% (27414)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% (27402)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
fof(f293,plain,
    ( k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k5_relat_1(k1_xboole_0,k4_relat_1(sK0))
    | ~ spl1_8 ),
    inference(resolution,[],[f138,f41])).

fof(f138,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(X1)
        | k4_relat_1(k5_relat_1(X1,k1_xboole_0)) = k5_relat_1(k1_xboole_0,k4_relat_1(X1)) )
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f137])).

fof(f324,plain,
    ( ~ spl1_28
    | spl1_32
    | ~ spl1_8 ),
    inference(avatar_split_clause,[],[f301,f137,f321,f304])).

fof(f301,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))
    | ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_8 ),
    inference(superposition,[],[f50,f293])).

fof(f50,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(f257,plain,
    ( ~ spl1_5
    | ~ spl1_3
    | spl1_19 ),
    inference(avatar_split_clause,[],[f255,f229,f105,f124])).

fof(f255,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | spl1_19 ),
    inference(resolution,[],[f231,f61])).

fof(f231,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | spl1_19 ),
    inference(avatar_component_clause,[],[f229])).

fof(f142,plain,(
    spl1_5 ),
    inference(avatar_contradiction_clause,[],[f141])).

fof(f141,plain,
    ( $false
    | spl1_5 ),
    inference(resolution,[],[f140,f43])).

fof(f43,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f140,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl1_5 ),
    inference(resolution,[],[f126,f48])).

fof(f48,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f126,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl1_5 ),
    inference(avatar_component_clause,[],[f124])).

fof(f139,plain,
    ( ~ spl1_5
    | spl1_8
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f120,f109,f137,f124])).

fof(f120,plain,
    ( ! [X1] :
        ( k4_relat_1(k5_relat_1(X1,k1_xboole_0)) = k5_relat_1(k1_xboole_0,k4_relat_1(X1))
        | ~ v1_relat_1(k1_xboole_0)
        | ~ v1_relat_1(X1) )
    | ~ spl1_4 ),
    inference(superposition,[],[f53,f111])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

fof(f117,plain,(
    spl1_3 ),
    inference(avatar_contradiction_clause,[],[f115])).

fof(f115,plain,
    ( $false
    | spl1_3 ),
    inference(resolution,[],[f107,f41])).

fof(f107,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_3 ),
    inference(avatar_component_clause,[],[f105])).

fof(f114,plain,
    ( ~ spl1_3
    | spl1_4 ),
    inference(avatar_split_clause,[],[f113,f109,f105])).

fof(f113,plain,
    ( k1_xboole_0 = k4_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK0) ),
    inference(forward_demodulation,[],[f102,f92])).

fof(f92,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f77,f76])).

fof(f76,plain,(
    ! [X0] : k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f55,f71])).

fof(f71,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f58,f70])).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f55,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f77,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f56,f71])).

fof(f56,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f102,plain,
    ( k1_xboole_0 = k4_relat_1(k4_xboole_0(sK0,sK0))
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f92,f99])).

fof(f99,plain,(
    ! [X7] :
      ( k4_relat_1(k4_xboole_0(X7,sK0)) = k4_xboole_0(k4_relat_1(X7),k4_relat_1(sK0))
      | ~ v1_relat_1(X7) ) ),
    inference(resolution,[],[f75,f41])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k4_relat_1(k4_xboole_0(X0,X1)) = k4_xboole_0(k4_relat_1(X0),k4_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f52,f57,f57])).

fof(f57,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_relat_1)).

fof(f88,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f42,f85,f81])).

fof(f42,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:30:33 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (27407)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (27415)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (27424)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.32/0.53  % (27399)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.48/0.55  % (27406)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.48/0.55  % (27397)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.48/0.56  % (27398)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.48/0.56  % (27423)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.48/0.56  % (27400)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.48/0.56  % (27407)Refutation found. Thanks to Tanya!
% 1.48/0.56  % SZS status Theorem for theBenchmark
% 1.48/0.56  % SZS output start Proof for theBenchmark
% 1.48/0.56  fof(f972,plain,(
% 1.48/0.56    $false),
% 1.48/0.56    inference(avatar_sat_refutation,[],[f88,f114,f117,f139,f142,f257,f324,f329,f332,f637,f690,f692,f702,f760,f943,f945,f971])).
% 1.48/0.56  fof(f971,plain,(
% 1.48/0.56    ~spl1_19 | spl1_1 | ~spl1_60),
% 1.48/0.56    inference(avatar_split_clause,[],[f970,f813,f81,f229])).
% 1.48/0.56  fof(f229,plain,(
% 1.48/0.56    spl1_19 <=> v1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_19])])).
% 1.48/0.56  fof(f81,plain,(
% 1.48/0.56    spl1_1 <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 1.48/0.56  fof(f813,plain,(
% 1.48/0.56    spl1_60 <=> k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_60])])).
% 1.48/0.56  fof(f970,plain,(
% 1.48/0.56    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) | ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~spl1_60),
% 1.48/0.56    inference(forward_demodulation,[],[f969,f73])).
% 1.48/0.56  fof(f73,plain,(
% 1.48/0.56    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 1.48/0.56    inference(definition_unfolding,[],[f47,f72])).
% 1.48/0.56  fof(f72,plain,(
% 1.48/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 1.48/0.56    inference(definition_unfolding,[],[f59,f70])).
% 1.48/0.56  fof(f70,plain,(
% 1.48/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 1.48/0.56    inference(definition_unfolding,[],[f60,f69])).
% 1.48/0.56  fof(f69,plain,(
% 1.48/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 1.48/0.56    inference(definition_unfolding,[],[f65,f68])).
% 1.48/0.56  fof(f68,plain,(
% 1.48/0.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 1.48/0.56    inference(definition_unfolding,[],[f66,f67])).
% 1.48/0.56  fof(f67,plain,(
% 1.48/0.56    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f9])).
% 1.48/0.56  fof(f9,axiom,(
% 1.48/0.56    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.48/0.56  fof(f66,plain,(
% 1.48/0.56    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f8])).
% 1.48/0.56  fof(f8,axiom,(
% 1.48/0.56    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.48/0.56  fof(f65,plain,(
% 1.48/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f7])).
% 1.48/0.56  fof(f7,axiom,(
% 1.48/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.48/0.56  fof(f60,plain,(
% 1.48/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f6])).
% 1.48/0.56  fof(f6,axiom,(
% 1.48/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.48/0.56  fof(f59,plain,(
% 1.48/0.56    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f13])).
% 1.48/0.56  fof(f13,axiom,(
% 1.48/0.56    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.48/0.56  fof(f47,plain,(
% 1.48/0.56    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f3])).
% 1.48/0.56  fof(f3,axiom,(
% 1.48/0.56    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.48/0.56  fof(f969,plain,(
% 1.48/0.56    k5_relat_1(k1_xboole_0,sK0) = k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k1_xboole_0)) | ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~spl1_60),
% 1.48/0.56    inference(forward_demodulation,[],[f964,f79])).
% 1.48/0.56  % (27404)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.48/0.56  fof(f79,plain,(
% 1.48/0.56    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.48/0.56    inference(equality_resolution,[],[f63])).
% 1.48/0.56  fof(f63,plain,(
% 1.48/0.56    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.48/0.56    inference(cnf_transformation,[],[f40])).
% 1.48/0.56  fof(f40,plain,(
% 1.48/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.48/0.56    inference(flattening,[],[f39])).
% 1.48/0.56  fof(f39,plain,(
% 1.48/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.48/0.56    inference(nnf_transformation,[],[f11])).
% 1.48/0.56  fof(f11,axiom,(
% 1.48/0.56    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.48/0.56  fof(f964,plain,(
% 1.48/0.56    k5_relat_1(k1_xboole_0,sK0) = k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) | ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~spl1_60),
% 1.48/0.56    inference(superposition,[],[f74,f815])).
% 1.48/0.56  fof(f815,plain,(
% 1.48/0.56    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~spl1_60),
% 1.48/0.56    inference(avatar_component_clause,[],[f813])).
% 1.48/0.56  fof(f74,plain,(
% 1.48/0.56    ( ! [X0] : (k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 | ~v1_relat_1(X0)) )),
% 1.48/0.56    inference(definition_unfolding,[],[f51,f72])).
% 1.48/0.56  fof(f51,plain,(
% 1.48/0.56    ( ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f30])).
% 1.48/0.56  fof(f30,plain,(
% 1.48/0.56    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.48/0.56    inference(ennf_transformation,[],[f18])).
% 1.48/0.56  fof(f18,axiom,(
% 1.48/0.56    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).
% 1.48/0.56  fof(f945,plain,(
% 1.48/0.56    spl1_65),
% 1.48/0.56    inference(avatar_contradiction_clause,[],[f944])).
% 1.48/0.56  fof(f944,plain,(
% 1.48/0.56    $false | spl1_65),
% 1.48/0.56    inference(resolution,[],[f942,f46])).
% 1.48/0.56  fof(f46,plain,(
% 1.48/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f4])).
% 1.48/0.56  fof(f4,axiom,(
% 1.48/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.48/0.56  fof(f942,plain,(
% 1.48/0.56    ~r1_tarski(k1_xboole_0,k1_relat_1(sK0)) | spl1_65),
% 1.48/0.56    inference(avatar_component_clause,[],[f940])).
% 1.48/0.56  fof(f940,plain,(
% 1.48/0.56    spl1_65 <=> r1_tarski(k1_xboole_0,k1_relat_1(sK0))),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_65])])).
% 1.48/0.56  fof(f943,plain,(
% 1.48/0.56    ~spl1_5 | ~spl1_3 | ~spl1_65 | spl1_60),
% 1.48/0.56    inference(avatar_split_clause,[],[f938,f813,f940,f105,f124])).
% 1.48/0.56  fof(f124,plain,(
% 1.48/0.56    spl1_5 <=> v1_relat_1(k1_xboole_0)),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 1.48/0.56  fof(f105,plain,(
% 1.48/0.56    spl1_3 <=> v1_relat_1(sK0)),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 1.48/0.56  fof(f938,plain,(
% 1.48/0.56    ~r1_tarski(k1_xboole_0,k1_relat_1(sK0)) | ~v1_relat_1(sK0) | ~v1_relat_1(k1_xboole_0) | spl1_60),
% 1.48/0.56    inference(forward_demodulation,[],[f937,f45])).
% 1.48/0.56  fof(f45,plain,(
% 1.48/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.48/0.56    inference(cnf_transformation,[],[f22])).
% 1.48/0.56  fof(f22,axiom,(
% 1.48/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.48/0.56  fof(f937,plain,(
% 1.48/0.56    ~r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(sK0)) | ~v1_relat_1(sK0) | ~v1_relat_1(k1_xboole_0) | spl1_60),
% 1.48/0.56    inference(trivial_inequality_removal,[],[f936])).
% 1.48/0.56  fof(f936,plain,(
% 1.48/0.56    k1_xboole_0 != k1_xboole_0 | ~r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(sK0)) | ~v1_relat_1(sK0) | ~v1_relat_1(k1_xboole_0) | spl1_60),
% 1.48/0.56    inference(forward_demodulation,[],[f935,f44])).
% 1.48/0.56  fof(f44,plain,(
% 1.48/0.56    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.48/0.56    inference(cnf_transformation,[],[f22])).
% 1.48/0.56  fof(f935,plain,(
% 1.48/0.56    k1_xboole_0 != k1_relat_1(k1_xboole_0) | ~r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(sK0)) | ~v1_relat_1(sK0) | ~v1_relat_1(k1_xboole_0) | spl1_60),
% 1.48/0.56    inference(superposition,[],[f814,f54])).
% 1.48/0.56  fof(f54,plain,(
% 1.48/0.56    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f34])).
% 1.48/0.56  fof(f34,plain,(
% 1.48/0.56    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.48/0.56    inference(flattening,[],[f33])).
% 1.48/0.56  fof(f33,plain,(
% 1.48/0.56    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.48/0.56    inference(ennf_transformation,[],[f20])).
% 1.48/0.56  fof(f20,axiom,(
% 1.48/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).
% 1.48/0.56  fof(f814,plain,(
% 1.48/0.56    k1_xboole_0 != k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | spl1_60),
% 1.48/0.56    inference(avatar_component_clause,[],[f813])).
% 1.48/0.56  fof(f760,plain,(
% 1.48/0.56    spl1_2 | ~spl1_4 | ~spl1_32 | ~spl1_55),
% 1.48/0.56    inference(avatar_contradiction_clause,[],[f759])).
% 1.48/0.56  fof(f759,plain,(
% 1.48/0.56    $false | (spl1_2 | ~spl1_4 | ~spl1_32 | ~spl1_55)),
% 1.48/0.56    inference(trivial_inequality_removal,[],[f755])).
% 1.48/0.56  fof(f755,plain,(
% 1.48/0.56    k1_xboole_0 != k1_xboole_0 | (spl1_2 | ~spl1_4 | ~spl1_32 | ~spl1_55)),
% 1.48/0.56    inference(superposition,[],[f87,f727])).
% 1.48/0.56  fof(f727,plain,(
% 1.48/0.56    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | (~spl1_4 | ~spl1_32 | ~spl1_55)),
% 1.48/0.56    inference(forward_demodulation,[],[f707,f111])).
% 1.48/0.56  fof(f111,plain,(
% 1.48/0.56    k1_xboole_0 = k4_relat_1(k1_xboole_0) | ~spl1_4),
% 1.48/0.56    inference(avatar_component_clause,[],[f109])).
% 1.48/0.56  fof(f109,plain,(
% 1.48/0.56    spl1_4 <=> k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 1.48/0.56  fof(f707,plain,(
% 1.48/0.56    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k1_xboole_0) | (~spl1_32 | ~spl1_55)),
% 1.48/0.56    inference(backward_demodulation,[],[f323,f701])).
% 1.48/0.56  fof(f701,plain,(
% 1.48/0.56    k1_xboole_0 = k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) | ~spl1_55),
% 1.48/0.56    inference(avatar_component_clause,[],[f699])).
% 1.48/0.56  fof(f699,plain,(
% 1.48/0.56    spl1_55 <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,k4_relat_1(sK0))),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_55])])).
% 1.48/0.56  fof(f323,plain,(
% 1.48/0.56    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) | ~spl1_32),
% 1.48/0.56    inference(avatar_component_clause,[],[f321])).
% 1.48/0.56  fof(f321,plain,(
% 1.48/0.56    spl1_32 <=> k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_32])])).
% 1.48/0.56  fof(f87,plain,(
% 1.48/0.56    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | spl1_2),
% 1.48/0.56    inference(avatar_component_clause,[],[f85])).
% 1.48/0.56  fof(f85,plain,(
% 1.48/0.56    spl1_2 <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 1.48/0.56  fof(f702,plain,(
% 1.48/0.56    ~spl1_33 | spl1_55 | ~spl1_51),
% 1.48/0.56    inference(avatar_split_clause,[],[f697,f610,f699,f326])).
% 1.48/0.56  fof(f326,plain,(
% 1.48/0.56    spl1_33 <=> v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_33])])).
% 1.48/0.56  fof(f610,plain,(
% 1.48/0.56    spl1_51 <=> k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_51])])).
% 1.48/0.56  fof(f697,plain,(
% 1.48/0.56    k1_xboole_0 = k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) | ~v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) | ~spl1_51),
% 1.48/0.56    inference(forward_demodulation,[],[f696,f73])).
% 1.48/0.56  fof(f696,plain,(
% 1.48/0.56    k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k1_xboole_0)) | ~v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) | ~spl1_51),
% 1.48/0.56    inference(forward_demodulation,[],[f695,f79])).
% 1.48/0.56  fof(f695,plain,(
% 1.48/0.56    k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))))) | ~v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) | ~spl1_51),
% 1.48/0.56    inference(superposition,[],[f74,f612])).
% 1.48/0.56  fof(f612,plain,(
% 1.48/0.56    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) | ~spl1_51),
% 1.48/0.56    inference(avatar_component_clause,[],[f610])).
% 1.48/0.56  fof(f692,plain,(
% 1.48/0.56    spl1_54),
% 1.48/0.56    inference(avatar_contradiction_clause,[],[f691])).
% 1.48/0.56  fof(f691,plain,(
% 1.48/0.56    $false | spl1_54),
% 1.48/0.56    inference(resolution,[],[f689,f46])).
% 1.48/0.56  fof(f689,plain,(
% 1.48/0.56    ~r1_tarski(k1_xboole_0,k1_relat_1(k4_relat_1(sK0))) | spl1_54),
% 1.48/0.56    inference(avatar_component_clause,[],[f687])).
% 1.48/0.56  fof(f687,plain,(
% 1.48/0.56    spl1_54 <=> r1_tarski(k1_xboole_0,k1_relat_1(k4_relat_1(sK0)))),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_54])])).
% 1.48/0.56  fof(f690,plain,(
% 1.48/0.56    ~spl1_5 | ~spl1_53 | ~spl1_54 | spl1_51),
% 1.48/0.56    inference(avatar_split_clause,[],[f685,f610,f687,f624,f124])).
% 1.48/0.56  fof(f624,plain,(
% 1.48/0.56    spl1_53 <=> v1_relat_1(k4_relat_1(sK0))),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_53])])).
% 1.48/0.56  fof(f685,plain,(
% 1.48/0.56    ~r1_tarski(k1_xboole_0,k1_relat_1(k4_relat_1(sK0))) | ~v1_relat_1(k4_relat_1(sK0)) | ~v1_relat_1(k1_xboole_0) | spl1_51),
% 1.48/0.56    inference(forward_demodulation,[],[f684,f45])).
% 1.48/0.56  fof(f684,plain,(
% 1.48/0.56    ~r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(k4_relat_1(sK0))) | ~v1_relat_1(k4_relat_1(sK0)) | ~v1_relat_1(k1_xboole_0) | spl1_51),
% 1.48/0.56    inference(trivial_inequality_removal,[],[f683])).
% 1.48/0.56  fof(f683,plain,(
% 1.48/0.56    k1_xboole_0 != k1_xboole_0 | ~r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(k4_relat_1(sK0))) | ~v1_relat_1(k4_relat_1(sK0)) | ~v1_relat_1(k1_xboole_0) | spl1_51),
% 1.48/0.56    inference(forward_demodulation,[],[f682,f44])).
% 1.48/0.56  fof(f682,plain,(
% 1.48/0.56    k1_xboole_0 != k1_relat_1(k1_xboole_0) | ~r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(k4_relat_1(sK0))) | ~v1_relat_1(k4_relat_1(sK0)) | ~v1_relat_1(k1_xboole_0) | spl1_51),
% 1.48/0.56    inference(superposition,[],[f611,f54])).
% 1.48/0.56  fof(f611,plain,(
% 1.48/0.56    k1_xboole_0 != k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) | spl1_51),
% 1.48/0.56    inference(avatar_component_clause,[],[f610])).
% 1.48/0.56  fof(f637,plain,(
% 1.48/0.56    spl1_53),
% 1.48/0.56    inference(avatar_contradiction_clause,[],[f635])).
% 1.48/0.56  fof(f635,plain,(
% 1.48/0.56    $false | spl1_53),
% 1.48/0.56    inference(resolution,[],[f633,f41])).
% 1.48/0.56  fof(f41,plain,(
% 1.48/0.56    v1_relat_1(sK0)),
% 1.48/0.56    inference(cnf_transformation,[],[f38])).
% 1.48/0.56  fof(f38,plain,(
% 1.48/0.56    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 1.48/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f37])).
% 1.48/0.56  fof(f37,plain,(
% 1.48/0.56    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 1.48/0.56    introduced(choice_axiom,[])).
% 1.48/0.56  fof(f26,plain,(
% 1.48/0.56    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 1.48/0.56    inference(ennf_transformation,[],[f24])).
% 1.48/0.56  fof(f24,negated_conjecture,(
% 1.48/0.56    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.48/0.56    inference(negated_conjecture,[],[f23])).
% 1.48/0.56  fof(f23,conjecture,(
% 1.48/0.56    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).
% 1.48/0.56  fof(f633,plain,(
% 1.48/0.56    ~v1_relat_1(sK0) | spl1_53),
% 1.48/0.56    inference(resolution,[],[f626,f49])).
% 1.48/0.56  fof(f49,plain,(
% 1.48/0.56    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f28])).
% 1.48/0.56  fof(f28,plain,(
% 1.48/0.56    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.48/0.56    inference(ennf_transformation,[],[f15])).
% 1.48/0.56  fof(f15,axiom,(
% 1.48/0.56    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 1.48/0.56  fof(f626,plain,(
% 1.48/0.56    ~v1_relat_1(k4_relat_1(sK0)) | spl1_53),
% 1.48/0.56    inference(avatar_component_clause,[],[f624])).
% 1.48/0.56  fof(f332,plain,(
% 1.48/0.56    ~spl1_3 | ~spl1_5 | spl1_28),
% 1.48/0.56    inference(avatar_split_clause,[],[f330,f304,f124,f105])).
% 1.48/0.56  fof(f304,plain,(
% 1.48/0.56    spl1_28 <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_28])])).
% 1.48/0.56  fof(f330,plain,(
% 1.48/0.56    ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK0) | spl1_28),
% 1.48/0.56    inference(resolution,[],[f306,f61])).
% 1.48/0.56  fof(f61,plain,(
% 1.48/0.56    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f36])).
% 1.48/0.56  fof(f36,plain,(
% 1.48/0.56    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.48/0.56    inference(flattening,[],[f35])).
% 1.48/0.56  fof(f35,plain,(
% 1.48/0.56    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.48/0.56    inference(ennf_transformation,[],[f16])).
% 1.48/0.56  fof(f16,axiom,(
% 1.48/0.56    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.48/0.56  fof(f306,plain,(
% 1.48/0.56    ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | spl1_28),
% 1.48/0.56    inference(avatar_component_clause,[],[f304])).
% 1.48/0.56  fof(f329,plain,(
% 1.48/0.56    ~spl1_28 | spl1_33 | ~spl1_8),
% 1.48/0.56    inference(avatar_split_clause,[],[f302,f137,f326,f304])).
% 1.48/0.56  fof(f137,plain,(
% 1.48/0.56    spl1_8 <=> ! [X1] : (k4_relat_1(k5_relat_1(X1,k1_xboole_0)) = k5_relat_1(k1_xboole_0,k4_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 1.48/0.56  fof(f302,plain,(
% 1.48/0.56    v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) | ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | ~spl1_8),
% 1.48/0.56    inference(superposition,[],[f49,f293])).
% 1.48/0.56  % (27409)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.48/0.56  % (27418)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.48/0.56  % (27395)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.48/0.56  % (27421)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.48/0.57  % (27401)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.48/0.57  % (27422)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.48/0.57  % (27418)Refutation not found, incomplete strategy% (27418)------------------------------
% 1.48/0.57  % (27418)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.57  % (27418)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.57  
% 1.48/0.57  % (27418)Memory used [KB]: 10746
% 1.48/0.57  % (27418)Time elapsed: 0.081 s
% 1.48/0.57  % (27418)------------------------------
% 1.48/0.57  % (27418)------------------------------
% 1.48/0.57  % (27425)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.48/0.57  % (27413)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.48/0.57  % (27412)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.48/0.57  % (27412)Refutation not found, incomplete strategy% (27412)------------------------------
% 1.48/0.57  % (27412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.57  % (27412)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.57  
% 1.48/0.57  % (27412)Memory used [KB]: 10618
% 1.48/0.57  % (27412)Time elapsed: 0.160 s
% 1.48/0.57  % (27412)------------------------------
% 1.48/0.57  % (27412)------------------------------
% 1.48/0.57  % (27416)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.48/0.58  % (27414)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.48/0.58  % (27402)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.48/0.58  fof(f293,plain,(
% 1.48/0.58    k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) | ~spl1_8),
% 1.48/0.58    inference(resolution,[],[f138,f41])).
% 1.48/0.58  fof(f138,plain,(
% 1.48/0.58    ( ! [X1] : (~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X1,k1_xboole_0)) = k5_relat_1(k1_xboole_0,k4_relat_1(X1))) ) | ~spl1_8),
% 1.48/0.58    inference(avatar_component_clause,[],[f137])).
% 1.48/0.58  fof(f324,plain,(
% 1.48/0.58    ~spl1_28 | spl1_32 | ~spl1_8),
% 1.48/0.58    inference(avatar_split_clause,[],[f301,f137,f321,f304])).
% 1.48/0.58  fof(f301,plain,(
% 1.48/0.58    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) | ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | ~spl1_8),
% 1.48/0.58    inference(superposition,[],[f50,f293])).
% 1.48/0.58  fof(f50,plain,(
% 1.48/0.58    ( ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f29])).
% 1.48/0.58  fof(f29,plain,(
% 1.48/0.58    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 1.48/0.58    inference(ennf_transformation,[],[f17])).
% 1.48/0.58  fof(f17,axiom,(
% 1.48/0.58    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 1.48/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).
% 1.48/0.58  fof(f257,plain,(
% 1.48/0.58    ~spl1_5 | ~spl1_3 | spl1_19),
% 1.48/0.58    inference(avatar_split_clause,[],[f255,f229,f105,f124])).
% 1.48/0.58  fof(f255,plain,(
% 1.48/0.58    ~v1_relat_1(sK0) | ~v1_relat_1(k1_xboole_0) | spl1_19),
% 1.48/0.58    inference(resolution,[],[f231,f61])).
% 1.48/0.58  fof(f231,plain,(
% 1.48/0.58    ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | spl1_19),
% 1.48/0.58    inference(avatar_component_clause,[],[f229])).
% 1.48/0.58  fof(f142,plain,(
% 1.48/0.58    spl1_5),
% 1.48/0.58    inference(avatar_contradiction_clause,[],[f141])).
% 1.48/0.58  fof(f141,plain,(
% 1.48/0.58    $false | spl1_5),
% 1.48/0.58    inference(resolution,[],[f140,f43])).
% 1.48/0.58  fof(f43,plain,(
% 1.48/0.58    v1_xboole_0(k1_xboole_0)),
% 1.48/0.58    inference(cnf_transformation,[],[f1])).
% 1.48/0.58  fof(f1,axiom,(
% 1.48/0.58    v1_xboole_0(k1_xboole_0)),
% 1.48/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.48/0.58  fof(f140,plain,(
% 1.48/0.58    ~v1_xboole_0(k1_xboole_0) | spl1_5),
% 1.48/0.58    inference(resolution,[],[f126,f48])).
% 1.48/0.58  fof(f48,plain,(
% 1.48/0.58    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f27])).
% 1.48/0.58  fof(f27,plain,(
% 1.48/0.58    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 1.48/0.58    inference(ennf_transformation,[],[f14])).
% 1.48/0.58  fof(f14,axiom,(
% 1.48/0.58    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 1.48/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 1.48/0.58  fof(f126,plain,(
% 1.48/0.58    ~v1_relat_1(k1_xboole_0) | spl1_5),
% 1.48/0.58    inference(avatar_component_clause,[],[f124])).
% 1.48/0.58  fof(f139,plain,(
% 1.48/0.58    ~spl1_5 | spl1_8 | ~spl1_4),
% 1.48/0.58    inference(avatar_split_clause,[],[f120,f109,f137,f124])).
% 1.48/0.58  fof(f120,plain,(
% 1.48/0.58    ( ! [X1] : (k4_relat_1(k5_relat_1(X1,k1_xboole_0)) = k5_relat_1(k1_xboole_0,k4_relat_1(X1)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X1)) ) | ~spl1_4),
% 1.48/0.58    inference(superposition,[],[f53,f111])).
% 1.48/0.58  fof(f53,plain,(
% 1.48/0.58    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f32])).
% 1.48/0.58  fof(f32,plain,(
% 1.48/0.58    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.48/0.58    inference(ennf_transformation,[],[f21])).
% 1.48/0.58  fof(f21,axiom,(
% 1.48/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 1.48/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).
% 1.48/0.58  fof(f117,plain,(
% 1.48/0.58    spl1_3),
% 1.48/0.58    inference(avatar_contradiction_clause,[],[f115])).
% 1.48/0.58  fof(f115,plain,(
% 1.48/0.58    $false | spl1_3),
% 1.48/0.58    inference(resolution,[],[f107,f41])).
% 1.48/0.58  fof(f107,plain,(
% 1.48/0.58    ~v1_relat_1(sK0) | spl1_3),
% 1.48/0.58    inference(avatar_component_clause,[],[f105])).
% 1.48/0.58  fof(f114,plain,(
% 1.48/0.58    ~spl1_3 | spl1_4),
% 1.48/0.58    inference(avatar_split_clause,[],[f113,f109,f105])).
% 1.48/0.58  fof(f113,plain,(
% 1.48/0.58    k1_xboole_0 = k4_relat_1(k1_xboole_0) | ~v1_relat_1(sK0)),
% 1.48/0.58    inference(forward_demodulation,[],[f102,f92])).
% 1.48/0.58  fof(f92,plain,(
% 1.48/0.58    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.48/0.58    inference(superposition,[],[f77,f76])).
% 1.48/0.58  fof(f76,plain,(
% 1.48/0.58    ( ! [X0] : (k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0) )),
% 1.48/0.58    inference(definition_unfolding,[],[f55,f71])).
% 1.48/0.58  fof(f71,plain,(
% 1.48/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 1.48/0.58    inference(definition_unfolding,[],[f58,f70])).
% 1.48/0.58  fof(f58,plain,(
% 1.48/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.48/0.58    inference(cnf_transformation,[],[f10])).
% 1.48/0.58  fof(f10,axiom,(
% 1.48/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.48/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.48/0.58  fof(f55,plain,(
% 1.48/0.58    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.48/0.58    inference(cnf_transformation,[],[f25])).
% 1.48/0.58  fof(f25,plain,(
% 1.48/0.58    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.48/0.58    inference(rectify,[],[f2])).
% 1.48/0.58  fof(f2,axiom,(
% 1.48/0.58    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 1.48/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 1.48/0.58  fof(f77,plain,(
% 1.48/0.58    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))) )),
% 1.48/0.58    inference(definition_unfolding,[],[f56,f71])).
% 1.48/0.58  fof(f56,plain,(
% 1.48/0.58    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.48/0.58    inference(cnf_transformation,[],[f5])).
% 1.48/0.58  fof(f5,axiom,(
% 1.48/0.58    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 1.48/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.48/0.58  fof(f102,plain,(
% 1.48/0.58    k1_xboole_0 = k4_relat_1(k4_xboole_0(sK0,sK0)) | ~v1_relat_1(sK0)),
% 1.48/0.58    inference(superposition,[],[f92,f99])).
% 1.48/0.58  fof(f99,plain,(
% 1.48/0.58    ( ! [X7] : (k4_relat_1(k4_xboole_0(X7,sK0)) = k4_xboole_0(k4_relat_1(X7),k4_relat_1(sK0)) | ~v1_relat_1(X7)) )),
% 1.48/0.58    inference(resolution,[],[f75,f41])).
% 1.48/0.58  fof(f75,plain,(
% 1.48/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | k4_relat_1(k4_xboole_0(X0,X1)) = k4_xboole_0(k4_relat_1(X0),k4_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 1.48/0.58    inference(definition_unfolding,[],[f52,f57,f57])).
% 1.48/0.58  fof(f57,plain,(
% 1.48/0.58    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k4_xboole_0(X0,X1)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f12])).
% 1.48/0.58  fof(f12,axiom,(
% 1.48/0.58    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1)),
% 1.48/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.48/0.58  fof(f52,plain,(
% 1.48/0.58    ( ! [X0,X1] : (k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f31])).
% 1.48/0.58  fof(f31,plain,(
% 1.48/0.58    ! [X0] : (! [X1] : (k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.48/0.58    inference(ennf_transformation,[],[f19])).
% 1.48/0.58  fof(f19,axiom,(
% 1.48/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1))))),
% 1.48/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_relat_1)).
% 1.48/0.58  fof(f88,plain,(
% 1.48/0.58    ~spl1_1 | ~spl1_2),
% 1.48/0.58    inference(avatar_split_clause,[],[f42,f85,f81])).
% 1.48/0.58  fof(f42,plain,(
% 1.48/0.58    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 1.48/0.58    inference(cnf_transformation,[],[f38])).
% 1.48/0.58  % SZS output end Proof for theBenchmark
% 1.48/0.58  % (27407)------------------------------
% 1.48/0.58  % (27407)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.58  % (27407)Termination reason: Refutation
% 1.48/0.58  
% 1.48/0.58  % (27407)Memory used [KB]: 6908
% 1.48/0.58  % (27407)Time elapsed: 0.159 s
% 1.48/0.58  % (27407)------------------------------
% 1.48/0.58  % (27407)------------------------------
% 1.48/0.58  % (27394)Success in time 0.22 s
%------------------------------------------------------------------------------
