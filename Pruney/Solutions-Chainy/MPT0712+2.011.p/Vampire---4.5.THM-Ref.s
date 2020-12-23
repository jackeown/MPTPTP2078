%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:44 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 143 expanded)
%              Number of leaves         :   22 (  52 expanded)
%              Depth                    :   13
%              Number of atoms          :  249 ( 370 expanded)
%              Number of equality atoms :   29 (  42 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f296,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f66,f71,f82,f135,f149,f164,f169,f190,f193,f295])).

% (8658)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
fof(f295,plain,
    ( ~ spl2_2
    | ~ spl2_3
    | spl2_4
    | ~ spl2_9 ),
    inference(avatar_contradiction_clause,[],[f294])).

fof(f294,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_3
    | spl2_4
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f293,f70])).

fof(f70,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl2_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f293,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl2_2
    | spl2_4
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f292,f65])).

fof(f65,plain,
    ( v1_funct_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl2_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f292,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl2_4
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f291,f128])).

fof(f128,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl2_9
  <=> r2_hidden(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f291,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl2_4 ),
    inference(subsumption_resolution,[],[f275,f55])).

fof(f55,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f275,plain,
    ( ~ r1_tarski(k1_tarski(k1_funct_1(sK1,sK0)),k1_tarski(k1_funct_1(sK1,sK0)))
    | ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl2_4 ),
    inference(superposition,[],[f81,f122])).

fof(f122,plain,(
    ! [X4,X3] :
      ( k1_tarski(k1_funct_1(X3,X4)) = k9_relat_1(X3,k1_tarski(X4))
      | ~ r2_hidden(X4,k1_relat_1(X3))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(forward_demodulation,[],[f121,f50])).

fof(f50,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f121,plain,(
    ! [X4,X3] :
      ( k1_tarski(k1_funct_1(X3,X4)) = k9_relat_1(X3,k2_tarski(X4,X4))
      | ~ r2_hidden(X4,k1_relat_1(X3))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f118])).

fof(f118,plain,(
    ! [X4,X3] :
      ( k1_tarski(k1_funct_1(X3,X4)) = k9_relat_1(X3,k2_tarski(X4,X4))
      | ~ r2_hidden(X4,k1_relat_1(X3))
      | ~ r2_hidden(X4,k1_relat_1(X3))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(superposition,[],[f45,f50])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r2_hidden(X1,k1_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) )
       => k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_funct_1)).

fof(f81,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,k1_tarski(sK0)),k1_tarski(k1_funct_1(sK1,sK0)))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl2_4
  <=> r1_tarski(k9_relat_1(sK1,k1_tarski(sK0)),k1_tarski(k1_funct_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f193,plain,
    ( spl2_9
    | spl2_5 ),
    inference(avatar_split_clause,[],[f192,f91,f126])).

fof(f91,plain,
    ( spl2_5
  <=> r1_xboole_0(k1_tarski(sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f192,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | spl2_5 ),
    inference(resolution,[],[f93,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f93,plain,
    ( ~ r1_xboole_0(k1_tarski(sK0),k1_relat_1(sK1))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f91])).

fof(f190,plain,
    ( ~ spl2_5
    | spl2_1
    | ~ spl2_3
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f189,f159,f68,f58,f91])).

fof(f58,plain,
    ( spl2_1
  <=> r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f159,plain,
    ( spl2_11
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f189,plain,
    ( ~ r1_xboole_0(k1_tarski(sK0),k1_relat_1(sK1))
    | spl2_1
    | ~ spl2_3
    | ~ spl2_11 ),
    inference(subsumption_resolution,[],[f188,f44])).

fof(f44,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f188,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1(sK1,sK0)))
    | ~ r1_xboole_0(k1_tarski(sK0),k1_relat_1(sK1))
    | spl2_1
    | ~ spl2_3
    | ~ spl2_11 ),
    inference(forward_demodulation,[],[f187,f161])).

fof(f161,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f159])).

fof(f187,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_tarski(k1_funct_1(sK1,sK0)))
    | ~ r1_xboole_0(k1_tarski(sK0),k1_relat_1(sK1))
    | spl2_1
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f140,f70])).

fof(f140,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_tarski(k1_funct_1(sK1,sK0)))
    | ~ r1_xboole_0(k1_tarski(sK0),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | spl2_1 ),
    inference(superposition,[],[f60,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

fof(f60,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f169,plain,(
    ~ spl2_10 ),
    inference(avatar_contradiction_clause,[],[f165])).

fof(f165,plain,
    ( $false
    | ~ spl2_10 ),
    inference(unit_resulting_resolution,[],[f51,f157])).

fof(f157,plain,
    ( ! [X0] : ~ r1_xboole_0(X0,k1_relat_1(k1_xboole_0))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl2_10
  <=> ! [X0] : ~ r1_xboole_0(X0,k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f51,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f164,plain,
    ( spl2_10
    | spl2_11
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f163,f103,f159,f156])).

fof(f103,plain,
    ( spl2_8
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f163,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
        | ~ r1_xboole_0(X0,k1_relat_1(k1_xboole_0)) )
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f152,f105])).

fof(f105,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f103])).

fof(f152,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ r1_xboole_0(X0,k1_relat_1(k1_xboole_0)) ) ),
    inference(superposition,[],[f52,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X0,X1) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0)
      | ~ r1_xboole_0(X1,k1_relat_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X0,X1) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f46,f48])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f52,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

fof(f149,plain,
    ( spl2_7
    | spl2_8 ),
    inference(avatar_split_clause,[],[f145,f103,f100])).

fof(f100,plain,
    ( spl2_7
  <=> ! [X3,X2] :
        ( ~ v1_relat_1(X2)
        | ~ r1_xboole_0(X3,k1_relat_1(X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f145,plain,(
    ! [X6,X5] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X5)
      | ~ r1_xboole_0(X6,k1_relat_1(X5)) ) ),
    inference(duplicate_literal_removal,[],[f143])).

fof(f143,plain,(
    ! [X6,X5] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X5)
      | ~ r1_xboole_0(X6,k1_relat_1(X5))
      | ~ v1_relat_1(X5) ) ),
    inference(superposition,[],[f47,f48])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f135,plain,
    ( ~ spl2_3
    | ~ spl2_7 ),
    inference(avatar_contradiction_clause,[],[f130])).

fof(f130,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(unit_resulting_resolution,[],[f70,f51,f101])).

fof(f101,plain,
    ( ! [X2,X3] :
        ( ~ r1_xboole_0(X3,k1_relat_1(X2))
        | ~ v1_relat_1(X2) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f100])).

fof(f82,plain,
    ( ~ spl2_4
    | spl2_1
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f77,f68,f58,f79])).

% (8658)Refutation not found, incomplete strategy% (8658)------------------------------
% (8658)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (8658)Termination reason: Refutation not found, incomplete strategy

% (8658)Memory used [KB]: 10746
% (8658)Time elapsed: 0.091 s
% (8658)------------------------------
% (8658)------------------------------
fof(f77,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,k1_tarski(sK0)),k1_tarski(k1_funct_1(sK1,sK0)))
    | spl2_1
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f76,f70])).

fof(f76,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,k1_tarski(sK0)),k1_tarski(k1_funct_1(sK1,sK0)))
    | ~ v1_relat_1(sK1)
    | spl2_1 ),
    inference(superposition,[],[f60,f46])).

fof(f71,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f36,f68])).

fof(f36,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f32])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_funct_1)).

fof(f66,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f37,f63])).

fof(f37,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f61,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f38,f58])).

fof(f38,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:57:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.51  % (8652)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (8653)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (8650)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.52  % (8669)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.52  % (8662)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.52  % (8654)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (8662)Refutation not found, incomplete strategy% (8662)------------------------------
% 0.20/0.52  % (8662)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (8656)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.53  % (8659)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.53  % (8662)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (8662)Memory used [KB]: 1663
% 0.20/0.53  % (8662)Time elapsed: 0.114 s
% 0.20/0.53  % (8662)------------------------------
% 0.20/0.53  % (8662)------------------------------
% 0.20/0.53  % (8668)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.53  % (8651)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (8669)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f296,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(avatar_sat_refutation,[],[f61,f66,f71,f82,f135,f149,f164,f169,f190,f193,f295])).
% 0.20/0.53  % (8658)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.53  fof(f295,plain,(
% 0.20/0.53    ~spl2_2 | ~spl2_3 | spl2_4 | ~spl2_9),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f294])).
% 0.20/0.53  fof(f294,plain,(
% 0.20/0.53    $false | (~spl2_2 | ~spl2_3 | spl2_4 | ~spl2_9)),
% 0.20/0.53    inference(subsumption_resolution,[],[f293,f70])).
% 0.20/0.53  fof(f70,plain,(
% 0.20/0.53    v1_relat_1(sK1) | ~spl2_3),
% 0.20/0.53    inference(avatar_component_clause,[],[f68])).
% 0.20/0.53  fof(f68,plain,(
% 0.20/0.53    spl2_3 <=> v1_relat_1(sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.53  fof(f293,plain,(
% 0.20/0.53    ~v1_relat_1(sK1) | (~spl2_2 | spl2_4 | ~spl2_9)),
% 0.20/0.53    inference(subsumption_resolution,[],[f292,f65])).
% 0.20/0.53  fof(f65,plain,(
% 0.20/0.53    v1_funct_1(sK1) | ~spl2_2),
% 0.20/0.53    inference(avatar_component_clause,[],[f63])).
% 0.20/0.53  fof(f63,plain,(
% 0.20/0.53    spl2_2 <=> v1_funct_1(sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.53  fof(f292,plain,(
% 0.20/0.53    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (spl2_4 | ~spl2_9)),
% 0.20/0.53    inference(subsumption_resolution,[],[f291,f128])).
% 0.20/0.53  fof(f128,plain,(
% 0.20/0.53    r2_hidden(sK0,k1_relat_1(sK1)) | ~spl2_9),
% 0.20/0.53    inference(avatar_component_clause,[],[f126])).
% 0.20/0.53  fof(f126,plain,(
% 0.20/0.53    spl2_9 <=> r2_hidden(sK0,k1_relat_1(sK1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.20/0.53  fof(f291,plain,(
% 0.20/0.53    ~r2_hidden(sK0,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl2_4),
% 0.20/0.53    inference(subsumption_resolution,[],[f275,f55])).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.53    inference(equality_resolution,[],[f42])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f35])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.53    inference(flattening,[],[f34])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.53    inference(nnf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.53  fof(f275,plain,(
% 0.20/0.53    ~r1_tarski(k1_tarski(k1_funct_1(sK1,sK0)),k1_tarski(k1_funct_1(sK1,sK0))) | ~r2_hidden(sK0,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl2_4),
% 0.20/0.53    inference(superposition,[],[f81,f122])).
% 0.20/0.53  fof(f122,plain,(
% 0.20/0.53    ( ! [X4,X3] : (k1_tarski(k1_funct_1(X3,X4)) = k9_relat_1(X3,k1_tarski(X4)) | ~r2_hidden(X4,k1_relat_1(X3)) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) )),
% 0.20/0.53    inference(forward_demodulation,[],[f121,f50])).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.53  fof(f121,plain,(
% 0.20/0.53    ( ! [X4,X3] : (k1_tarski(k1_funct_1(X3,X4)) = k9_relat_1(X3,k2_tarski(X4,X4)) | ~r2_hidden(X4,k1_relat_1(X3)) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) )),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f118])).
% 0.20/0.53  fof(f118,plain,(
% 0.20/0.53    ( ! [X4,X3] : (k1_tarski(k1_funct_1(X3,X4)) = k9_relat_1(X3,k2_tarski(X4,X4)) | ~r2_hidden(X4,k1_relat_1(X3)) | ~r2_hidden(X4,k1_relat_1(X3)) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) )),
% 0.20/0.53    inference(superposition,[],[f45,f50])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.53    inference(flattening,[],[f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) | (~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.53    inference(ennf_transformation,[],[f17])).
% 0.20/0.53  fof(f17,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r2_hidden(X1,k1_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) => k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_funct_1)).
% 0.20/0.53  fof(f81,plain,(
% 0.20/0.53    ~r1_tarski(k9_relat_1(sK1,k1_tarski(sK0)),k1_tarski(k1_funct_1(sK1,sK0))) | spl2_4),
% 0.20/0.53    inference(avatar_component_clause,[],[f79])).
% 0.20/0.53  fof(f79,plain,(
% 0.20/0.53    spl2_4 <=> r1_tarski(k9_relat_1(sK1,k1_tarski(sK0)),k1_tarski(k1_funct_1(sK1,sK0)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.53  fof(f193,plain,(
% 0.20/0.53    spl2_9 | spl2_5),
% 0.20/0.53    inference(avatar_split_clause,[],[f192,f91,f126])).
% 0.20/0.53  fof(f91,plain,(
% 0.20/0.53    spl2_5 <=> r1_xboole_0(k1_tarski(sK0),k1_relat_1(sK1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.53  fof(f192,plain,(
% 0.20/0.53    r2_hidden(sK0,k1_relat_1(sK1)) | spl2_5),
% 0.20/0.53    inference(resolution,[],[f93,f49])).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,axiom,(
% 0.20/0.53    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.20/0.53  fof(f93,plain,(
% 0.20/0.53    ~r1_xboole_0(k1_tarski(sK0),k1_relat_1(sK1)) | spl2_5),
% 0.20/0.53    inference(avatar_component_clause,[],[f91])).
% 0.20/0.53  fof(f190,plain,(
% 0.20/0.53    ~spl2_5 | spl2_1 | ~spl2_3 | ~spl2_11),
% 0.20/0.53    inference(avatar_split_clause,[],[f189,f159,f68,f58,f91])).
% 0.20/0.53  fof(f58,plain,(
% 0.20/0.53    spl2_1 <=> r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.53  fof(f159,plain,(
% 0.20/0.53    spl2_11 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.20/0.53  fof(f189,plain,(
% 0.20/0.53    ~r1_xboole_0(k1_tarski(sK0),k1_relat_1(sK1)) | (spl2_1 | ~spl2_3 | ~spl2_11)),
% 0.20/0.53    inference(subsumption_resolution,[],[f188,f44])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.53  fof(f188,plain,(
% 0.20/0.53    ~r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1(sK1,sK0))) | ~r1_xboole_0(k1_tarski(sK0),k1_relat_1(sK1)) | (spl2_1 | ~spl2_3 | ~spl2_11)),
% 0.20/0.53    inference(forward_demodulation,[],[f187,f161])).
% 0.20/0.53  fof(f161,plain,(
% 0.20/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl2_11),
% 0.20/0.53    inference(avatar_component_clause,[],[f159])).
% 0.20/0.53  fof(f187,plain,(
% 0.20/0.53    ~r1_tarski(k2_relat_1(k1_xboole_0),k1_tarski(k1_funct_1(sK1,sK0))) | ~r1_xboole_0(k1_tarski(sK0),k1_relat_1(sK1)) | (spl2_1 | ~spl2_3)),
% 0.20/0.53    inference(subsumption_resolution,[],[f140,f70])).
% 0.20/0.53  fof(f140,plain,(
% 0.20/0.53    ~r1_tarski(k2_relat_1(k1_xboole_0),k1_tarski(k1_funct_1(sK1,sK0))) | ~r1_xboole_0(k1_tarski(sK0),k1_relat_1(sK1)) | ~v1_relat_1(sK1) | spl2_1),
% 0.20/0.53    inference(superposition,[],[f60,f48])).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f16])).
% 0.20/0.53  fof(f16,axiom,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).
% 0.20/0.53  fof(f60,plain,(
% 0.20/0.53    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) | spl2_1),
% 0.20/0.53    inference(avatar_component_clause,[],[f58])).
% 0.20/0.53  fof(f169,plain,(
% 0.20/0.53    ~spl2_10),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f165])).
% 0.20/0.53  fof(f165,plain,(
% 0.20/0.53    $false | ~spl2_10),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f51,f157])).
% 0.20/0.53  fof(f157,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_xboole_0(X0,k1_relat_1(k1_xboole_0))) ) | ~spl2_10),
% 0.20/0.53    inference(avatar_component_clause,[],[f156])).
% 0.20/0.53  fof(f156,plain,(
% 0.20/0.53    spl2_10 <=> ! [X0] : ~r1_xboole_0(X0,k1_relat_1(k1_xboole_0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.20/0.53  fof(f164,plain,(
% 0.20/0.53    spl2_10 | spl2_11 | ~spl2_8),
% 0.20/0.53    inference(avatar_split_clause,[],[f163,f103,f159,f156])).
% 0.20/0.53  fof(f103,plain,(
% 0.20/0.53    spl2_8 <=> v1_relat_1(k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.53  fof(f163,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~r1_xboole_0(X0,k1_relat_1(k1_xboole_0))) ) | ~spl2_8),
% 0.20/0.53    inference(subsumption_resolution,[],[f152,f105])).
% 0.20/0.53  fof(f105,plain,(
% 0.20/0.53    v1_relat_1(k1_xboole_0) | ~spl2_8),
% 0.20/0.53    inference(avatar_component_clause,[],[f103])).
% 0.20/0.53  fof(f152,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~r1_xboole_0(X0,k1_relat_1(k1_xboole_0))) )),
% 0.20/0.53    inference(superposition,[],[f52,f88])).
% 0.20/0.53  fof(f88,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k9_relat_1(X0,X1) = k2_relat_1(k1_xboole_0) | ~v1_relat_1(X0) | ~r1_xboole_0(X1,k1_relat_1(X0))) )),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f85])).
% 0.20/0.53  fof(f85,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k9_relat_1(X0,X1) = k2_relat_1(k1_xboole_0) | ~v1_relat_1(X0) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(superposition,[],[f46,f48])).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,axiom,(
% 0.20/0.53    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f15])).
% 0.20/0.53  fof(f15,axiom,(
% 0.20/0.53    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).
% 0.20/0.53  fof(f149,plain,(
% 0.20/0.53    spl2_7 | spl2_8),
% 0.20/0.53    inference(avatar_split_clause,[],[f145,f103,f100])).
% 0.20/0.53  fof(f100,plain,(
% 0.20/0.53    spl2_7 <=> ! [X3,X2] : (~v1_relat_1(X2) | ~r1_xboole_0(X3,k1_relat_1(X2)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.53  fof(f145,plain,(
% 0.20/0.53    ( ! [X6,X5] : (v1_relat_1(k1_xboole_0) | ~v1_relat_1(X5) | ~r1_xboole_0(X6,k1_relat_1(X5))) )),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f143])).
% 0.20/0.53  fof(f143,plain,(
% 0.20/0.53    ( ! [X6,X5] : (v1_relat_1(k1_xboole_0) | ~v1_relat_1(X5) | ~r1_xboole_0(X6,k1_relat_1(X5)) | ~v1_relat_1(X5)) )),
% 0.20/0.53    inference(superposition,[],[f47,f48])).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,axiom,(
% 0.20/0.53    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.20/0.53  fof(f135,plain,(
% 0.20/0.53    ~spl2_3 | ~spl2_7),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f130])).
% 0.20/0.53  fof(f130,plain,(
% 0.20/0.53    $false | (~spl2_3 | ~spl2_7)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f70,f51,f101])).
% 0.20/0.53  fof(f101,plain,(
% 0.20/0.53    ( ! [X2,X3] : (~r1_xboole_0(X3,k1_relat_1(X2)) | ~v1_relat_1(X2)) ) | ~spl2_7),
% 0.20/0.53    inference(avatar_component_clause,[],[f100])).
% 0.20/0.53  fof(f82,plain,(
% 0.20/0.53    ~spl2_4 | spl2_1 | ~spl2_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f77,f68,f58,f79])).
% 0.20/0.53  % (8658)Refutation not found, incomplete strategy% (8658)------------------------------
% 0.20/0.53  % (8658)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (8658)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (8658)Memory used [KB]: 10746
% 0.20/0.53  % (8658)Time elapsed: 0.091 s
% 0.20/0.53  % (8658)------------------------------
% 0.20/0.53  % (8658)------------------------------
% 0.20/0.53  fof(f77,plain,(
% 0.20/0.53    ~r1_tarski(k9_relat_1(sK1,k1_tarski(sK0)),k1_tarski(k1_funct_1(sK1,sK0))) | (spl2_1 | ~spl2_3)),
% 0.20/0.53    inference(subsumption_resolution,[],[f76,f70])).
% 0.20/0.53  fof(f76,plain,(
% 0.20/0.53    ~r1_tarski(k9_relat_1(sK1,k1_tarski(sK0)),k1_tarski(k1_funct_1(sK1,sK0))) | ~v1_relat_1(sK1) | spl2_1),
% 0.20/0.53    inference(superposition,[],[f60,f46])).
% 0.20/0.53  fof(f71,plain,(
% 0.20/0.53    spl2_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f36,f68])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    v1_relat_1(sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & v1_funct_1(X1) & v1_relat_1(X1)) => (~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.53    inference(flattening,[],[f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.20/0.53    inference(ennf_transformation,[],[f19])).
% 0.20/0.53  fof(f19,negated_conjecture,(
% 0.20/0.53    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))))),
% 0.20/0.53    inference(negated_conjecture,[],[f18])).
% 0.20/0.53  fof(f18,conjecture,(
% 0.20/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_funct_1)).
% 0.20/0.53  fof(f66,plain,(
% 0.20/0.53    spl2_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f37,f63])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    v1_funct_1(sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f33])).
% 0.20/0.53  fof(f61,plain,(
% 0.20/0.53    ~spl2_1),
% 0.20/0.53    inference(avatar_split_clause,[],[f38,f58])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))),
% 0.20/0.53    inference(cnf_transformation,[],[f33])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (8669)------------------------------
% 0.20/0.53  % (8669)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (8669)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (8669)Memory used [KB]: 6396
% 0.20/0.53  % (8669)Time elapsed: 0.119 s
% 0.20/0.53  % (8669)------------------------------
% 0.20/0.53  % (8669)------------------------------
% 0.20/0.53  % (8655)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.53  % (8657)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.54  % (8647)Success in time 0.175 s
%------------------------------------------------------------------------------
