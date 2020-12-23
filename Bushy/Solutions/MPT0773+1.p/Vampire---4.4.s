%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : wellord1__t22_wellord1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:11 EDT 2019

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 122 expanded)
%              Number of leaves         :   10 (  33 expanded)
%              Depth                    :   20
%              Number of atoms          :  181 ( 349 expanded)
%              Number of equality atoms :    6 (   7 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5888,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f79,f86,f5887])).

fof(f5887,plain,
    ( ~ spl5_0
    | ~ spl5_2
    | spl5_5 ),
    inference(avatar_contradiction_clause,[],[f5884])).

fof(f5884,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f85,f5883])).

fof(f5883,plain,
    ( ! [X0] : v1_relat_2(k2_wellord1(sK1,X0))
    | ~ spl5_0
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f5882,f82])).

fof(f82,plain,
    ( ! [X1] : v1_relat_1(k2_wellord1(sK1,X1))
    | ~ spl5_0 ),
    inference(resolution,[],[f74,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k2_wellord1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t22_wellord1.p',dt_k2_wellord1)).

fof(f74,plain,
    ( v1_relat_1(sK1)
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl5_0
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f5882,plain,
    ( ! [X0] :
        ( v1_relat_2(k2_wellord1(sK1,X0))
        | ~ v1_relat_1(k2_wellord1(sK1,X0)) )
    | ~ spl5_0
    | ~ spl5_2 ),
    inference(duplicate_literal_removal,[],[f5858])).

fof(f5858,plain,
    ( ! [X0] :
        ( v1_relat_2(k2_wellord1(sK1,X0))
        | ~ v1_relat_1(k2_wellord1(sK1,X0))
        | v1_relat_2(k2_wellord1(sK1,X0)) )
    | ~ spl5_0
    | ~ spl5_2 ),
    inference(resolution,[],[f5790,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK2(X0),sK2(X0)),X0)
      | ~ v1_relat_1(X0)
      | v1_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(k4_tarski(X1,X1),X0)
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(X1,k3_relat_1(X0))
           => r2_hidden(k4_tarski(X1,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t22_wellord1.p',l1_wellord1)).

fof(f5790,plain,
    ( ! [X2] :
        ( r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,X2)),sK2(k2_wellord1(sK1,X2))),k2_wellord1(sK1,X2))
        | v1_relat_2(k2_wellord1(sK1,X2)) )
    | ~ spl5_0
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f5789,f81])).

fof(f81,plain,
    ( ! [X0] : k2_wellord1(sK1,X0) = k3_xboole_0(sK1,k2_zfmisc_1(X0,X0))
    | ~ spl5_0 ),
    inference(resolution,[],[f74,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t22_wellord1.p',d6_wellord1)).

fof(f5789,plain,
    ( ! [X2] :
        ( v1_relat_2(k2_wellord1(sK1,X2))
        | r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,X2)),sK2(k2_wellord1(sK1,X2))),k3_xboole_0(sK1,k2_zfmisc_1(X2,X2))) )
    | ~ spl5_0
    | ~ spl5_2 ),
    inference(resolution,[],[f2533,f71])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( ~ sP4(X3,X1,X0)
      | r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP4(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t22_wellord1.p',d4_xboole_0)).

fof(f2533,plain,
    ( ! [X7] :
        ( sP4(k4_tarski(sK2(k2_wellord1(sK1,X7)),sK2(k2_wellord1(sK1,X7))),k2_zfmisc_1(X7,X7),sK1)
        | v1_relat_2(k2_wellord1(sK1,X7)) )
    | ~ spl5_0
    | ~ spl5_2 ),
    inference(duplicate_literal_removal,[],[f2528])).

fof(f2528,plain,
    ( ! [X7] :
        ( v1_relat_2(k2_wellord1(sK1,X7))
        | sP4(k4_tarski(sK2(k2_wellord1(sK1,X7)),sK2(k2_wellord1(sK1,X7))),k2_zfmisc_1(X7,X7),sK1)
        | v1_relat_2(k2_wellord1(sK1,X7))
        | v1_relat_2(k2_wellord1(sK1,X7)) )
    | ~ spl5_0
    | ~ spl5_2 ),
    inference(resolution,[],[f248,f301])).

fof(f301,plain,
    ( ! [X8,X9] :
        ( r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,X8)),sK2(k2_wellord1(sK1,X9))),k2_zfmisc_1(X8,X9))
        | v1_relat_2(k2_wellord1(sK1,X8))
        | v1_relat_2(k2_wellord1(sK1,X9)) )
    | ~ spl5_0 ),
    inference(resolution,[],[f106,f105])).

fof(f105,plain,
    ( ! [X1] :
        ( r2_hidden(sK2(k2_wellord1(sK1,X1)),X1)
        | v1_relat_2(k2_wellord1(sK1,X1)) )
    | ~ spl5_0 ),
    inference(subsumption_resolution,[],[f99,f74])).

fof(f99,plain,
    ( ! [X1] :
        ( v1_relat_2(k2_wellord1(sK1,X1))
        | ~ v1_relat_1(sK1)
        | r2_hidden(sK2(k2_wellord1(sK1,X1)),X1) )
    | ~ spl5_0 ),
    inference(resolution,[],[f87,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
       => ( r2_hidden(X0,X1)
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t22_wellord1.p',t19_wellord1)).

fof(f87,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(k2_wellord1(sK1,X0)),k3_relat_1(k2_wellord1(sK1,X0)))
        | v1_relat_2(k2_wellord1(sK1,X0)) )
    | ~ spl5_0 ),
    inference(resolution,[],[f82,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK2(X0),k3_relat_1(X0))
      | v1_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f106,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X1,X2)
        | v1_relat_2(k2_wellord1(sK1,X0))
        | r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,X0)),X1),k2_zfmisc_1(X0,X2)) )
    | ~ spl5_0 ),
    inference(resolution,[],[f105,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X3)
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t22_wellord1.p',t106_zfmisc_1)).

fof(f248,plain,
    ( ! [X6,X7] :
        ( ~ r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,X6)),sK2(k2_wellord1(sK1,X6))),X7)
        | v1_relat_2(k2_wellord1(sK1,X6))
        | sP4(k4_tarski(sK2(k2_wellord1(sK1,X6)),sK2(k2_wellord1(sK1,X6))),X7,sK1) )
    | ~ spl5_0
    | ~ spl5_2 ),
    inference(resolution,[],[f127,f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | sP4(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f127,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,X0)),sK2(k2_wellord1(sK1,X0))),sK1)
        | v1_relat_2(k2_wellord1(sK1,X0)) )
    | ~ spl5_0
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f126,f78])).

fof(f78,plain,
    ( v1_relat_2(sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl5_2
  <=> v1_relat_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f126,plain,
    ( ! [X0] :
        ( v1_relat_2(k2_wellord1(sK1,X0))
        | r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,X0)),sK2(k2_wellord1(sK1,X0))),sK1)
        | ~ v1_relat_2(sK1) )
    | ~ spl5_0 ),
    inference(subsumption_resolution,[],[f122,f74])).

fof(f122,plain,
    ( ! [X0] :
        ( v1_relat_2(k2_wellord1(sK1,X0))
        | ~ v1_relat_1(sK1)
        | r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,X0)),sK2(k2_wellord1(sK1,X0))),sK1)
        | ~ v1_relat_2(sK1) )
    | ~ spl5_0 ),
    inference(resolution,[],[f104,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X1,X1),X0)
      | ~ v1_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f104,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(k2_wellord1(sK1,X0)),k3_relat_1(sK1))
        | v1_relat_2(k2_wellord1(sK1,X0)) )
    | ~ spl5_0 ),
    inference(subsumption_resolution,[],[f98,f74])).

fof(f98,plain,
    ( ! [X0] :
        ( v1_relat_2(k2_wellord1(sK1,X0))
        | ~ v1_relat_1(sK1)
        | r2_hidden(sK2(k2_wellord1(sK1,X0)),k3_relat_1(sK1)) )
    | ~ spl5_0 ),
    inference(resolution,[],[f87,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2)
      | r2_hidden(X0,k3_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f85,plain,
    ( ~ v1_relat_2(k2_wellord1(sK1,sK0))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl5_5
  <=> ~ v1_relat_2(k2_wellord1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f86,plain,(
    ~ spl5_5 ),
    inference(avatar_split_clause,[],[f47,f84])).

fof(f47,plain,(
    ~ v1_relat_2(k2_wellord1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ? [X0,X1] :
      ( ~ v1_relat_2(k2_wellord1(X1,X0))
      & v1_relat_2(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ? [X0,X1] :
      ( ~ v1_relat_2(k2_wellord1(X1,X0))
      & v1_relat_2(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( v1_relat_2(X1)
         => v1_relat_2(k2_wellord1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v1_relat_2(X1)
       => v1_relat_2(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t22_wellord1.p',t22_wellord1)).

fof(f79,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f46,f77])).

fof(f46,plain,(
    v1_relat_2(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f75,plain,(
    spl5_0 ),
    inference(avatar_split_clause,[],[f45,f73])).

fof(f45,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
