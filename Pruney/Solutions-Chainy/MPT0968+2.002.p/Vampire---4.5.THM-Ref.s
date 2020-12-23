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
% DateTime   : Thu Dec  3 13:00:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 212 expanded)
%              Number of leaves         :   17 (  51 expanded)
%              Depth                    :   16
%              Number of atoms          :  231 ( 740 expanded)
%              Number of equality atoms :   84 ( 239 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f593,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f120,f269,f276,f301,f347,f592])).

fof(f592,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f574])).

fof(f574,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f452,f486])).

fof(f486,plain,
    ( r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,k1_xboole_0))
    | ~ spl7_2
    | ~ spl7_7 ),
    inference(forward_demodulation,[],[f485,f44])).

fof(f44,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f485,plain,
    ( r2_hidden(k1_xboole_0,k1_funct_2(k1_relat_1(k1_xboole_0),k1_xboole_0))
    | ~ spl7_2
    | ~ spl7_7 ),
    inference(forward_demodulation,[],[f484,f257])).

fof(f257,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f255])).

fof(f255,plain,
    ( spl7_7
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f484,plain,
    ( r2_hidden(sK2,k1_funct_2(k1_relat_1(sK2),k1_xboole_0))
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f172,f118])).

fof(f118,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f172,plain,(
    r2_hidden(sK2,k1_funct_2(k1_relat_1(sK2),sK1)) ),
    inference(global_subsumption,[],[f40,f125,f166])).

fof(f166,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | r2_hidden(sK2,k1_funct_2(k1_relat_1(sK2),sK1)) ),
    inference(resolution,[],[f161,f95])).

fof(f95,plain,(
    ! [X4,X1] :
      ( ~ v1_relat_1(X4)
      | ~ v1_funct_1(X4)
      | ~ r1_tarski(k2_relat_1(X4),X1)
      | r2_hidden(X4,k1_funct_2(k1_relat_1(X4),X1)) ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X4,X2,X1] :
      ( ~ v1_relat_1(X4)
      | ~ v1_funct_1(X4)
      | ~ r1_tarski(k2_relat_1(X4),X1)
      | r2_hidden(X4,X2)
      | k1_funct_2(k1_relat_1(X4),X1) != X2 ) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_relat_1(X4)
      | ~ v1_funct_1(X4)
      | k1_relat_1(X4) != X0
      | ~ r1_tarski(k2_relat_1(X4),X1)
      | r2_hidden(X4,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X4)
      | ~ v1_funct_1(X4)
      | X3 != X4
      | k1_relat_1(X4) != X0
      | ~ r1_tarski(k2_relat_1(X4),X1)
      | r2_hidden(X3,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( k1_funct_2(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r1_tarski(k2_relat_1(X4),X1)
              & k1_relat_1(X4) = X0
              & X3 = X4
              & v1_funct_1(X4)
              & v1_relat_1(X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_funct_2)).

fof(f161,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(resolution,[],[f160,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f160,plain,(
    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    inference(global_subsumption,[],[f42,f159])).

fof(f159,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f122,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f122,plain,(
    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f42,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X2,k1_funct_2(X0,X1))
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X2,k1_funct_2(X0,X1))
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => r2_hidden(X2,k1_funct_2(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => r2_hidden(X2,k1_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_funct_2)).

fof(f125,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f42,f64])).

% (22118)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f40,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f452,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,k1_xboole_0))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_7 ),
    inference(forward_demodulation,[],[f311,f257])).

fof(f311,plain,
    ( ~ r2_hidden(sK2,k1_funct_2(k1_xboole_0,k1_xboole_0))
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f310,f115])).

fof(f115,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl7_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f310,plain,
    ( ~ r2_hidden(sK2,k1_funct_2(sK0,k1_xboole_0))
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f43,f118])).

fof(f43,plain,(
    ~ r2_hidden(sK2,k1_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f347,plain,
    ( ~ spl7_2
    | spl7_9 ),
    inference(avatar_contradiction_clause,[],[f343])).

fof(f343,plain,
    ( $false
    | ~ spl7_2
    | spl7_9 ),
    inference(subsumption_resolution,[],[f268,f342])).

fof(f342,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f334,f46])).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f334,plain,
    ( k2_relat_1(sK2) = k3_xboole_0(k2_relat_1(sK2),k1_xboole_0)
    | ~ spl7_2 ),
    inference(resolution,[],[f308,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f308,plain,
    ( r1_tarski(k2_relat_1(sK2),k1_xboole_0)
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f161,f118])).

fof(f268,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | spl7_9 ),
    inference(avatar_component_clause,[],[f266])).

fof(f266,plain,
    ( spl7_9
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f301,plain,(
    ~ spl7_10 ),
    inference(avatar_contradiction_clause,[],[f289])).

fof(f289,plain,
    ( $false
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f43,f282])).

fof(f282,plain,
    ( r2_hidden(sK2,k1_funct_2(sK0,sK1))
    | ~ spl7_10 ),
    inference(backward_demodulation,[],[f172,f277])).

fof(f277,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl7_10 ),
    inference(backward_demodulation,[],[f123,f275])).

fof(f275,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl7_10
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f123,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f42,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f276,plain,
    ( spl7_10
    | spl7_2 ),
    inference(avatar_split_clause,[],[f105,f117,f273])).

fof(f105,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(global_subsumption,[],[f42,f104])).

fof(f104,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f41,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f41,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f269,plain,
    ( spl7_7
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f133,f266,f255])).

fof(f133,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f125,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f120,plain,
    ( spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f39,f117,f113])).

fof(f39,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:27:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (22128)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.48  % (22136)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.50  % (22125)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.50  % (22136)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (22124)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f593,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f120,f269,f276,f301,f347,f592])).
% 0.21/0.51  fof(f592,plain,(
% 0.21/0.51    ~spl7_1 | ~spl7_2 | ~spl7_7),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f574])).
% 0.21/0.51  fof(f574,plain,(
% 0.21/0.51    $false | (~spl7_1 | ~spl7_2 | ~spl7_7)),
% 0.21/0.51    inference(subsumption_resolution,[],[f452,f486])).
% 0.21/0.51  fof(f486,plain,(
% 0.21/0.51    r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,k1_xboole_0)) | (~spl7_2 | ~spl7_7)),
% 0.21/0.51    inference(forward_demodulation,[],[f485,f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.51  fof(f485,plain,(
% 0.21/0.51    r2_hidden(k1_xboole_0,k1_funct_2(k1_relat_1(k1_xboole_0),k1_xboole_0)) | (~spl7_2 | ~spl7_7)),
% 0.21/0.51    inference(forward_demodulation,[],[f484,f257])).
% 0.21/0.51  fof(f257,plain,(
% 0.21/0.51    k1_xboole_0 = sK2 | ~spl7_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f255])).
% 0.21/0.51  fof(f255,plain,(
% 0.21/0.51    spl7_7 <=> k1_xboole_0 = sK2),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.51  fof(f484,plain,(
% 0.21/0.51    r2_hidden(sK2,k1_funct_2(k1_relat_1(sK2),k1_xboole_0)) | ~spl7_2),
% 0.21/0.51    inference(forward_demodulation,[],[f172,f118])).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    k1_xboole_0 = sK1 | ~spl7_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f117])).
% 0.21/0.51  fof(f117,plain,(
% 0.21/0.51    spl7_2 <=> k1_xboole_0 = sK1),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.51  fof(f172,plain,(
% 0.21/0.51    r2_hidden(sK2,k1_funct_2(k1_relat_1(sK2),sK1))),
% 0.21/0.51    inference(global_subsumption,[],[f40,f125,f166])).
% 0.21/0.51  fof(f166,plain,(
% 0.21/0.51    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | r2_hidden(sK2,k1_funct_2(k1_relat_1(sK2),sK1))),
% 0.21/0.51    inference(resolution,[],[f161,f95])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    ( ! [X4,X1] : (~v1_relat_1(X4) | ~v1_funct_1(X4) | ~r1_tarski(k2_relat_1(X4),X1) | r2_hidden(X4,k1_funct_2(k1_relat_1(X4),X1))) )),
% 0.21/0.51    inference(equality_resolution,[],[f94])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    ( ! [X4,X2,X1] : (~v1_relat_1(X4) | ~v1_funct_1(X4) | ~r1_tarski(k2_relat_1(X4),X1) | r2_hidden(X4,X2) | k1_funct_2(k1_relat_1(X4),X1) != X2) )),
% 0.21/0.51    inference(equality_resolution,[],[f93])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X1] : (~v1_relat_1(X4) | ~v1_funct_1(X4) | k1_relat_1(X4) != X0 | ~r1_tarski(k2_relat_1(X4),X1) | r2_hidden(X4,X2) | k1_funct_2(X0,X1) != X2) )),
% 0.21/0.51    inference(equality_resolution,[],[f85])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X4) | ~v1_funct_1(X4) | X3 != X4 | k1_relat_1(X4) != X0 | ~r1_tarski(k2_relat_1(X4),X1) | r2_hidden(X3,X2) | k1_funct_2(X0,X1) != X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_funct_2)).
% 0.21/0.51  fof(f161,plain,(
% 0.21/0.51    r1_tarski(k2_relat_1(sK2),sK1)),
% 0.21/0.51    inference(resolution,[],[f160,f62])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.51  fof(f160,plain,(
% 0.21/0.51    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))),
% 0.21/0.51    inference(global_subsumption,[],[f42,f159])).
% 0.21/0.51  fof(f159,plain,(
% 0.21/0.51    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.51    inference(superposition,[],[f122,f65])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))),
% 0.21/0.51    inference(resolution,[],[f42,f67])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (~r2_hidden(X2,k1_funct_2(X0,X1)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.51    inference(flattening,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ? [X0,X1,X2] : ((~r2_hidden(X2,k1_funct_2(X0,X1)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => r2_hidden(X2,k1_funct_2(X0,X1))))),
% 0.21/0.51    inference(negated_conjecture,[],[f20])).
% 0.21/0.51  fof(f20,conjecture,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => r2_hidden(X2,k1_funct_2(X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_funct_2)).
% 0.21/0.51  fof(f125,plain,(
% 0.21/0.51    v1_relat_1(sK2)),
% 0.21/0.51    inference(resolution,[],[f42,f64])).
% 0.21/0.51  % (22118)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    v1_funct_1(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f452,plain,(
% 0.21/0.51    ~r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,k1_xboole_0)) | (~spl7_1 | ~spl7_2 | ~spl7_7)),
% 0.21/0.51    inference(forward_demodulation,[],[f311,f257])).
% 0.21/0.51  fof(f311,plain,(
% 0.21/0.51    ~r2_hidden(sK2,k1_funct_2(k1_xboole_0,k1_xboole_0)) | (~spl7_1 | ~spl7_2)),
% 0.21/0.51    inference(forward_demodulation,[],[f310,f115])).
% 0.21/0.51  fof(f115,plain,(
% 0.21/0.51    k1_xboole_0 = sK0 | ~spl7_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f113])).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    spl7_1 <=> k1_xboole_0 = sK0),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.51  fof(f310,plain,(
% 0.21/0.51    ~r2_hidden(sK2,k1_funct_2(sK0,k1_xboole_0)) | ~spl7_2),
% 0.21/0.51    inference(forward_demodulation,[],[f43,f118])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ~r2_hidden(sK2,k1_funct_2(sK0,sK1))),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f347,plain,(
% 0.21/0.51    ~spl7_2 | spl7_9),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f343])).
% 0.21/0.51  fof(f343,plain,(
% 0.21/0.51    $false | (~spl7_2 | spl7_9)),
% 0.21/0.51    inference(subsumption_resolution,[],[f268,f342])).
% 0.21/0.51  fof(f342,plain,(
% 0.21/0.51    k1_xboole_0 = k2_relat_1(sK2) | ~spl7_2),
% 0.21/0.51    inference(forward_demodulation,[],[f334,f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.51  fof(f334,plain,(
% 0.21/0.51    k2_relat_1(sK2) = k3_xboole_0(k2_relat_1(sK2),k1_xboole_0) | ~spl7_2),
% 0.21/0.51    inference(resolution,[],[f308,f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.51  fof(f308,plain,(
% 0.21/0.51    r1_tarski(k2_relat_1(sK2),k1_xboole_0) | ~spl7_2),
% 0.21/0.51    inference(backward_demodulation,[],[f161,f118])).
% 0.21/0.51  fof(f268,plain,(
% 0.21/0.51    k1_xboole_0 != k2_relat_1(sK2) | spl7_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f266])).
% 0.21/0.51  fof(f266,plain,(
% 0.21/0.51    spl7_9 <=> k1_xboole_0 = k2_relat_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.21/0.51  fof(f301,plain,(
% 0.21/0.51    ~spl7_10),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f289])).
% 0.21/0.51  fof(f289,plain,(
% 0.21/0.51    $false | ~spl7_10),
% 0.21/0.51    inference(subsumption_resolution,[],[f43,f282])).
% 0.21/0.51  fof(f282,plain,(
% 0.21/0.51    r2_hidden(sK2,k1_funct_2(sK0,sK1)) | ~spl7_10),
% 0.21/0.51    inference(backward_demodulation,[],[f172,f277])).
% 0.21/0.51  fof(f277,plain,(
% 0.21/0.51    sK0 = k1_relat_1(sK2) | ~spl7_10),
% 0.21/0.51    inference(backward_demodulation,[],[f123,f275])).
% 0.21/0.51  fof(f275,plain,(
% 0.21/0.51    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl7_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f273])).
% 0.21/0.51  fof(f273,plain,(
% 0.21/0.51    spl7_10 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.21/0.51  fof(f123,plain,(
% 0.21/0.51    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.21/0.51    inference(resolution,[],[f42,f66])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.51  fof(f276,plain,(
% 0.21/0.51    spl7_10 | spl7_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f105,f117,f273])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.51    inference(global_subsumption,[],[f42,f104])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.51    inference(resolution,[],[f41,f73])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(flattening,[],[f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f269,plain,(
% 0.21/0.51    spl7_7 | ~spl7_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f133,f266,f255])).
% 0.21/0.51  fof(f133,plain,(
% 0.21/0.51    k1_xboole_0 != k2_relat_1(sK2) | k1_xboole_0 = sK2),
% 0.21/0.51    inference(resolution,[],[f125,f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.51  fof(f120,plain,(
% 0.21/0.51    spl7_1 | ~spl7_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f39,f117,f113])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (22136)------------------------------
% 0.21/0.51  % (22136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (22136)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (22136)Memory used [KB]: 10874
% 0.21/0.51  % (22136)Time elapsed: 0.093 s
% 0.21/0.51  % (22136)------------------------------
% 0.21/0.51  % (22136)------------------------------
% 0.21/0.52  % (22115)Success in time 0.158 s
%------------------------------------------------------------------------------
