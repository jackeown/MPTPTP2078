%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0555+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:37 EST 2020

% Result     : Theorem 18.58s
% Output     : Refutation 18.58s
% Verified   : 
% Statistics : Number of formulae       :   49 (  79 expanded)
%              Number of leaves         :    9 (  22 expanded)
%              Depth                    :   14
%              Number of atoms          :  140 ( 224 expanded)
%              Number of equality atoms :    5 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11589,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1986,f1990,f2228,f2298,f11568])).

fof(f11568,plain,
    ( ~ spl94_1
    | ~ spl94_2
    | ~ spl94_3
    | spl94_5 ),
    inference(avatar_contradiction_clause,[],[f11567])).

fof(f11567,plain,
    ( $false
    | ~ spl94_1
    | ~ spl94_2
    | ~ spl94_3
    | spl94_5 ),
    inference(subsumption_resolution,[],[f2297,f11566])).

fof(f11566,plain,
    ( ! [X39] : r1_tarski(k9_relat_1(sK1,X39),k9_relat_1(sK2,X39))
    | ~ spl94_1
    | ~ spl94_2
    | ~ spl94_3 ),
    inference(forward_demodulation,[],[f11565,f2115])).

fof(f2115,plain,
    ( ! [X11] : k9_relat_1(sK1,X11) = k2_relat_1(k7_relat_1(sK1,X11))
    | ~ spl94_2 ),
    inference(resolution,[],[f1989,f1215])).

fof(f1215,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f827])).

fof(f827,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f729])).

fof(f729,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f1989,plain,
    ( v1_relat_1(sK1)
    | ~ spl94_2 ),
    inference(avatar_component_clause,[],[f1988])).

fof(f1988,plain,
    ( spl94_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl94_2])])).

fof(f11565,plain,
    ( ! [X39] : r1_tarski(k2_relat_1(k7_relat_1(sK1,X39)),k9_relat_1(sK2,X39))
    | ~ spl94_1
    | ~ spl94_2
    | ~ spl94_3 ),
    inference(forward_demodulation,[],[f11564,f1998])).

fof(f1998,plain,
    ( ! [X11] : k9_relat_1(sK2,X11) = k2_relat_1(k7_relat_1(sK2,X11))
    | ~ spl94_1 ),
    inference(resolution,[],[f1985,f1215])).

fof(f1985,plain,
    ( v1_relat_1(sK2)
    | ~ spl94_1 ),
    inference(avatar_component_clause,[],[f1984])).

fof(f1984,plain,
    ( spl94_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl94_1])])).

fof(f11564,plain,
    ( ! [X39] : r1_tarski(k2_relat_1(k7_relat_1(sK1,X39)),k2_relat_1(k7_relat_1(sK2,X39)))
    | ~ spl94_1
    | ~ spl94_2
    | ~ spl94_3 ),
    inference(subsumption_resolution,[],[f11563,f2175])).

fof(f2175,plain,
    ( ! [X77] : v1_relat_1(k7_relat_1(sK1,X77))
    | ~ spl94_2 ),
    inference(resolution,[],[f1989,f1711])).

fof(f1711,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f1098])).

fof(f1098,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f658])).

fof(f658,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f11563,plain,
    ( ! [X39] :
        ( ~ v1_relat_1(k7_relat_1(sK1,X39))
        | r1_tarski(k2_relat_1(k7_relat_1(sK1,X39)),k2_relat_1(k7_relat_1(sK2,X39))) )
    | ~ spl94_1
    | ~ spl94_2
    | ~ spl94_3 ),
    inference(subsumption_resolution,[],[f11532,f2058])).

fof(f2058,plain,
    ( ! [X77] : v1_relat_1(k7_relat_1(sK2,X77))
    | ~ spl94_1 ),
    inference(resolution,[],[f1985,f1711])).

fof(f11532,plain,
    ( ! [X39] :
        ( ~ v1_relat_1(k7_relat_1(sK2,X39))
        | ~ v1_relat_1(k7_relat_1(sK1,X39))
        | r1_tarski(k2_relat_1(k7_relat_1(sK1,X39)),k2_relat_1(k7_relat_1(sK2,X39))) )
    | ~ spl94_1
    | ~ spl94_2
    | ~ spl94_3 ),
    inference(resolution,[],[f2284,f1417])).

fof(f1417,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f923])).

fof(f923,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f922])).

fof(f922,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f749])).

fof(f749,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f2284,plain,
    ( ! [X32] : r1_tarski(k7_relat_1(sK1,X32),k7_relat_1(sK2,X32))
    | ~ spl94_1
    | ~ spl94_2
    | ~ spl94_3 ),
    inference(subsumption_resolution,[],[f2283,f1989])).

fof(f2283,plain,
    ( ! [X32] :
        ( ~ v1_relat_1(sK1)
        | r1_tarski(k7_relat_1(sK1,X32),k7_relat_1(sK2,X32)) )
    | ~ spl94_1
    | ~ spl94_3 ),
    inference(subsumption_resolution,[],[f2265,f1985])).

fof(f2265,plain,
    ( ! [X32] :
        ( ~ v1_relat_1(sK2)
        | ~ v1_relat_1(sK1)
        | r1_tarski(k7_relat_1(sK1,X32),k7_relat_1(sK2,X32)) )
    | ~ spl94_3 ),
    inference(resolution,[],[f2227,f1705])).

fof(f1705,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) ) ),
    inference(cnf_transformation,[],[f1092])).

fof(f1092,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1091])).

fof(f1091,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f689])).

fof(f689,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).

fof(f2227,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl94_3 ),
    inference(avatar_component_clause,[],[f2226])).

fof(f2226,plain,
    ( spl94_3
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl94_3])])).

fof(f2297,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0))
    | spl94_5 ),
    inference(avatar_component_clause,[],[f2296])).

fof(f2296,plain,
    ( spl94_5
  <=> r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl94_5])])).

fof(f2298,plain,(
    ~ spl94_5 ),
    inference(avatar_split_clause,[],[f1200,f2296])).

fof(f1200,plain,(
    ~ r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f815])).

fof(f815,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
          & r1_tarski(X1,X2)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f814])).

fof(f814,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
          & r1_tarski(X1,X2)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f740])).

fof(f740,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_tarski(X1,X2)
             => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) ) ) ) ),
    inference(negated_conjecture,[],[f739])).

fof(f739,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_relat_1)).

fof(f2228,plain,(
    spl94_3 ),
    inference(avatar_split_clause,[],[f1199,f2226])).

fof(f1199,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f815])).

fof(f1990,plain,(
    spl94_2 ),
    inference(avatar_split_clause,[],[f1201,f1988])).

fof(f1201,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f815])).

fof(f1986,plain,(
    spl94_1 ),
    inference(avatar_split_clause,[],[f1198,f1984])).

fof(f1198,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f815])).
%------------------------------------------------------------------------------
