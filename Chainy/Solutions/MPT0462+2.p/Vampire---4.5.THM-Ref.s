%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0462+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:31 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 125 expanded)
%              Number of leaves         :   15 (  53 expanded)
%              Depth                    :   16
%              Number of atoms          :  259 ( 751 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f843,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f763,f767,f771,f775,f779,f783,f787,f842])).

fof(f842,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7 ),
    inference(avatar_contradiction_clause,[],[f841])).

fof(f841,plain,
    ( $false
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f840,f786])).

fof(f786,plain,
    ( v1_relat_1(sK0)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f785])).

fof(f785,plain,
    ( spl8_7
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f840,plain,
    ( ~ v1_relat_1(sK0)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f839,f782])).

fof(f782,plain,
    ( v1_relat_1(sK1)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f781])).

fof(f781,plain,
    ( spl8_6
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f839,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f838,f770])).

fof(f770,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f769])).

fof(f769,plain,
    ( spl8_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f838,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f837,f774])).

fof(f774,plain,
    ( v1_relat_1(sK3)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f773])).

fof(f773,plain,
    ( spl8_4
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f837,plain,
    ( ~ v1_relat_1(sK3)
    | ~ r1_tarski(sK0,sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_5
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f836,f766])).

fof(f766,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f765])).

fof(f765,plain,
    ( spl8_2
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f836,plain,
    ( ~ r1_tarski(sK2,sK3)
    | ~ v1_relat_1(sK3)
    | ~ r1_tarski(sK0,sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | spl8_1
    | ~ spl8_5
    | ~ spl8_7 ),
    inference(duplicate_literal_removal,[],[f834])).

fof(f834,plain,
    ( ~ r1_tarski(sK2,sK3)
    | ~ v1_relat_1(sK3)
    | ~ r1_tarski(sK0,sK1)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | spl8_1
    | ~ spl8_5
    | ~ spl8_7 ),
    inference(resolution,[],[f831,f742])).

fof(f742,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f701])).

fof(f701,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f700])).

fof(f700,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f688])).

fof(f688,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relat_1)).

fof(f831,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k5_relat_1(sK0,X0),k5_relat_1(sK1,sK3))
        | ~ r1_tarski(sK2,X0)
        | ~ v1_relat_1(X0) )
    | spl8_1
    | ~ spl8_5
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f830,f778])).

fof(f778,plain,
    ( v1_relat_1(sK2)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f777])).

fof(f777,plain,
    ( spl8_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f830,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k5_relat_1(sK0,X0),k5_relat_1(sK1,sK3))
        | ~ r1_tarski(sK2,X0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(sK2) )
    | spl8_1
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f826,f786])).

fof(f826,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k5_relat_1(sK0,X0),k5_relat_1(sK1,sK3))
        | ~ r1_tarski(sK2,X0)
        | ~ v1_relat_1(sK0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(sK2) )
    | spl8_1 ),
    inference(resolution,[],[f791,f741])).

fof(f741,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f699])).

fof(f699,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f698])).

fof(f698,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f687])).

fof(f687,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relat_1)).

fof(f791,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k5_relat_1(sK0,sK2),X0)
        | ~ r1_tarski(X0,k5_relat_1(sK1,sK3)) )
    | spl8_1 ),
    inference(resolution,[],[f747,f762])).

fof(f762,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f761])).

fof(f761,plain,
    ( spl8_1
  <=> r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f747,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f709])).

fof(f709,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f708])).

fof(f708,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f77])).

fof(f77,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f787,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f727,f785])).

fof(f727,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f718])).

fof(f718,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3))
    & r1_tarski(sK2,sK3)
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK3)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f694,f717,f716,f715,f714])).

fof(f714,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
                    & r1_tarski(X2,X3)
                    & r1_tarski(X0,X1)
                    & v1_relat_1(X3) )
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k5_relat_1(sK0,X2),k5_relat_1(X1,X3))
                  & r1_tarski(X2,X3)
                  & r1_tarski(sK0,X1)
                  & v1_relat_1(X3) )
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f715,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tarski(k5_relat_1(sK0,X2),k5_relat_1(X1,X3))
                & r1_tarski(X2,X3)
                & r1_tarski(sK0,X1)
                & v1_relat_1(X3) )
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k5_relat_1(sK0,X2),k5_relat_1(sK1,X3))
              & r1_tarski(X2,X3)
              & r1_tarski(sK0,sK1)
              & v1_relat_1(X3) )
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f716,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k5_relat_1(sK0,X2),k5_relat_1(sK1,X3))
            & r1_tarski(X2,X3)
            & r1_tarski(sK0,sK1)
            & v1_relat_1(X3) )
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,X3))
          & r1_tarski(sK2,X3)
          & r1_tarski(sK0,sK1)
          & v1_relat_1(X3) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f717,plain,
    ( ? [X3] :
        ( ~ r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,X3))
        & r1_tarski(sK2,X3)
        & r1_tarski(sK0,sK1)
        & v1_relat_1(X3) )
   => ( ~ r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3))
      & r1_tarski(sK2,sK3)
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f694,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
                  & r1_tarski(X2,X3)
                  & r1_tarski(X0,X1)
                  & v1_relat_1(X3) )
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f693])).

% (29733)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% (29737)ott+11_8:1_av=off:bs=on:bce=on:fde=none:gsp=input_only:gs=on:gsem=on:irw=on:lcm=predicate:nm=6:nwc=1.5:sd=2:ss=axioms:st=1.2:sos=theory:urr=on:updr=off_49 on theBenchmark
fof(f693,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
                  & r1_tarski(X2,X3)
                  & r1_tarski(X0,X1)
                  & v1_relat_1(X3) )
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f690])).

fof(f690,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => ! [X3] :
                    ( v1_relat_1(X3)
                   => ( ( r1_tarski(X2,X3)
                        & r1_tarski(X0,X1) )
                     => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f689])).

fof(f689,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ! [X3] :
                  ( v1_relat_1(X3)
                 => ( ( r1_tarski(X2,X3)
                      & r1_tarski(X0,X1) )
                   => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relat_1)).

fof(f783,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f728,f781])).

fof(f728,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f718])).

fof(f779,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f729,f777])).

fof(f729,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f718])).

fof(f775,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f730,f773])).

fof(f730,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f718])).

fof(f771,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f731,f769])).

fof(f731,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f718])).

fof(f767,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f732,f765])).

fof(f732,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f718])).

fof(f763,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f733,f761])).

fof(f733,plain,(
    ~ r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f718])).
%------------------------------------------------------------------------------
