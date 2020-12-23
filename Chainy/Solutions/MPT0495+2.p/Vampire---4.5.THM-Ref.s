%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0495+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   40 (  63 expanded)
%              Number of leaves         :   10 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :  109 ( 175 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1093,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f854,f858,f862,f1072,f1087])).

fof(f1087,plain,
    ( ~ spl9_12
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f1086,f860,f856,f852,f1062])).

% (31307)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=2.0:amm=sco:anc=none:gs=on:gsem=off:lma=on:lwlo=on:nm=4:nwc=10:stl=30:sd=3:ss=axioms:sos=all:sac=on_49 on theBenchmark
fof(f1062,plain,
    ( spl9_12
  <=> v1_relat_1(k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f852,plain,
    ( spl9_1
  <=> r1_tarski(k5_relat_1(sK1,k7_relat_1(sK2,sK0)),k5_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f856,plain,
    ( spl9_2
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f860,plain,
    ( spl9_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f1086,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f1085,f857])).

fof(f857,plain,
    ( v1_relat_1(sK2)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f856])).

fof(f1085,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f1084,f861])).

fof(f861,plain,
    ( v1_relat_1(sK1)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f860])).

fof(f1084,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f1073,f897])).

fof(f897,plain,
    ( ! [X10] : r1_tarski(k7_relat_1(sK2,X10),sK2)
    | ~ spl9_2 ),
    inference(resolution,[],[f832,f857])).

fof(f832,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    inference(cnf_transformation,[],[f770])).

fof(f770,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f732])).

fof(f732,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(f1073,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,sK0),sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | spl9_1 ),
    inference(resolution,[],[f815,f853])).

fof(f853,plain,
    ( ~ r1_tarski(k5_relat_1(sK1,k7_relat_1(sK2,sK0)),k5_relat_1(sK1,sK2))
    | spl9_1 ),
    inference(avatar_component_clause,[],[f852])).

fof(f815,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f755])).

fof(f755,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f754])).

fof(f754,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f702])).

fof(f702,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).

fof(f1072,plain,
    ( ~ spl9_2
    | spl9_12 ),
    inference(avatar_contradiction_clause,[],[f1071])).

fof(f1071,plain,
    ( $false
    | ~ spl9_2
    | spl9_12 ),
    inference(subsumption_resolution,[],[f1069,f857])).

fof(f1069,plain,
    ( ~ v1_relat_1(sK2)
    | spl9_12 ),
    inference(resolution,[],[f1063,f833])).

fof(f833,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f771])).

fof(f771,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f656])).

fof(f656,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f1063,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | spl9_12 ),
    inference(avatar_component_clause,[],[f1062])).

fof(f862,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f795,f860])).

fof(f795,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f779])).

fof(f779,plain,
    ( ~ r1_tarski(k5_relat_1(sK1,k7_relat_1(sK2,sK0)),k5_relat_1(sK1,sK2))
    & v1_relat_1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f740,f778,f777])).

fof(f777,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k5_relat_1(X1,k7_relat_1(X2,X0)),k5_relat_1(X1,X2))
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(sK1,k7_relat_1(X2,sK0)),k5_relat_1(sK1,X2))
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f778,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k5_relat_1(sK1,k7_relat_1(X2,sK0)),k5_relat_1(sK1,X2))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k5_relat_1(sK1,k7_relat_1(sK2,sK0)),k5_relat_1(sK1,sK2))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f740,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(X1,k7_relat_1(X2,X0)),k5_relat_1(X1,X2))
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f738])).

fof(f738,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => r1_tarski(k5_relat_1(X1,k7_relat_1(X2,X0)),k5_relat_1(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f737])).

fof(f737,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k5_relat_1(X1,k7_relat_1(X2,X0)),k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_relat_1)).

fof(f858,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f796,f856])).

fof(f796,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f779])).

fof(f854,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f797,f852])).

fof(f797,plain,(
    ~ r1_tarski(k5_relat_1(sK1,k7_relat_1(sK2,sK0)),k5_relat_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f779])).
%------------------------------------------------------------------------------
