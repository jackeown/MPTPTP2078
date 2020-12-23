%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0491+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:33 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :   31 (  50 expanded)
%              Number of leaves         :    7 (  15 expanded)
%              Depth                    :    8
%              Number of atoms          :   71 ( 113 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3699,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3690,f3695,f3698])).

fof(f3698,plain,(
    spl157_2 ),
    inference(avatar_contradiction_clause,[],[f3697])).

fof(f3697,plain,
    ( $false
    | spl157_2 ),
    inference(subsumption_resolution,[],[f3696,f1714])).

fof(f1714,plain,(
    v1_relat_1(sK11) ),
    inference(cnf_transformation,[],[f1295])).

fof(f1295,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK11,sK10)),k1_relat_1(sK11))
    & v1_relat_1(sK11) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f751,f1294])).

fof(f1294,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK11,sK10)),k1_relat_1(sK11))
      & v1_relat_1(sK11) ) ),
    introduced(choice_axiom,[])).

fof(f751,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f734])).

fof(f734,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    inference(negated_conjecture,[],[f733])).

fof(f733,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).

fof(f3696,plain,
    ( ~ v1_relat_1(sK11)
    | spl157_2 ),
    inference(resolution,[],[f3689,f2002])).

fof(f2002,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f862])).

fof(f862,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f732])).

fof(f732,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(f3689,plain,
    ( ~ r1_tarski(k7_relat_1(sK11,sK10),sK11)
    | spl157_2 ),
    inference(avatar_component_clause,[],[f3687])).

fof(f3687,plain,
    ( spl157_2
  <=> r1_tarski(k7_relat_1(sK11,sK10),sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl157_2])])).

fof(f3695,plain,(
    spl157_1 ),
    inference(avatar_contradiction_clause,[],[f3694])).

fof(f3694,plain,
    ( $false
    | spl157_1 ),
    inference(subsumption_resolution,[],[f3692,f1714])).

fof(f3692,plain,
    ( ~ v1_relat_1(sK11)
    | spl157_1 ),
    inference(resolution,[],[f3685,f1999])).

fof(f1999,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f859])).

fof(f859,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f656])).

fof(f656,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f3685,plain,
    ( ~ v1_relat_1(k7_relat_1(sK11,sK10))
    | spl157_1 ),
    inference(avatar_component_clause,[],[f3683])).

fof(f3683,plain,
    ( spl157_1
  <=> v1_relat_1(k7_relat_1(sK11,sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl157_1])])).

fof(f3690,plain,
    ( ~ spl157_1
    | ~ spl157_2 ),
    inference(avatar_split_clause,[],[f3681,f3687,f3683])).

fof(f3681,plain,
    ( ~ r1_tarski(k7_relat_1(sK11,sK10),sK11)
    | ~ v1_relat_1(k7_relat_1(sK11,sK10)) ),
    inference(subsumption_resolution,[],[f3680,f1714])).

fof(f3680,plain,
    ( ~ r1_tarski(k7_relat_1(sK11,sK10),sK11)
    | ~ v1_relat_1(sK11)
    | ~ v1_relat_1(k7_relat_1(sK11,sK10)) ),
    inference(resolution,[],[f1715,f1822])).

fof(f1822,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f799])).

fof(f799,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f798])).

fof(f798,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f684])).

fof(f684,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f1715,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1(sK11,sK10)),k1_relat_1(sK11)) ),
    inference(cnf_transformation,[],[f1295])).
%------------------------------------------------------------------------------
