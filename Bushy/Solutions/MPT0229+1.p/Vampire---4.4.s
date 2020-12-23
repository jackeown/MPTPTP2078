%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t24_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:04 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   18 (  23 expanded)
%              Number of leaves         :    4 (   7 expanded)
%              Depth                    :    6
%              Number of atoms          :   32 (  42 expanded)
%              Number of equality atoms :   10 (  14 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f34,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f23,f30,f33])).

fof(f33,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f32])).

fof(f32,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f31,f22])).

fof(f22,plain,
    ( sK0 != sK1
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f21])).

fof(f21,plain,
    ( spl2_1
  <=> sK0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f31,plain,
    ( sK0 = sK1
    | ~ spl2_2 ),
    inference(resolution,[],[f16,f29])).

fof(f29,plain,
    ( r1_tarski(k1_tarski(sK0),k1_tarski(sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl2_2
  <=> r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t24_zfmisc_1.p',t6_zfmisc_1)).

fof(f30,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f14,f28])).

fof(f14,plain,(
    r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t24_zfmisc_1.p',t24_zfmisc_1)).

fof(f23,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f15,f21])).

fof(f15,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
