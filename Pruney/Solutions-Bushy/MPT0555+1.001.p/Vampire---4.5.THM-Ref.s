%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0555+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   55 (  91 expanded)
%              Number of leaves         :    9 (  29 expanded)
%              Depth                    :   13
%              Number of atoms          :  151 ( 275 expanded)
%              Number of equality atoms :    4 (  12 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f146,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f34,f47,f53,f62,f138,f145])).

fof(f145,plain,
    ( ~ spl7_2
    | ~ spl7_5
    | spl7_8 ),
    inference(avatar_contradiction_clause,[],[f144])).

fof(f144,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_5
    | spl7_8 ),
    inference(subsumption_resolution,[],[f142,f61])).

fof(f61,plain,
    ( r2_hidden(sK6(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0)),k9_relat_1(sK1,sK0))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl7_5
  <=> r2_hidden(sK6(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0)),k9_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f142,plain,
    ( ~ r2_hidden(sK6(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0)),k9_relat_1(sK1,sK0))
    | ~ spl7_2
    | spl7_8 ),
    inference(resolution,[],[f137,f40])).

fof(f40,plain,
    ( ! [X2,X3] :
        ( sP4(X2,X3,sK1)
        | ~ r2_hidden(X2,k9_relat_1(sK1,X3)) )
    | ~ spl7_2 ),
    inference(resolution,[],[f33,f23])).

fof(f23,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | sP4(X3,X1,X0)
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | sP4(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).

fof(f33,plain,
    ( v1_relat_1(sK1)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl7_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f137,plain,
    ( ~ sP4(sK6(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0)),sK0,sK1)
    | spl7_8 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl7_8
  <=> sP4(sK6(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0)),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f138,plain,
    ( ~ spl7_8
    | ~ spl7_1
    | ~ spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f131,f50,f44,f26,f135])).

fof(f26,plain,
    ( spl7_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f44,plain,
    ( spl7_3
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f50,plain,
    ( spl7_4
  <=> r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f131,plain,
    ( ~ sP4(sK6(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0)),sK0,sK1)
    | ~ spl7_1
    | ~ spl7_3
    | spl7_4 ),
    inference(duplicate_literal_removal,[],[f130])).

fof(f130,plain,
    ( ~ sP4(sK6(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0)),sK0,sK1)
    | ~ sP4(sK6(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0)),sK0,sK1)
    | ~ spl7_1
    | ~ spl7_3
    | spl7_4 ),
    inference(resolution,[],[f122,f15])).

fof(f15,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK5(X0,X1,X3),X1)
      | ~ sP4(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f122,plain,
    ( ! [X4] :
        ( ~ r2_hidden(sK5(sK1,X4,sK6(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0))),sK0)
        | ~ sP4(sK6(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0)),X4,sK1) )
    | ~ spl7_1
    | ~ spl7_3
    | spl7_4 ),
    inference(resolution,[],[f78,f52])).

fof(f52,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0))
    | spl7_4 ),
    inference(avatar_component_clause,[],[f50])).

fof(f78,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X0,k9_relat_1(sK2,X1))
        | ~ r2_hidden(sK5(sK1,X2,sK6(X0,k9_relat_1(sK2,X1))),X1)
        | ~ sP4(sK6(X0,k9_relat_1(sK2,X1)),X2,sK1) )
    | ~ spl7_1
    | ~ spl7_3 ),
    inference(resolution,[],[f76,f14])).

fof(f14,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1,X3),X3),X0)
      | ~ sP4(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f76,plain,
    ( ! [X4,X5,X3] :
        ( ~ r2_hidden(k4_tarski(X3,sK6(X5,k9_relat_1(sK2,X4))),sK1)
        | r1_tarski(X5,k9_relat_1(sK2,X4))
        | ~ r2_hidden(X3,X4) )
    | ~ spl7_1
    | ~ spl7_3 ),
    inference(resolution,[],[f64,f48])).

fof(f48,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl7_3 ),
    inference(resolution,[],[f46,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f46,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f64,plain,
    ( ! [X4,X2,X3] :
        ( ~ r2_hidden(k4_tarski(X4,sK6(X2,k9_relat_1(sK2,X3))),sK2)
        | ~ r2_hidden(X4,X3)
        | r1_tarski(X2,k9_relat_1(sK2,X3)) )
    | ~ spl7_1 ),
    inference(resolution,[],[f56,f13])).

fof(f13,plain,(
    ! [X4,X0,X3,X1] :
      ( sP4(X3,X1,X0)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(k4_tarski(X4,X3),X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f56,plain,
    ( ! [X0,X1] :
        ( ~ sP4(sK6(X0,k9_relat_1(sK2,X1)),X1,sK2)
        | r1_tarski(X0,k9_relat_1(sK2,X1)) )
    | ~ spl7_1 ),
    inference(resolution,[],[f35,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f35,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,k9_relat_1(sK2,X1))
        | ~ sP4(X0,X1,sK2) )
    | ~ spl7_1 ),
    inference(resolution,[],[f28,f24])).

fof(f24,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ sP4(X3,X1,X0)
      | r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ sP4(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f28,plain,
    ( v1_relat_1(sK2)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f62,plain,
    ( spl7_5
    | spl7_4 ),
    inference(avatar_split_clause,[],[f55,f50,f59])).

fof(f55,plain,
    ( r2_hidden(sK6(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0)),k9_relat_1(sK1,sK0))
    | spl7_4 ),
    inference(resolution,[],[f52,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK6(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f53,plain,(
    ~ spl7_4 ),
    inference(avatar_split_clause,[],[f11,f50])).

fof(f11,plain,(
    ~ r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
          & r1_tarski(X1,X2)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
          & r1_tarski(X1,X2)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_tarski(X1,X2)
             => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_relat_1)).

fof(f47,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f10,f44])).

fof(f10,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f6])).

fof(f34,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f12,f31])).

fof(f12,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f29,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f9,f26])).

fof(f9,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f6])).

%------------------------------------------------------------------------------
