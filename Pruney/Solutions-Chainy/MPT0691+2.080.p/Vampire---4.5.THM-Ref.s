%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 154 expanded)
%              Number of leaves         :   25 (  70 expanded)
%              Depth                    :    7
%              Number of atoms          :  275 ( 444 expanded)
%              Number of equality atoms :   32 (  47 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f296,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f39,f44,f48,f52,f56,f60,f64,f68,f79,f85,f95,f106,f154,f168,f284,f291,f295])).

fof(f295,plain,
    ( spl2_1
    | ~ spl2_16
    | ~ spl2_51 ),
    inference(avatar_contradiction_clause,[],[f294])).

fof(f294,plain,
    ( $false
    | spl2_1
    | ~ spl2_16
    | ~ spl2_51 ),
    inference(subsumption_resolution,[],[f292,f33])).

fof(f33,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl2_1
  <=> r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f292,plain,
    ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    | ~ spl2_16
    | ~ spl2_51 ),
    inference(superposition,[],[f290,f105])).

fof(f105,plain,
    ( sK0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl2_16
  <=> sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f290,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k10_relat_1(sK1,k9_relat_1(sK1,X0)))
    | ~ spl2_51 ),
    inference(avatar_component_clause,[],[f289])).

fof(f289,plain,
    ( spl2_51
  <=> ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k10_relat_1(sK1,k9_relat_1(sK1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).

fof(f291,plain,
    ( spl2_51
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_50 ),
    inference(avatar_split_clause,[],[f287,f282,f54,f41,f289])).

fof(f41,plain,
    ( spl2_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f54,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( r1_tarski(k7_relat_1(X1,X0),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f282,plain,
    ( spl2_50
  <=> ! [X1,X0] :
        ( ~ r1_tarski(k7_relat_1(sK1,X0),X1)
        | ~ v1_relat_1(X1)
        | r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k10_relat_1(X1,k9_relat_1(sK1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).

fof(f287,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k10_relat_1(sK1,k9_relat_1(sK1,X0)))
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_50 ),
    inference(subsumption_resolution,[],[f286,f43])).

fof(f43,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f286,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK1)
        | r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k10_relat_1(sK1,k9_relat_1(sK1,X0))) )
    | ~ spl2_6
    | ~ spl2_50 ),
    inference(duplicate_literal_removal,[],[f285])).

fof(f285,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK1)
        | r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k10_relat_1(sK1,k9_relat_1(sK1,X0)))
        | ~ v1_relat_1(sK1) )
    | ~ spl2_6
    | ~ spl2_50 ),
    inference(resolution,[],[f283,f55])).

fof(f55,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k7_relat_1(X1,X0),X1)
        | ~ v1_relat_1(X1) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f54])).

fof(f283,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k7_relat_1(sK1,X0),X1)
        | ~ v1_relat_1(X1)
        | r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k10_relat_1(X1,k9_relat_1(sK1,X0))) )
    | ~ spl2_50 ),
    inference(avatar_component_clause,[],[f282])).

fof(f284,plain,
    ( spl2_50
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_28 ),
    inference(avatar_split_clause,[],[f280,f166,f50,f41,f282])).

fof(f50,plain,
    ( spl2_5
  <=> ! [X1,X0] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f166,plain,
    ( spl2_28
  <=> ! [X3,X2] :
        ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X2)),k10_relat_1(X3,k9_relat_1(sK1,X2)))
        | ~ r1_tarski(k7_relat_1(sK1,X2),X3)
        | ~ v1_relat_1(X3)
        | ~ v1_relat_1(k7_relat_1(sK1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f280,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k7_relat_1(sK1,X0),X1)
        | ~ v1_relat_1(X1)
        | r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k10_relat_1(X1,k9_relat_1(sK1,X0))) )
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_28 ),
    inference(subsumption_resolution,[],[f279,f43])).

fof(f279,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k7_relat_1(sK1,X0),X1)
        | ~ v1_relat_1(X1)
        | r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k10_relat_1(X1,k9_relat_1(sK1,X0)))
        | ~ v1_relat_1(sK1) )
    | ~ spl2_5
    | ~ spl2_28 ),
    inference(resolution,[],[f167,f51])).

fof(f51,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f50])).

fof(f167,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(k7_relat_1(sK1,X2))
        | ~ r1_tarski(k7_relat_1(sK1,X2),X3)
        | ~ v1_relat_1(X3)
        | r1_tarski(k1_relat_1(k7_relat_1(sK1,X2)),k10_relat_1(X3,k9_relat_1(sK1,X2))) )
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f166])).

fof(f168,plain,
    ( spl2_28
    | ~ spl2_9
    | ~ spl2_25 ),
    inference(avatar_split_clause,[],[f160,f152,f66,f166])).

fof(f66,plain,
    ( spl2_9
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))
        | ~ r1_tarski(X1,X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f152,plain,
    ( spl2_25
  <=> ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f160,plain,
    ( ! [X2,X3] :
        ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X2)),k10_relat_1(X3,k9_relat_1(sK1,X2)))
        | ~ r1_tarski(k7_relat_1(sK1,X2),X3)
        | ~ v1_relat_1(X3)
        | ~ v1_relat_1(k7_relat_1(sK1,X2)) )
    | ~ spl2_9
    | ~ spl2_25 ),
    inference(superposition,[],[f67,f153])).

fof(f153,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,X0))
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f152])).

fof(f67,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))
        | ~ r1_tarski(X1,X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f66])).

fof(f154,plain,
    ( spl2_25
    | ~ spl2_3
    | ~ spl2_11
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f150,f83,f77,f41,f152])).

fof(f77,plain,
    ( spl2_11
  <=> ! [X1,X0] :
        ( k1_relat_1(k7_relat_1(X0,X1)) = k10_relat_1(k7_relat_1(X0,X1),k2_relat_1(k7_relat_1(X0,X1)))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f83,plain,
    ( spl2_12
  <=> ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f150,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,X0))
    | ~ spl2_3
    | ~ spl2_11
    | ~ spl2_12 ),
    inference(forward_demodulation,[],[f148,f84])).

fof(f84,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f83])).

fof(f148,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0)))
    | ~ spl2_3
    | ~ spl2_11 ),
    inference(resolution,[],[f78,f43])).

fof(f78,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | k1_relat_1(k7_relat_1(X0,X1)) = k10_relat_1(k7_relat_1(X0,X1),k2_relat_1(k7_relat_1(X0,X1))) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f77])).

fof(f106,plain,
    ( spl2_16
    | ~ spl2_2
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f100,f93,f36,f103])).

fof(f36,plain,
    ( spl2_2
  <=> r1_tarski(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f93,plain,
    ( spl2_14
  <=> ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK1))
        | k1_relat_1(k7_relat_1(sK1,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f100,plain,
    ( sK0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl2_2
    | ~ spl2_14 ),
    inference(resolution,[],[f94,f38])).

fof(f38,plain,
    ( r1_tarski(sK0,k1_relat_1(sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f94,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK1))
        | k1_relat_1(k7_relat_1(sK1,X0)) = X0 )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f93])).

fof(f95,plain,
    ( spl2_14
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f90,f62,f41,f93])).

fof(f62,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( k1_relat_1(k7_relat_1(X1,X0)) = X0
        | ~ r1_tarski(X0,k1_relat_1(X1))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f90,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK1))
        | k1_relat_1(k7_relat_1(sK1,X0)) = X0 )
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(resolution,[],[f63,f43])).

fof(f63,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ r1_tarski(X0,k1_relat_1(X1))
        | k1_relat_1(k7_relat_1(X1,X0)) = X0 )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f62])).

fof(f85,plain,
    ( spl2_12
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f80,f58,f41,f83])).

fof(f58,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f80,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(resolution,[],[f59,f43])).

fof(f59,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f58])).

fof(f79,plain,
    ( spl2_11
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f70,f50,f46,f77])).

fof(f46,plain,
    ( spl2_4
  <=> ! [X0] :
        ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f70,plain,
    ( ! [X0,X1] :
        ( k1_relat_1(k7_relat_1(X0,X1)) = k10_relat_1(k7_relat_1(X0,X1),k2_relat_1(k7_relat_1(X0,X1)))
        | ~ v1_relat_1(X0) )
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(resolution,[],[f47,f51])).

fof(f47,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f46])).

fof(f68,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f29,f66])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t179_relat_1)).

fof(f64,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f28,f62])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f60,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f27,f58])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f56,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f26,f54])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(f52,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f25,f50])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f48,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f24,f46])).

fof(f24,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f44,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f21,f41])).

fof(f21,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f19])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f39,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f22,f36])).

fof(f22,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f34,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f23,f31])).

fof(f23,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:13:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.42  % (29421)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.42  % (29420)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.42  % (29423)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.22/0.42  % (29420)Refutation found. Thanks to Tanya!
% 0.22/0.42  % SZS status Theorem for theBenchmark
% 0.22/0.42  % SZS output start Proof for theBenchmark
% 0.22/0.42  fof(f296,plain,(
% 0.22/0.42    $false),
% 0.22/0.42    inference(avatar_sat_refutation,[],[f34,f39,f44,f48,f52,f56,f60,f64,f68,f79,f85,f95,f106,f154,f168,f284,f291,f295])).
% 0.22/0.42  fof(f295,plain,(
% 0.22/0.42    spl2_1 | ~spl2_16 | ~spl2_51),
% 0.22/0.42    inference(avatar_contradiction_clause,[],[f294])).
% 0.22/0.42  fof(f294,plain,(
% 0.22/0.42    $false | (spl2_1 | ~spl2_16 | ~spl2_51)),
% 0.22/0.42    inference(subsumption_resolution,[],[f292,f33])).
% 0.22/0.42  fof(f33,plain,(
% 0.22/0.42    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) | spl2_1),
% 0.22/0.42    inference(avatar_component_clause,[],[f31])).
% 0.22/0.42  fof(f31,plain,(
% 0.22/0.42    spl2_1 <=> r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.42  fof(f292,plain,(
% 0.22/0.42    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) | (~spl2_16 | ~spl2_51)),
% 0.22/0.42    inference(superposition,[],[f290,f105])).
% 0.22/0.42  fof(f105,plain,(
% 0.22/0.42    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) | ~spl2_16),
% 0.22/0.42    inference(avatar_component_clause,[],[f103])).
% 0.22/0.42  fof(f103,plain,(
% 0.22/0.42    spl2_16 <=> sK0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.22/0.42  fof(f290,plain,(
% 0.22/0.42    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k10_relat_1(sK1,k9_relat_1(sK1,X0)))) ) | ~spl2_51),
% 0.22/0.42    inference(avatar_component_clause,[],[f289])).
% 0.22/0.42  fof(f289,plain,(
% 0.22/0.42    spl2_51 <=> ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k10_relat_1(sK1,k9_relat_1(sK1,X0)))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).
% 0.22/0.42  fof(f291,plain,(
% 0.22/0.42    spl2_51 | ~spl2_3 | ~spl2_6 | ~spl2_50),
% 0.22/0.42    inference(avatar_split_clause,[],[f287,f282,f54,f41,f289])).
% 0.22/0.42  fof(f41,plain,(
% 0.22/0.42    spl2_3 <=> v1_relat_1(sK1)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.42  fof(f54,plain,(
% 0.22/0.42    spl2_6 <=> ! [X1,X0] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.42  fof(f282,plain,(
% 0.22/0.42    spl2_50 <=> ! [X1,X0] : (~r1_tarski(k7_relat_1(sK1,X0),X1) | ~v1_relat_1(X1) | r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k10_relat_1(X1,k9_relat_1(sK1,X0))))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).
% 0.22/0.42  fof(f287,plain,(
% 0.22/0.42    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k10_relat_1(sK1,k9_relat_1(sK1,X0)))) ) | (~spl2_3 | ~spl2_6 | ~spl2_50)),
% 0.22/0.42    inference(subsumption_resolution,[],[f286,f43])).
% 0.22/0.42  fof(f43,plain,(
% 0.22/0.42    v1_relat_1(sK1) | ~spl2_3),
% 0.22/0.42    inference(avatar_component_clause,[],[f41])).
% 0.22/0.42  fof(f286,plain,(
% 0.22/0.42    ( ! [X0] : (~v1_relat_1(sK1) | r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k10_relat_1(sK1,k9_relat_1(sK1,X0)))) ) | (~spl2_6 | ~spl2_50)),
% 0.22/0.42    inference(duplicate_literal_removal,[],[f285])).
% 0.22/0.42  fof(f285,plain,(
% 0.22/0.42    ( ! [X0] : (~v1_relat_1(sK1) | r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k10_relat_1(sK1,k9_relat_1(sK1,X0))) | ~v1_relat_1(sK1)) ) | (~spl2_6 | ~spl2_50)),
% 0.22/0.42    inference(resolution,[],[f283,f55])).
% 0.22/0.42  fof(f55,plain,(
% 0.22/0.42    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) ) | ~spl2_6),
% 0.22/0.42    inference(avatar_component_clause,[],[f54])).
% 0.22/0.42  fof(f283,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~r1_tarski(k7_relat_1(sK1,X0),X1) | ~v1_relat_1(X1) | r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k10_relat_1(X1,k9_relat_1(sK1,X0)))) ) | ~spl2_50),
% 0.22/0.42    inference(avatar_component_clause,[],[f282])).
% 0.22/0.42  fof(f284,plain,(
% 0.22/0.42    spl2_50 | ~spl2_3 | ~spl2_5 | ~spl2_28),
% 0.22/0.42    inference(avatar_split_clause,[],[f280,f166,f50,f41,f282])).
% 0.22/0.42  fof(f50,plain,(
% 0.22/0.42    spl2_5 <=> ! [X1,X0] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.42  fof(f166,plain,(
% 0.22/0.42    spl2_28 <=> ! [X3,X2] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X2)),k10_relat_1(X3,k9_relat_1(sK1,X2))) | ~r1_tarski(k7_relat_1(sK1,X2),X3) | ~v1_relat_1(X3) | ~v1_relat_1(k7_relat_1(sK1,X2)))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 0.22/0.42  fof(f280,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~r1_tarski(k7_relat_1(sK1,X0),X1) | ~v1_relat_1(X1) | r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k10_relat_1(X1,k9_relat_1(sK1,X0)))) ) | (~spl2_3 | ~spl2_5 | ~spl2_28)),
% 0.22/0.42    inference(subsumption_resolution,[],[f279,f43])).
% 0.22/0.42  fof(f279,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~r1_tarski(k7_relat_1(sK1,X0),X1) | ~v1_relat_1(X1) | r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k10_relat_1(X1,k9_relat_1(sK1,X0))) | ~v1_relat_1(sK1)) ) | (~spl2_5 | ~spl2_28)),
% 0.22/0.42    inference(resolution,[],[f167,f51])).
% 0.22/0.42  fof(f51,plain,(
% 0.22/0.42    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) ) | ~spl2_5),
% 0.22/0.42    inference(avatar_component_clause,[],[f50])).
% 0.22/0.42  fof(f167,plain,(
% 0.22/0.42    ( ! [X2,X3] : (~v1_relat_1(k7_relat_1(sK1,X2)) | ~r1_tarski(k7_relat_1(sK1,X2),X3) | ~v1_relat_1(X3) | r1_tarski(k1_relat_1(k7_relat_1(sK1,X2)),k10_relat_1(X3,k9_relat_1(sK1,X2)))) ) | ~spl2_28),
% 0.22/0.42    inference(avatar_component_clause,[],[f166])).
% 0.22/0.42  fof(f168,plain,(
% 0.22/0.42    spl2_28 | ~spl2_9 | ~spl2_25),
% 0.22/0.42    inference(avatar_split_clause,[],[f160,f152,f66,f166])).
% 0.22/0.42  fof(f66,plain,(
% 0.22/0.42    spl2_9 <=> ! [X1,X0,X2] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.42  fof(f152,plain,(
% 0.22/0.42    spl2_25 <=> ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,X0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.22/0.42  fof(f160,plain,(
% 0.22/0.42    ( ! [X2,X3] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X2)),k10_relat_1(X3,k9_relat_1(sK1,X2))) | ~r1_tarski(k7_relat_1(sK1,X2),X3) | ~v1_relat_1(X3) | ~v1_relat_1(k7_relat_1(sK1,X2))) ) | (~spl2_9 | ~spl2_25)),
% 0.22/0.42    inference(superposition,[],[f67,f153])).
% 0.22/0.42  fof(f153,plain,(
% 0.22/0.42    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,X0))) ) | ~spl2_25),
% 0.22/0.42    inference(avatar_component_clause,[],[f152])).
% 0.22/0.42  fof(f67,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) ) | ~spl2_9),
% 0.22/0.42    inference(avatar_component_clause,[],[f66])).
% 0.22/0.42  fof(f154,plain,(
% 0.22/0.42    spl2_25 | ~spl2_3 | ~spl2_11 | ~spl2_12),
% 0.22/0.42    inference(avatar_split_clause,[],[f150,f83,f77,f41,f152])).
% 0.22/0.42  fof(f77,plain,(
% 0.22/0.42    spl2_11 <=> ! [X1,X0] : (k1_relat_1(k7_relat_1(X0,X1)) = k10_relat_1(k7_relat_1(X0,X1),k2_relat_1(k7_relat_1(X0,X1))) | ~v1_relat_1(X0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.22/0.42  fof(f83,plain,(
% 0.22/0.42    spl2_12 <=> ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.22/0.42  fof(f150,plain,(
% 0.22/0.42    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,X0))) ) | (~spl2_3 | ~spl2_11 | ~spl2_12)),
% 0.22/0.42    inference(forward_demodulation,[],[f148,f84])).
% 0.22/0.42  fof(f84,plain,(
% 0.22/0.42    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)) ) | ~spl2_12),
% 0.22/0.42    inference(avatar_component_clause,[],[f83])).
% 0.22/0.42  fof(f148,plain,(
% 0.22/0.42    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0)))) ) | (~spl2_3 | ~spl2_11)),
% 0.22/0.42    inference(resolution,[],[f78,f43])).
% 0.22/0.42  fof(f78,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~v1_relat_1(X0) | k1_relat_1(k7_relat_1(X0,X1)) = k10_relat_1(k7_relat_1(X0,X1),k2_relat_1(k7_relat_1(X0,X1)))) ) | ~spl2_11),
% 0.22/0.42    inference(avatar_component_clause,[],[f77])).
% 0.22/0.42  fof(f106,plain,(
% 0.22/0.42    spl2_16 | ~spl2_2 | ~spl2_14),
% 0.22/0.42    inference(avatar_split_clause,[],[f100,f93,f36,f103])).
% 0.22/0.42  fof(f36,plain,(
% 0.22/0.42    spl2_2 <=> r1_tarski(sK0,k1_relat_1(sK1))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.43  fof(f93,plain,(
% 0.22/0.43    spl2_14 <=> ! [X0] : (~r1_tarski(X0,k1_relat_1(sK1)) | k1_relat_1(k7_relat_1(sK1,X0)) = X0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.22/0.43  fof(f100,plain,(
% 0.22/0.43    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) | (~spl2_2 | ~spl2_14)),
% 0.22/0.43    inference(resolution,[],[f94,f38])).
% 0.22/0.43  fof(f38,plain,(
% 0.22/0.43    r1_tarski(sK0,k1_relat_1(sK1)) | ~spl2_2),
% 0.22/0.43    inference(avatar_component_clause,[],[f36])).
% 0.22/0.43  fof(f94,plain,(
% 0.22/0.43    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK1)) | k1_relat_1(k7_relat_1(sK1,X0)) = X0) ) | ~spl2_14),
% 0.22/0.43    inference(avatar_component_clause,[],[f93])).
% 0.22/0.43  fof(f95,plain,(
% 0.22/0.43    spl2_14 | ~spl2_3 | ~spl2_8),
% 0.22/0.43    inference(avatar_split_clause,[],[f90,f62,f41,f93])).
% 0.22/0.43  fof(f62,plain,(
% 0.22/0.43    spl2_8 <=> ! [X1,X0] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.43  fof(f90,plain,(
% 0.22/0.43    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK1)) | k1_relat_1(k7_relat_1(sK1,X0)) = X0) ) | (~spl2_3 | ~spl2_8)),
% 0.22/0.43    inference(resolution,[],[f63,f43])).
% 0.22/0.43  fof(f63,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0) ) | ~spl2_8),
% 0.22/0.43    inference(avatar_component_clause,[],[f62])).
% 0.22/0.43  fof(f85,plain,(
% 0.22/0.43    spl2_12 | ~spl2_3 | ~spl2_7),
% 0.22/0.43    inference(avatar_split_clause,[],[f80,f58,f41,f83])).
% 0.22/0.43  fof(f58,plain,(
% 0.22/0.43    spl2_7 <=> ! [X1,X0] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.43  fof(f80,plain,(
% 0.22/0.43    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)) ) | (~spl2_3 | ~spl2_7)),
% 0.22/0.43    inference(resolution,[],[f59,f43])).
% 0.22/0.43  fof(f59,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) ) | ~spl2_7),
% 0.22/0.43    inference(avatar_component_clause,[],[f58])).
% 0.22/0.43  fof(f79,plain,(
% 0.22/0.43    spl2_11 | ~spl2_4 | ~spl2_5),
% 0.22/0.43    inference(avatar_split_clause,[],[f70,f50,f46,f77])).
% 0.22/0.43  fof(f46,plain,(
% 0.22/0.43    spl2_4 <=> ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.43  fof(f70,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X0,X1)) = k10_relat_1(k7_relat_1(X0,X1),k2_relat_1(k7_relat_1(X0,X1))) | ~v1_relat_1(X0)) ) | (~spl2_4 | ~spl2_5)),
% 0.22/0.43    inference(resolution,[],[f47,f51])).
% 0.22/0.43  fof(f47,plain,(
% 0.22/0.43    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) ) | ~spl2_4),
% 0.22/0.43    inference(avatar_component_clause,[],[f46])).
% 0.22/0.43  fof(f68,plain,(
% 0.22/0.43    spl2_9),
% 0.22/0.43    inference(avatar_split_clause,[],[f29,f66])).
% 0.22/0.43  fof(f29,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f18])).
% 0.22/0.43  fof(f18,plain,(
% 0.22/0.43    ! [X0,X1] : (! [X2] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(flattening,[],[f17])).
% 0.22/0.43  fof(f17,plain,(
% 0.22/0.43    ! [X0,X1] : (! [X2] : ((r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f4])).
% 0.22/0.43  fof(f4,axiom,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)))))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t179_relat_1)).
% 0.22/0.43  fof(f64,plain,(
% 0.22/0.43    spl2_8),
% 0.22/0.43    inference(avatar_split_clause,[],[f28,f62])).
% 0.22/0.43  fof(f28,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f16])).
% 0.22/0.43  fof(f16,plain,(
% 0.22/0.43    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(flattening,[],[f15])).
% 0.22/0.43  fof(f15,plain,(
% 0.22/0.43    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f6])).
% 0.22/0.43  fof(f6,axiom,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 0.22/0.43  fof(f60,plain,(
% 0.22/0.43    spl2_7),
% 0.22/0.43    inference(avatar_split_clause,[],[f27,f58])).
% 0.22/0.43  fof(f27,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f14])).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.43  fof(f56,plain,(
% 0.22/0.43    spl2_6),
% 0.22/0.43    inference(avatar_split_clause,[],[f26,f54])).
% 0.22/0.43  fof(f26,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f13])).
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f5])).
% 0.22/0.43  fof(f5,axiom,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
% 0.22/0.43  fof(f52,plain,(
% 0.22/0.43    spl2_5),
% 0.22/0.43    inference(avatar_split_clause,[],[f25,f50])).
% 0.22/0.43  fof(f25,plain,(
% 0.22/0.43    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f12])).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.22/0.43  fof(f48,plain,(
% 0.22/0.43    spl2_4),
% 0.22/0.43    inference(avatar_split_clause,[],[f24,f46])).
% 0.22/0.43  fof(f24,plain,(
% 0.22/0.43    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f11])).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 0.22/0.43  fof(f44,plain,(
% 0.22/0.43    spl2_3),
% 0.22/0.43    inference(avatar_split_clause,[],[f21,f41])).
% 0.22/0.43  fof(f21,plain,(
% 0.22/0.43    v1_relat_1(sK1)),
% 0.22/0.43    inference(cnf_transformation,[],[f20])).
% 0.22/0.43  fof(f20,plain,(
% 0.22/0.43    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f19])).
% 0.22/0.43  fof(f19,plain,(
% 0.22/0.43    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f10,plain,(
% 0.22/0.43    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 0.22/0.43    inference(flattening,[],[f9])).
% 0.22/0.43  fof(f9,plain,(
% 0.22/0.43    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f8])).
% 0.22/0.43  fof(f8,negated_conjecture,(
% 0.22/0.43    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.22/0.43    inference(negated_conjecture,[],[f7])).
% 0.22/0.43  fof(f7,conjecture,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 0.22/0.43  fof(f39,plain,(
% 0.22/0.43    spl2_2),
% 0.22/0.43    inference(avatar_split_clause,[],[f22,f36])).
% 0.22/0.43  fof(f22,plain,(
% 0.22/0.43    r1_tarski(sK0,k1_relat_1(sK1))),
% 0.22/0.43    inference(cnf_transformation,[],[f20])).
% 0.22/0.43  fof(f34,plain,(
% 0.22/0.43    ~spl2_1),
% 0.22/0.43    inference(avatar_split_clause,[],[f23,f31])).
% 0.22/0.43  fof(f23,plain,(
% 0.22/0.43    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 0.22/0.43    inference(cnf_transformation,[],[f20])).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (29420)------------------------------
% 0.22/0.43  % (29420)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (29420)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (29420)Memory used [KB]: 10746
% 0.22/0.43  % (29420)Time elapsed: 0.011 s
% 0.22/0.43  % (29420)------------------------------
% 0.22/0.43  % (29420)------------------------------
% 0.22/0.43  % (29414)Success in time 0.069 s
%------------------------------------------------------------------------------
