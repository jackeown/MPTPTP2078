%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : wellord2__t7_wellord2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:18 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   43 (  56 expanded)
%              Number of leaves         :   11 (  17 expanded)
%              Depth                    :   11
%              Number of atoms          :  122 ( 151 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f58,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f53,f57])).

fof(f57,plain,(
    spl1_3 ),
    inference(avatar_contradiction_clause,[],[f56])).

fof(f56,plain,
    ( $false
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f54,f18])).

fof(f18,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ v2_wellord1(k1_wellord2(sK0))
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( ~ v2_wellord1(k1_wellord2(X0))
        & v3_ordinal1(X0) )
   => ( ~ v2_wellord1(k1_wellord2(sK0))
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ~ v2_wellord1(k1_wellord2(X0))
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => v2_wellord1(k1_wellord2(X0)) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v2_wellord1(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/wellord2__t7_wellord2.p',t7_wellord2)).

fof(f54,plain,
    ( ~ v3_ordinal1(sK0)
    | ~ spl1_3 ),
    inference(resolution,[],[f48,f30])).

fof(f30,plain,(
    ! [X0] :
      ( v6_relat_2(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( v6_relat_2(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v6_relat_2(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/wellord2__t7_wellord2.p',t4_wellord2)).

fof(f48,plain,
    ( ~ v6_relat_2(k1_wellord2(sK0))
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl1_3
  <=> ~ v6_relat_2(k1_wellord2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f53,plain,(
    spl1_1 ),
    inference(avatar_contradiction_clause,[],[f52])).

fof(f52,plain,
    ( $false
    | ~ spl1_1 ),
    inference(subsumption_resolution,[],[f50,f18])).

fof(f50,plain,
    ( ~ v3_ordinal1(sK0)
    | ~ spl1_1 ),
    inference(resolution,[],[f42,f31])).

fof(f31,plain,(
    ! [X0] :
      ( v1_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( v1_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v1_wellord1(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/wellord2__t7_wellord2.p',t6_wellord2)).

fof(f42,plain,
    ( ~ v1_wellord1(k1_wellord2(sK0))
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl1_1
  <=> ~ v1_wellord1(k1_wellord2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f49,plain,
    ( ~ spl1_1
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f36,f47,f41])).

fof(f36,plain,
    ( ~ v6_relat_2(k1_wellord2(sK0))
    | ~ v1_wellord1(k1_wellord2(sK0)) ),
    inference(resolution,[],[f35,f19])).

fof(f19,plain,(
    ~ v2_wellord1(k1_wellord2(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v6_relat_2(k1_wellord2(X0))
      | ~ v1_wellord1(k1_wellord2(X0)) ) ),
    inference(subsumption_resolution,[],[f34,f22])).

fof(f22,plain,(
    ! [X0] : v1_relat_2(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : v1_relat_2(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/wellord2__t7_wellord2.p',t2_wellord2)).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_wellord1(k1_wellord2(X0))
      | ~ v6_relat_2(k1_wellord2(X0))
      | ~ v1_relat_2(k1_wellord2(X0))
      | v2_wellord1(k1_wellord2(X0)) ) ),
    inference(subsumption_resolution,[],[f33,f21])).

fof(f21,plain,(
    ! [X0] : v8_relat_2(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : v8_relat_2(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/wellord2__t7_wellord2.p',t3_wellord2)).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_wellord1(k1_wellord2(X0))
      | ~ v6_relat_2(k1_wellord2(X0))
      | ~ v8_relat_2(k1_wellord2(X0))
      | ~ v1_relat_2(k1_wellord2(X0))
      | v2_wellord1(k1_wellord2(X0)) ) ),
    inference(subsumption_resolution,[],[f32,f20])).

fof(f20,plain,(
    ! [X0] : v4_relat_2(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : v4_relat_2(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/wellord2__t7_wellord2.p',t5_wellord2)).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_wellord1(k1_wellord2(X0))
      | ~ v6_relat_2(k1_wellord2(X0))
      | ~ v4_relat_2(k1_wellord2(X0))
      | ~ v8_relat_2(k1_wellord2(X0))
      | ~ v1_relat_2(k1_wellord2(X0))
      | v2_wellord1(k1_wellord2(X0)) ) ),
    inference(resolution,[],[f29,f23])).

fof(f23,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/wellord2__t7_wellord2.p',dt_k1_wellord2)).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_wellord1(X0)
      | ~ v6_relat_2(X0)
      | ~ v4_relat_2(X0)
      | ~ v8_relat_2(X0)
      | ~ v1_relat_2(X0)
      | v2_wellord1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord2__t7_wellord2.p',d4_wellord1)).
%------------------------------------------------------------------------------
