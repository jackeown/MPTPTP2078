%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0942+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:56 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   29 (  40 expanded)
%              Number of leaves         :    9 (  13 expanded)
%              Depth                    :    6
%              Number of atoms          :   84 ( 109 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f41,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f23,f21,f22,f20,f32,f19,f33,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_wellord1(X0)
      | v2_wellord1(X0)
      | ~ v6_relat_2(X0)
      | ~ v4_relat_2(X0)
      | ~ v8_relat_2(X0)
      | ~ v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).

fof(f33,plain,(
    v1_wellord1(k1_wellord2(sK0)) ),
    inference(unit_resulting_resolution,[],[f18,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v1_wellord1(k1_wellord2(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( v1_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v1_wellord1(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_wellord2)).

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
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => v2_wellord1(k1_wellord2(X0)) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v2_wellord1(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_wellord2)).

fof(f19,plain,(
    ~ v2_wellord1(k1_wellord2(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f32,plain,(
    v6_relat_2(k1_wellord2(sK0)) ),
    inference(unit_resulting_resolution,[],[f18,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v6_relat_2(k1_wellord2(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( v6_relat_2(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v6_relat_2(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_wellord2)).

fof(f20,plain,(
    ! [X0] : v4_relat_2(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : v4_relat_2(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_wellord2)).

fof(f22,plain,(
    ! [X0] : v8_relat_2(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : v8_relat_2(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_wellord2)).

fof(f21,plain,(
    ! [X0] : v1_relat_2(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_2(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_wellord2)).

fof(f23,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

%------------------------------------------------------------------------------
