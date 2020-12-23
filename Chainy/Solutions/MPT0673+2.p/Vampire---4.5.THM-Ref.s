%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0673+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:44 EST 2020

% Result     : Theorem 2.95s
% Output     : Refutation 2.95s
% Verified   : 
% Statistics : Number of formulae       :   31 (  57 expanded)
%              Number of leaves         :    6 (  15 expanded)
%              Depth                    :   14
%              Number of atoms          :  105 ( 220 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6808,plain,(
    $false ),
    inference(resolution,[],[f5325,f1255])).

fof(f1255,plain,(
    ~ v2_funct_1(k8_relat_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f1165])).

fof(f1165,plain,
    ( ~ v2_funct_1(k8_relat_1(sK0,sK1))
    & v2_funct_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f985,f1164])).

fof(f1164,plain,
    ( ? [X0,X1] :
        ( ~ v2_funct_1(k8_relat_1(X0,X1))
        & v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ v2_funct_1(k8_relat_1(sK0,sK1))
      & v2_funct_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f985,plain,(
    ? [X0,X1] :
      ( ~ v2_funct_1(k8_relat_1(X0,X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f984])).

fof(f984,plain,(
    ? [X0,X1] :
      ( ~ v2_funct_1(k8_relat_1(X0,X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f979])).

fof(f979,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( v2_funct_1(X1)
         => v2_funct_1(k8_relat_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f978])).

fof(f978,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => v2_funct_1(k8_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_funct_1)).

fof(f5325,plain,(
    ! [X8] : v2_funct_1(k8_relat_1(X8,sK1)) ),
    inference(subsumption_resolution,[],[f5324,f1252])).

fof(f1252,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f1165])).

fof(f5324,plain,(
    ! [X8] :
      ( v2_funct_1(k8_relat_1(X8,sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f5323,f1253])).

fof(f1253,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f1165])).

fof(f5323,plain,(
    ! [X8] :
      ( v2_funct_1(k8_relat_1(X8,sK1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f5322,f1254])).

fof(f1254,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f1165])).

fof(f5322,plain,(
    ! [X8] :
      ( v2_funct_1(k8_relat_1(X8,sK1))
      | ~ v2_funct_1(sK1)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f5321,f1493])).

fof(f1493,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f903])).

fof(f903,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f5321,plain,(
    ! [X8] :
      ( v2_funct_1(k8_relat_1(X8,sK1))
      | ~ v1_relat_1(k6_relat_1(X8))
      | ~ v2_funct_1(sK1)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f5320,f1494])).

fof(f1494,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f903])).

fof(f5320,plain,(
    ! [X8] :
      ( v2_funct_1(k8_relat_1(X8,sK1))
      | ~ v1_funct_1(k6_relat_1(X8))
      | ~ v1_relat_1(k6_relat_1(X8))
      | ~ v2_funct_1(sK1)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f5304,f1386])).

fof(f1386,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f949])).

fof(f949,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

fof(f5304,plain,(
    ! [X8] :
      ( v2_funct_1(k8_relat_1(X8,sK1))
      | ~ v2_funct_1(k6_relat_1(X8))
      | ~ v1_funct_1(k6_relat_1(X8))
      | ~ v1_relat_1(k6_relat_1(X8))
      | ~ v2_funct_1(sK1)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f1322,f1554])).

fof(f1554,plain,(
    ! [X34] : k8_relat_1(X34,sK1) = k5_relat_1(sK1,k6_relat_1(X34)) ),
    inference(resolution,[],[f1252,f1304])).

fof(f1304,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f1027])).

fof(f1027,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f726])).

fof(f726,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f1322,plain,(
    ! [X0,X1] :
      ( v2_funct_1(k5_relat_1(X0,X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1043])).

fof(f1043,plain,(
    ! [X0,X1] :
      ( ( v2_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1042])).

fof(f1042,plain,(
    ! [X0,X1] :
      ( ( v2_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f907])).

fof(f907,axiom,(
    ! [X0,X1] :
      ( ( v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1)
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_funct_1)).
%------------------------------------------------------------------------------
