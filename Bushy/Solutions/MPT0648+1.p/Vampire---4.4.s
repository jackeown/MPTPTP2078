%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t55_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n030.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:25 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   24 (  70 expanded)
%              Number of leaves         :    3 (  13 expanded)
%              Depth                    :    9
%              Number of atoms          :   62 ( 255 expanded)
%              Number of equality atoms :   27 ( 102 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f74,plain,(
    $false ),
    inference(global_subsumption,[],[f19,f68,f67])).

fof(f67,plain,(
    k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
    inference(superposition,[],[f50,f66])).

fof(f66,plain,(
    k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f65,f20])).

fof(f20,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) != k1_relat_1(X0)
        | k2_relat_1(X0) != k1_relat_1(k2_funct_1(X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) != k1_relat_1(X0)
        | k2_relat_1(X0) != k1_relat_1(k2_funct_1(X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
            & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t55_funct_1.p',t55_funct_1)).

fof(f65,plain,
    ( ~ v1_relat_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f64,f21])).

fof(f21,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f64,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(resolution,[],[f29,f22])).

fof(f22,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_funct_1(X0) = k4_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(X0) = k4_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t55_funct_1.p',d9_funct_1)).

fof(f50,plain,(
    k2_relat_1(k4_relat_1(sK0)) = k1_relat_1(sK0) ),
    inference(resolution,[],[f26,f20])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t55_funct_1.p',t37_relat_1)).

fof(f68,plain,(
    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    inference(superposition,[],[f47,f66])).

fof(f47,plain,(
    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f25,f20])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f19,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0))
    | k2_relat_1(k2_funct_1(sK0)) != k1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
