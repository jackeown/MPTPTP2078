%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t67_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:26 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 176 expanded)
%              Number of leaves         :   11 (  55 expanded)
%              Depth                    :   18
%              Number of atoms          :  155 ( 439 expanded)
%              Number of equality atoms :   62 ( 151 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2275,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f2265,f2266])).

fof(f2266,plain,(
    spl1_1 ),
    inference(avatar_contradiction_clause,[],[f2258])).

fof(f2258,plain,
    ( $false
    | ~ spl1_1 ),
    inference(unit_resulting_resolution,[],[f48,f514])).

fof(f514,plain,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(subsumption_resolution,[],[f513,f34])).

fof(f34,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t67_funct_1.p',t71_relat_1)).

fof(f513,plain,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) != X0
      | k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ) ),
    inference(forward_demodulation,[],[f512,f112])).

fof(f112,plain,(
    ! [X0] : k1_relat_1(k2_funct_1(k6_relat_1(X0))) = X0 ),
    inference(forward_demodulation,[],[f111,f34])).

fof(f111,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = k1_relat_1(k2_funct_1(k6_relat_1(X0))) ),
    inference(unit_resulting_resolution,[],[f28,f32,f30,f37])).

fof(f37,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t67_funct_1.p',t55_funct_1)).

fof(f30,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t67_funct_1.p',fc4_funct_1)).

fof(f32,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t67_funct_1.p',fc3_funct_1)).

fof(f28,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t67_funct_1.p',dt_k6_relat_1)).

fof(f512,plain,(
    ! [X0] :
      ( k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))
      | k2_relat_1(k6_relat_1(X0)) != k1_relat_1(k2_funct_1(k6_relat_1(X0))) ) ),
    inference(forward_demodulation,[],[f511,f112])).

fof(f511,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(k2_funct_1(k6_relat_1(X0)))) = k2_funct_1(k6_relat_1(X0))
      | k2_relat_1(k6_relat_1(X0)) != k1_relat_1(k2_funct_1(k6_relat_1(X0))) ) ),
    inference(subsumption_resolution,[],[f510,f28])).

fof(f510,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(k2_funct_1(k6_relat_1(X0)))) = k2_funct_1(k6_relat_1(X0))
      | k2_relat_1(k6_relat_1(X0)) != k1_relat_1(k2_funct_1(k6_relat_1(X0)))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f509,f32])).

fof(f509,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(k2_funct_1(k6_relat_1(X0)))) = k2_funct_1(k6_relat_1(X0))
      | k2_relat_1(k6_relat_1(X0)) != k1_relat_1(k2_funct_1(k6_relat_1(X0)))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f508,f50])).

fof(f50,plain,(
    ! [X0] : v1_relat_1(k2_funct_1(k6_relat_1(X0))) ),
    inference(unit_resulting_resolution,[],[f28,f32,f35])).

fof(f35,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t67_funct_1.p',dt_k2_funct_1)).

fof(f508,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(k2_funct_1(k6_relat_1(X0)))) = k2_funct_1(k6_relat_1(X0))
      | k2_relat_1(k6_relat_1(X0)) != k1_relat_1(k2_funct_1(k6_relat_1(X0)))
      | ~ v1_relat_1(k2_funct_1(k6_relat_1(X0)))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f507,f51])).

fof(f51,plain,(
    ! [X0] : v1_funct_1(k2_funct_1(k6_relat_1(X0))) ),
    inference(unit_resulting_resolution,[],[f28,f32,f36])).

fof(f36,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f507,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(k2_funct_1(k6_relat_1(X0)))) = k2_funct_1(k6_relat_1(X0))
      | k2_relat_1(k6_relat_1(X0)) != k1_relat_1(k2_funct_1(k6_relat_1(X0)))
      | ~ v1_funct_1(k2_funct_1(k6_relat_1(X0)))
      | ~ v1_relat_1(k2_funct_1(k6_relat_1(X0)))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(trivial_inequality_removal,[],[f505])).

fof(f505,plain,(
    ! [X0] :
      ( k6_relat_1(X0) != k6_relat_1(X0)
      | k6_relat_1(k1_relat_1(k2_funct_1(k6_relat_1(X0)))) = k2_funct_1(k6_relat_1(X0))
      | k2_relat_1(k6_relat_1(X0)) != k1_relat_1(k2_funct_1(k6_relat_1(X0)))
      | ~ v1_funct_1(k2_funct_1(k6_relat_1(X0)))
      | ~ v1_relat_1(k2_funct_1(k6_relat_1(X0)))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f41,f251])).

fof(f251,plain,(
    ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k2_funct_1(k6_relat_1(X0))) ),
    inference(forward_demodulation,[],[f249,f33])).

fof(f33,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f249,plain,(
    ! [X0] : k6_relat_1(k1_relat_1(k6_relat_1(X0))) = k5_relat_1(k6_relat_1(X0),k2_funct_1(k6_relat_1(X0))) ),
    inference(unit_resulting_resolution,[],[f28,f32,f30,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t67_funct_1.p',t61_funct_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) != X0
      | k6_relat_1(k1_relat_1(X1)) = X1
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_relat_1(k1_relat_1(X1)) = X1
          | k5_relat_1(X0,X1) != X0
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_relat_1(k1_relat_1(X1)) = X1
          | k5_relat_1(X0,X1) != X0
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = X0
              & k2_relat_1(X0) = k1_relat_1(X1) )
           => k6_relat_1(k1_relat_1(X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t67_funct_1.p',t44_funct_1)).

fof(f48,plain,
    ( k6_relat_1(sK0) != k2_funct_1(k6_relat_1(sK0))
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl1_1
  <=> k6_relat_1(sK0) != k2_funct_1(k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f2265,plain,(
    spl1_1 ),
    inference(avatar_contradiction_clause,[],[f2264])).

fof(f2264,plain,
    ( $false
    | ~ spl1_1 ),
    inference(trivial_inequality_removal,[],[f2259])).

fof(f2259,plain,
    ( k6_relat_1(sK0) != k6_relat_1(sK0)
    | ~ spl1_1 ),
    inference(superposition,[],[f48,f514])).

fof(f49,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f27,f47])).

fof(f27,plain,(
    k6_relat_1(sK0) != k2_funct_1(k6_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    k6_relat_1(sK0) != k2_funct_1(k6_relat_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f25])).

fof(f25,plain,
    ( ? [X0] : k6_relat_1(X0) != k2_funct_1(k6_relat_1(X0))
   => k6_relat_1(sK0) != k2_funct_1(k6_relat_1(sK0)) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] : k6_relat_1(X0) != k2_funct_1(k6_relat_1(X0)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t67_funct_1.p',t67_funct_1)).
%------------------------------------------------------------------------------
