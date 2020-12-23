%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : ordinal1__t48_ordinal1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:27 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 126 expanded)
%              Number of leaves         :   11 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :  203 ( 872 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f76,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f61,f65,f69,f75])).

fof(f75,plain,(
    spl3_7 ),
    inference(avatar_contradiction_clause,[],[f74])).

fof(f74,plain,
    ( $false
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f73,f20])).

fof(f20,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( ~ v5_ordinal1(k7_relat_1(sK1,sK2))
      | ~ v1_funct_1(k7_relat_1(sK1,sK2))
      | ~ v5_relat_1(k7_relat_1(sK1,sK2),sK0)
      | ~ v1_relat_1(k7_relat_1(sK1,sK2)) )
    & v3_ordinal1(sK2)
    & v5_ordinal1(sK1)
    & v1_funct_1(sK1)
    & v5_relat_1(sK1,sK0)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f18,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ v5_ordinal1(k7_relat_1(X1,X2))
              | ~ v1_funct_1(k7_relat_1(X1,X2))
              | ~ v5_relat_1(k7_relat_1(X1,X2),X0)
              | ~ v1_relat_1(k7_relat_1(X1,X2)) )
            & v3_ordinal1(X2) )
        & v5_ordinal1(X1)
        & v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ( ~ v5_ordinal1(k7_relat_1(sK1,X2))
            | ~ v1_funct_1(k7_relat_1(sK1,X2))
            | ~ v5_relat_1(k7_relat_1(sK1,X2),sK0)
            | ~ v1_relat_1(k7_relat_1(sK1,X2)) )
          & v3_ordinal1(X2) )
      & v5_ordinal1(sK1)
      & v1_funct_1(sK1)
      & v5_relat_1(sK1,sK0)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ v5_ordinal1(k7_relat_1(X1,X2))
            | ~ v1_funct_1(k7_relat_1(X1,X2))
            | ~ v5_relat_1(k7_relat_1(X1,X2),X0)
            | ~ v1_relat_1(k7_relat_1(X1,X2)) )
          & v3_ordinal1(X2) )
     => ( ( ~ v5_ordinal1(k7_relat_1(X1,sK2))
          | ~ v1_funct_1(k7_relat_1(X1,sK2))
          | ~ v5_relat_1(k7_relat_1(X1,sK2),X0)
          | ~ v1_relat_1(k7_relat_1(X1,sK2)) )
        & v3_ordinal1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ v5_ordinal1(k7_relat_1(X1,X2))
            | ~ v1_funct_1(k7_relat_1(X1,X2))
            | ~ v5_relat_1(k7_relat_1(X1,X2),X0)
            | ~ v1_relat_1(k7_relat_1(X1,X2)) )
          & v3_ordinal1(X2) )
      & v5_ordinal1(X1)
      & v1_funct_1(X1)
      & v5_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ v5_ordinal1(k7_relat_1(X1,X2))
            | ~ v1_funct_1(k7_relat_1(X1,X2))
            | ~ v5_relat_1(k7_relat_1(X1,X2),X0)
            | ~ v1_relat_1(k7_relat_1(X1,X2)) )
          & v3_ordinal1(X2) )
      & v5_ordinal1(X1)
      & v1_funct_1(X1)
      & v5_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v5_ordinal1(X1)
          & v1_funct_1(X1)
          & v5_relat_1(X1,X0)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( v3_ordinal1(X2)
           => ( v5_ordinal1(k7_relat_1(X1,X2))
              & v1_funct_1(k7_relat_1(X1,X2))
              & v5_relat_1(k7_relat_1(X1,X2),X0)
              & v1_relat_1(k7_relat_1(X1,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ( v5_ordinal1(X1)
        & v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( v5_ordinal1(k7_relat_1(X1,X2))
            & v1_funct_1(k7_relat_1(X1,X2))
            & v5_relat_1(k7_relat_1(X1,X2),X0)
            & v1_relat_1(k7_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t48_ordinal1.p',t48_ordinal1)).

fof(f73,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f72,f22])).

fof(f22,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f72,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f71,f23])).

fof(f23,plain,(
    v5_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f71,plain,
    ( ~ v5_ordinal1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f70,f24])).

fof(f24,plain,(
    v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f70,plain,
    ( ~ v3_ordinal1(sK2)
    | ~ v5_ordinal1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_7 ),
    inference(resolution,[],[f29,f57])).

fof(f57,plain,
    ( ~ v5_ordinal1(k7_relat_1(sK1,sK2))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl3_7
  <=> ~ v5_ordinal1(k7_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v5_ordinal1(k7_relat_1(X0,X1))
      | ~ v3_ordinal1(X1)
      | ~ v5_ordinal1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( v5_ordinal1(k7_relat_1(X0,X1))
        & v5_relat_1(k7_relat_1(X0,X1),k2_relat_1(X0))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v3_ordinal1(X1)
      | ~ v5_ordinal1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( v5_ordinal1(k7_relat_1(X0,X1))
        & v5_relat_1(k7_relat_1(X0,X1),k2_relat_1(X0))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v3_ordinal1(X1)
      | ~ v5_ordinal1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v5_ordinal1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v5_ordinal1(k7_relat_1(X0,X1))
        & v5_relat_1(k7_relat_1(X0,X1),k2_relat_1(X0))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t48_ordinal1.p',fc5_ordinal1)).

fof(f69,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f68])).

fof(f68,plain,
    ( $false
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f67,f20])).

fof(f67,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f66,f21])).

fof(f21,plain,(
    v5_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f66,plain,
    ( ~ v5_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl3_3 ),
    inference(resolution,[],[f33,f45])).

fof(f45,plain,
    ( ~ v5_relat_1(k7_relat_1(sK1,sK2),sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl3_3
  <=> ~ v5_relat_1(k7_relat_1(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v5_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(k7_relat_1(X2,X0),X1)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v5_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(k7_relat_1(X2,X0),X1)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v5_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v1_relat_1(X2) )
     => ( v5_relat_1(k7_relat_1(X2,X0),X1)
        & v1_relat_1(k7_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t48_ordinal1.p',fc22_relat_1)).

fof(f65,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f64])).

fof(f64,plain,
    ( $false
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f63,f20])).

fof(f63,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f62,f22])).

fof(f62,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_5 ),
    inference(resolution,[],[f31,f51])).

fof(f51,plain,
    ( ~ v1_funct_1(k7_relat_1(sK1,sK2))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl3_5
  <=> ~ v1_funct_1(k7_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t48_ordinal1.p',fc8_funct_1)).

fof(f61,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f60])).

fof(f60,plain,
    ( $false
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f59,f20])).

fof(f59,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl3_1 ),
    inference(resolution,[],[f26,f39])).

fof(f39,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl3_1
  <=> ~ v1_relat_1(k7_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t48_ordinal1.p',dt_k7_relat_1)).

fof(f58,plain,
    ( ~ spl3_1
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f25,f56,f50,f44,f38])).

fof(f25,plain,
    ( ~ v5_ordinal1(k7_relat_1(sK1,sK2))
    | ~ v1_funct_1(k7_relat_1(sK1,sK2))
    | ~ v5_relat_1(k7_relat_1(sK1,sK2),sK0)
    | ~ v1_relat_1(k7_relat_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
