%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t89_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:28 EDT 2019

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :   43 (  56 expanded)
%              Number of leaves         :    8 (  14 expanded)
%              Depth                    :   15
%              Number of atoms          :  150 ( 186 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f240,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f70,f77,f239])).

fof(f239,plain,
    ( ~ spl5_0
    | ~ spl5_2
    | spl5_5 ),
    inference(avatar_contradiction_clause,[],[f238])).

fof(f238,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f237,f69])).

fof(f69,plain,
    ( v1_funct_1(sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl5_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f237,plain,
    ( ~ v1_funct_1(sK1)
    | ~ spl5_0
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f233,f62])).

fof(f62,plain,
    ( v1_relat_1(sK1)
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl5_0
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f233,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ spl5_5 ),
    inference(resolution,[],[f204,f76])).

fof(f76,plain,
    ( ~ r1_tarski(k1_relat_1(k8_relat_1(sK0,sK1)),k1_relat_1(sK1))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl5_5
  <=> ~ r1_tarski(k1_relat_1(k8_relat_1(sK0,sK1)),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f204,plain,(
    ! [X12,X13] :
      ( r1_tarski(k1_relat_1(k8_relat_1(X13,X12)),k1_relat_1(X12))
      | ~ v1_relat_1(X12)
      | ~ v1_funct_1(X12) ) ),
    inference(duplicate_literal_removal,[],[f202])).

fof(f202,plain,(
    ! [X12,X13] :
      ( ~ v1_funct_1(X12)
      | ~ v1_relat_1(X12)
      | r1_tarski(k1_relat_1(k8_relat_1(X13,X12)),k1_relat_1(X12))
      | r1_tarski(k1_relat_1(k8_relat_1(X13,X12)),k1_relat_1(X12)) ) ),
    inference(resolution,[],[f84,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t89_funct_1.p',d3_tarski)).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(k1_relat_1(k8_relat_1(X0,X1)),X2),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),X2) ) ),
    inference(subsumption_resolution,[],[f83,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t89_funct_1.p',dt_k8_relat_1)).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | r2_hidden(sK2(k1_relat_1(k8_relat_1(X0,X1)),X2),k1_relat_1(X1))
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),X2) ) ),
    inference(subsumption_resolution,[],[f82,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k8_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t89_funct_1.p',fc9_funct_1)).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | r2_hidden(sK2(k1_relat_1(k8_relat_1(X0,X1)),X2),k1_relat_1(X1))
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),X2) ) ),
    inference(resolution,[],[f56,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f56,plain,(
    ! [X4,X2,X0] :
      ( ~ r2_hidden(X4,k1_relat_1(k8_relat_1(X0,X2)))
      | ~ v1_funct_1(k8_relat_1(X0,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | r2_hidden(X4,k1_relat_1(X2))
      | ~ v1_relat_1(k8_relat_1(X0,X2)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | r2_hidden(X4,k1_relat_1(X2))
      | ~ r2_hidden(X4,k1_relat_1(X1))
      | k8_relat_1(X0,X2) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) ) ) ) ),
    inference(rectify,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) )
              & ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X3),X0)
                    & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t89_funct_1.p',t85_funct_1)).

fof(f77,plain,(
    ~ spl5_5 ),
    inference(avatar_split_clause,[],[f34,f75])).

fof(f34,plain,(
    ~ r1_tarski(k1_relat_1(k8_relat_1(sK0,sK1)),k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t89_funct_1.p',t89_funct_1)).

fof(f70,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f33,f68])).

fof(f33,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f63,plain,(
    spl5_0 ),
    inference(avatar_split_clause,[],[f32,f61])).

fof(f32,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
