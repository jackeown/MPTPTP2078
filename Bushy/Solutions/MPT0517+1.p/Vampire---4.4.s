%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t117_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:48 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   35 (  58 expanded)
%              Number of leaves         :    6 (  16 expanded)
%              Depth                    :   14
%              Number of atoms          :   96 ( 154 expanded)
%              Number of equality atoms :    3 (   5 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f398,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f72,f396])).

fof(f396,plain,
    ( ~ spl8_0
    | spl8_3 ),
    inference(avatar_contradiction_clause,[],[f395])).

fof(f395,plain,
    ( $false
    | ~ spl8_0
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f71,f394])).

fof(f394,plain,
    ( ! [X0] : r1_tarski(k8_relat_1(X0,sK1),sK1)
    | ~ spl8_0 ),
    inference(subsumption_resolution,[],[f393,f63])).

fof(f63,plain,
    ( ! [X0] : v1_relat_1(k8_relat_1(X0,sK1))
    | ~ spl8_0 ),
    inference(resolution,[],[f61,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | v1_relat_1(k8_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t117_relat_1.p',dt_k8_relat_1)).

fof(f61,plain,
    ( v1_relat_1(sK1)
    | ~ spl8_0 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl8_0
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_0])])).

fof(f393,plain,
    ( ! [X0] :
        ( r1_tarski(k8_relat_1(X0,sK1),sK1)
        | ~ v1_relat_1(k8_relat_1(X0,sK1)) )
    | ~ spl8_0 ),
    inference(duplicate_literal_removal,[],[f385])).

fof(f385,plain,
    ( ! [X0] :
        ( r1_tarski(k8_relat_1(X0,sK1),sK1)
        | ~ v1_relat_1(k8_relat_1(X0,sK1))
        | r1_tarski(k8_relat_1(X0,sK1),sK1) )
    | ~ spl8_0 ),
    inference(resolution,[],[f202,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
      | ~ v1_relat_1(X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t117_relat_1.p',d3_relat_1)).

fof(f202,plain,
    ( ! [X2,X3] :
        ( r2_hidden(k4_tarski(sK2(k8_relat_1(X2,sK1),X3),sK3(k8_relat_1(X2,sK1),X3)),sK1)
        | r1_tarski(k8_relat_1(X2,sK1),X3) )
    | ~ spl8_0 ),
    inference(resolution,[],[f157,f43])).

fof(f43,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ sP6(X4,X3,X1,X0)
      | r2_hidden(k4_tarski(X3,X4),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t117_relat_1.p',d12_relat_1)).

fof(f157,plain,
    ( ! [X0,X1] :
        ( sP6(sK3(k8_relat_1(X0,sK1),X1),sK2(k8_relat_1(X0,sK1),X1),sK1,X0)
        | r1_tarski(k8_relat_1(X0,sK1),X1) )
    | ~ spl8_0 ),
    inference(subsumption_resolution,[],[f156,f61])).

fof(f156,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k8_relat_1(X0,sK1),X1)
        | sP6(sK3(k8_relat_1(X0,sK1),X1),sK2(k8_relat_1(X0,sK1),X1),sK1,X0)
        | ~ v1_relat_1(sK1) )
    | ~ spl8_0 ),
    inference(subsumption_resolution,[],[f146,f63])).

fof(f146,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k8_relat_1(X0,sK1),X1)
        | ~ v1_relat_1(k8_relat_1(X0,sK1))
        | sP6(sK3(k8_relat_1(X0,sK1),X1),sK2(k8_relat_1(X0,sK1),X1),sK1,X0)
        | ~ v1_relat_1(sK1) )
    | ~ spl8_0 ),
    inference(resolution,[],[f68,f57])).

fof(f57,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1))
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | sP6(X4,X3,X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | sP6(X4,X3,X1,X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k8_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f68,plain,
    ( ! [X6,X5] :
        ( r2_hidden(k4_tarski(sK2(k8_relat_1(X5,sK1),X6),sK3(k8_relat_1(X5,sK1),X6)),k8_relat_1(X5,sK1))
        | r1_tarski(k8_relat_1(X5,sK1),X6) )
    | ~ spl8_0 ),
    inference(resolution,[],[f63,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f71,plain,
    ( ~ r1_tarski(k8_relat_1(sK0,sK1),sK1)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl8_3
  <=> ~ r1_tarski(k8_relat_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f72,plain,(
    ~ spl8_3 ),
    inference(avatar_split_clause,[],[f35,f70])).

fof(f35,plain,(
    ~ r1_tarski(k8_relat_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k8_relat_1(X0,X1),X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t117_relat_1.p',t117_relat_1)).

fof(f62,plain,(
    spl8_0 ),
    inference(avatar_split_clause,[],[f34,f60])).

fof(f34,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
