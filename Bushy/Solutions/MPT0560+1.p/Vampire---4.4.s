%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t162_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:53 EDT 2019

% Result     : Theorem 21.33s
% Output     : Refutation 21.33s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 192 expanded)
%              Number of leaves         :   13 (  53 expanded)
%              Depth                    :   12
%              Number of atoms          :  256 ( 547 expanded)
%              Number of equality atoms :   16 (  87 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2585,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f488,f520,f551,f1695,f2582])).

fof(f2582,plain,
    ( ~ spl12_24
    | ~ spl12_28 ),
    inference(avatar_contradiction_clause,[],[f2581])).

fof(f2581,plain,
    ( $false
    | ~ spl12_24
    | ~ spl12_28 ),
    inference(subsumption_resolution,[],[f2580,f46])).

fof(f46,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k9_relat_1(X0,X1) != k9_relat_1(k7_relat_1(X0,X2),X1)
          & r1_tarski(X1,X2) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1,X2] :
            ( r1_tarski(X1,X2)
           => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t162_relat_1.p',t162_relat_1)).

fof(f2580,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl12_24
    | ~ spl12_28 ),
    inference(subsumption_resolution,[],[f2576,f1720])).

fof(f1720,plain,
    ( r2_hidden(sK5(sK0,sK1,k9_relat_1(k7_relat_1(sK0,sK2),sK1)),k9_relat_1(sK0,sK1))
    | ~ spl12_24 ),
    inference(subsumption_resolution,[],[f1719,f105])).

fof(f105,plain,(
    ! [X1] : r1_tarski(k7_relat_1(sK0,X1),sK0) ),
    inference(resolution,[],[f46,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t162_relat_1.p',t88_relat_1)).

fof(f1719,plain,
    ( ~ r1_tarski(k7_relat_1(sK0,sK2),sK0)
    | r2_hidden(sK5(sK0,sK1,k9_relat_1(k7_relat_1(sK0,sK2),sK1)),k9_relat_1(sK0,sK1))
    | ~ spl12_24 ),
    inference(subsumption_resolution,[],[f1705,f104])).

fof(f104,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK0,X0)) ),
    inference(resolution,[],[f46,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t162_relat_1.p',dt_k7_relat_1)).

fof(f1705,plain,
    ( ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ r1_tarski(k7_relat_1(sK0,sK2),sK0)
    | r2_hidden(sK5(sK0,sK1,k9_relat_1(k7_relat_1(sK0,sK2),sK1)),k9_relat_1(sK0,sK1))
    | ~ spl12_24 ),
    inference(resolution,[],[f481,f307])).

fof(f307,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X3,k9_relat_1(X2,X4))
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X2,sK0)
      | r2_hidden(X3,k9_relat_1(sK0,X4)) ) ),
    inference(resolution,[],[f106,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t162_relat_1.p',d3_tarski)).

fof(f106,plain,(
    ! [X2,X3] :
      ( r1_tarski(k9_relat_1(X2,X3),k9_relat_1(sK0,X3))
      | ~ r1_tarski(X2,sK0)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f46,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t162_relat_1.p',t157_relat_1)).

fof(f481,plain,
    ( r2_hidden(sK5(sK0,sK1,k9_relat_1(k7_relat_1(sK0,sK2),sK1)),k9_relat_1(k7_relat_1(sK0,sK2),sK1))
    | ~ spl12_24 ),
    inference(avatar_component_clause,[],[f480])).

fof(f480,plain,
    ( spl12_24
  <=> r2_hidden(sK5(sK0,sK1,k9_relat_1(k7_relat_1(sK0,sK2),sK1)),k9_relat_1(k7_relat_1(sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_24])])).

fof(f2576,plain,
    ( ~ r2_hidden(sK5(sK0,sK1,k9_relat_1(k7_relat_1(sK0,sK2),sK1)),k9_relat_1(sK0,sK1))
    | ~ v1_relat_1(sK0)
    | ~ spl12_28 ),
    inference(duplicate_literal_removal,[],[f2570])).

fof(f2570,plain,
    ( ~ r2_hidden(sK5(sK0,sK1,k9_relat_1(k7_relat_1(sK0,sK2),sK1)),k9_relat_1(sK0,sK1))
    | ~ v1_relat_1(sK0)
    | ~ r2_hidden(sK5(sK0,sK1,k9_relat_1(k7_relat_1(sK0,sK2),sK1)),k9_relat_1(sK0,sK1))
    | ~ spl12_28 ),
    inference(resolution,[],[f1729,f84])).

fof(f84,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK6(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK6(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t162_relat_1.p',d13_relat_1)).

fof(f1729,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK6(sK0,X2,sK5(sK0,sK1,k9_relat_1(k7_relat_1(sK0,sK2),sK1))),sK1)
        | ~ r2_hidden(sK5(sK0,sK1,k9_relat_1(k7_relat_1(sK0,sK2),sK1)),k9_relat_1(sK0,X2)) )
    | ~ spl12_28 ),
    inference(resolution,[],[f519,f113])).

fof(f113,plain,(
    ! [X21,X20] :
      ( r2_hidden(k4_tarski(sK6(sK0,X20,X21),X21),sK0)
      | ~ r2_hidden(X21,k9_relat_1(sK0,X20)) ) ),
    inference(resolution,[],[f46,f85])).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK6(X0,X1,X3),X3),X0)
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK6(X0,X1,X3),X3),X0)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f519,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK5(sK0,sK1,k9_relat_1(k7_relat_1(sK0,sK2),sK1))),sK0)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl12_28 ),
    inference(avatar_component_clause,[],[f518])).

fof(f518,plain,
    ( spl12_28
  <=> ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK5(sK0,sK1,k9_relat_1(k7_relat_1(sK0,sK2),sK1))),sK0)
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_28])])).

fof(f1695,plain,
    ( ~ spl12_26
    | ~ spl12_30 ),
    inference(avatar_contradiction_clause,[],[f1681])).

fof(f1681,plain,
    ( $false
    | ~ spl12_26
    | ~ spl12_30 ),
    inference(unit_resulting_resolution,[],[f521,f487,f550,f893,f415])).

fof(f415,plain,(
    ! [X14,X12,X15,X13] :
      ( ~ r2_hidden(k4_tarski(X12,X13),sK0)
      | ~ r2_hidden(X12,X14)
      | ~ r2_hidden(X12,X15)
      | r2_hidden(X13,k9_relat_1(k7_relat_1(sK0,X14),X15)) ) ),
    inference(subsumption_resolution,[],[f400,f104])).

fof(f400,plain,(
    ! [X14,X12,X15,X13] :
      ( ~ r2_hidden(k4_tarski(X12,X13),sK0)
      | ~ r2_hidden(X12,X14)
      | ~ v1_relat_1(k7_relat_1(sK0,X14))
      | ~ r2_hidden(X12,X15)
      | r2_hidden(X13,k9_relat_1(k7_relat_1(sK0,X14),X15)) ) ),
    inference(resolution,[],[f123,f83])).

fof(f83,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f123,plain,(
    ! [X6,X8,X7] :
      ( r2_hidden(k4_tarski(X7,X8),k7_relat_1(sK0,X6))
      | ~ r2_hidden(k4_tarski(X7,X8),sK0)
      | ~ r2_hidden(X7,X6) ) ),
    inference(subsumption_resolution,[],[f108,f104])).

fof(f108,plain,(
    ! [X6,X8,X7] :
      ( ~ v1_relat_1(k7_relat_1(sK0,X6))
      | ~ r2_hidden(X7,X6)
      | ~ r2_hidden(k4_tarski(X7,X8),sK0)
      | r2_hidden(k4_tarski(X7,X8),k7_relat_1(sK0,X6)) ) ),
    inference(resolution,[],[f46,f80])).

fof(f80,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | r2_hidden(k4_tarski(X3,X4),k7_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | r2_hidden(k4_tarski(X3,X4),X2)
      | k7_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t162_relat_1.p',d11_relat_1)).

fof(f893,plain,
    ( ~ r2_hidden(sK5(sK0,sK1,k9_relat_1(k7_relat_1(sK0,sK2),sK1)),k9_relat_1(k7_relat_1(sK0,sK2),sK1))
    | ~ spl12_26
    | ~ spl12_30 ),
    inference(subsumption_resolution,[],[f892,f91])).

fof(f91,plain,(
    ~ sQ11_eqProxy(k9_relat_1(sK0,sK1),k9_relat_1(k7_relat_1(sK0,sK2),sK1)) ),
    inference(equality_proxy_replacement,[],[f45,f90])).

fof(f90,plain,(
    ! [X1,X0] :
      ( sQ11_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ11_eqProxy])])).

fof(f45,plain,(
    k9_relat_1(sK0,sK1) != k9_relat_1(k7_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f892,plain,
    ( ~ r2_hidden(sK5(sK0,sK1,k9_relat_1(k7_relat_1(sK0,sK2),sK1)),k9_relat_1(k7_relat_1(sK0,sK2),sK1))
    | sQ11_eqProxy(k9_relat_1(sK0,sK1),k9_relat_1(k7_relat_1(sK0,sK2),sK1))
    | ~ spl12_26
    | ~ spl12_30 ),
    inference(subsumption_resolution,[],[f873,f487])).

fof(f873,plain,
    ( ~ r2_hidden(sK7(sK0,sK1,k9_relat_1(k7_relat_1(sK0,sK2),sK1)),sK1)
    | ~ r2_hidden(sK5(sK0,sK1,k9_relat_1(k7_relat_1(sK0,sK2),sK1)),k9_relat_1(k7_relat_1(sK0,sK2),sK1))
    | sQ11_eqProxy(k9_relat_1(sK0,sK1),k9_relat_1(k7_relat_1(sK0,sK2),sK1))
    | ~ spl12_30 ),
    inference(resolution,[],[f550,f122])).

fof(f122,plain,(
    ! [X39,X38,X40] :
      ( ~ r2_hidden(k4_tarski(X38,sK5(sK0,X39,X40)),sK0)
      | ~ r2_hidden(X38,X39)
      | ~ r2_hidden(sK5(sK0,X39,X40),X40)
      | sQ11_eqProxy(k9_relat_1(sK0,X39),X40) ) ),
    inference(resolution,[],[f46,f98])).

fof(f98,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,sK5(X0,X1,X2)),X0)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(sK5(X0,X1,X2),X2)
      | sQ11_eqProxy(k9_relat_1(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f55,f90])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,sK5(X0,X1,X2)),X0)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(sK5(X0,X1,X2),X2)
      | k9_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f550,plain,
    ( r2_hidden(k4_tarski(sK7(sK0,sK1,k9_relat_1(k7_relat_1(sK0,sK2),sK1)),sK5(sK0,sK1,k9_relat_1(k7_relat_1(sK0,sK2),sK1))),sK0)
    | ~ spl12_30 ),
    inference(avatar_component_clause,[],[f549])).

fof(f549,plain,
    ( spl12_30
  <=> r2_hidden(k4_tarski(sK7(sK0,sK1,k9_relat_1(k7_relat_1(sK0,sK2),sK1)),sK5(sK0,sK1,k9_relat_1(k7_relat_1(sK0,sK2),sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_30])])).

fof(f487,plain,
    ( r2_hidden(sK7(sK0,sK1,k9_relat_1(k7_relat_1(sK0,sK2),sK1)),sK1)
    | ~ spl12_26 ),
    inference(avatar_component_clause,[],[f486])).

fof(f486,plain,
    ( spl12_26
  <=> r2_hidden(sK7(sK0,sK1,k9_relat_1(k7_relat_1(sK0,sK2),sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_26])])).

fof(f521,plain,
    ( r2_hidden(sK7(sK0,sK1,k9_relat_1(k7_relat_1(sK0,sK2),sK1)),sK2)
    | ~ spl12_26 ),
    inference(resolution,[],[f487,f127])).

fof(f127,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f44,f71])).

fof(f44,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f551,plain,
    ( spl12_24
    | spl12_30 ),
    inference(avatar_split_clause,[],[f139,f549,f480])).

fof(f139,plain,
    ( r2_hidden(k4_tarski(sK7(sK0,sK1,k9_relat_1(k7_relat_1(sK0,sK2),sK1)),sK5(sK0,sK1,k9_relat_1(k7_relat_1(sK0,sK2),sK1))),sK0)
    | r2_hidden(sK5(sK0,sK1,k9_relat_1(k7_relat_1(sK0,sK2),sK1)),k9_relat_1(k7_relat_1(sK0,sK2),sK1)) ),
    inference(subsumption_resolution,[],[f132,f46])).

fof(f132,plain,
    ( ~ v1_relat_1(sK0)
    | r2_hidden(k4_tarski(sK7(sK0,sK1,k9_relat_1(k7_relat_1(sK0,sK2),sK1)),sK5(sK0,sK1,k9_relat_1(k7_relat_1(sK0,sK2),sK1))),sK0)
    | r2_hidden(sK5(sK0,sK1,k9_relat_1(k7_relat_1(sK0,sK2),sK1)),k9_relat_1(k7_relat_1(sK0,sK2),sK1)) ),
    inference(resolution,[],[f91,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK7(X0,X1,X2),sK5(X0,X1,X2)),X0)
      | r2_hidden(sK5(X0,X1,X2),X2)
      | sQ11_eqProxy(k9_relat_1(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f56,f90])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK7(X0,X1,X2),sK5(X0,X1,X2)),X0)
      | r2_hidden(sK5(X0,X1,X2),X2)
      | k9_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f520,plain,
    ( ~ spl12_25
    | spl12_28 ),
    inference(avatar_split_clause,[],[f138,f518,f477])).

fof(f477,plain,
    ( spl12_25
  <=> ~ r2_hidden(sK5(sK0,sK1,k9_relat_1(k7_relat_1(sK0,sK2),sK1)),k9_relat_1(k7_relat_1(sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_25])])).

fof(f138,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(X0,sK5(sK0,sK1,k9_relat_1(k7_relat_1(sK0,sK2),sK1))),sK0)
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(sK5(sK0,sK1,k9_relat_1(k7_relat_1(sK0,sK2),sK1)),k9_relat_1(k7_relat_1(sK0,sK2),sK1)) ) ),
    inference(subsumption_resolution,[],[f131,f46])).

fof(f131,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK0)
      | ~ r2_hidden(k4_tarski(X0,sK5(sK0,sK1,k9_relat_1(k7_relat_1(sK0,sK2),sK1))),sK0)
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(sK5(sK0,sK1,k9_relat_1(k7_relat_1(sK0,sK2),sK1)),k9_relat_1(k7_relat_1(sK0,sK2),sK1)) ) ),
    inference(resolution,[],[f91,f98])).

fof(f488,plain,
    ( spl12_24
    | spl12_26 ),
    inference(avatar_split_clause,[],[f140,f486,f480])).

fof(f140,plain,
    ( r2_hidden(sK7(sK0,sK1,k9_relat_1(k7_relat_1(sK0,sK2),sK1)),sK1)
    | r2_hidden(sK5(sK0,sK1,k9_relat_1(k7_relat_1(sK0,sK2),sK1)),k9_relat_1(k7_relat_1(sK0,sK2),sK1)) ),
    inference(subsumption_resolution,[],[f133,f46])).

fof(f133,plain,
    ( ~ v1_relat_1(sK0)
    | r2_hidden(sK7(sK0,sK1,k9_relat_1(k7_relat_1(sK0,sK2),sK1)),sK1)
    | r2_hidden(sK5(sK0,sK1,k9_relat_1(k7_relat_1(sK0,sK2),sK1)),k9_relat_1(k7_relat_1(sK0,sK2),sK1)) ),
    inference(resolution,[],[f91,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK7(X0,X1,X2),X1)
      | r2_hidden(sK5(X0,X1,X2),X2)
      | sQ11_eqProxy(k9_relat_1(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f57,f90])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK7(X0,X1,X2),X1)
      | r2_hidden(sK5(X0,X1,X2),X2)
      | k9_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
