%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t92_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:16 EDT 2019

% Result     : Theorem 8.92s
% Output     : Refutation 8.92s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 503 expanded)
%              Number of leaves         :   21 ( 119 expanded)
%              Depth                    :   26
%              Number of atoms          :  503 (1735 expanded)
%              Number of equality atoms :  113 ( 387 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f52195,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f228,f239,f258,f334,f343,f841,f3136,f3167,f52069])).

fof(f52069,plain,
    ( ~ spl14_4
    | ~ spl14_10
    | ~ spl14_16
    | ~ spl14_18
    | ~ spl14_40
    | ~ spl14_112 ),
    inference(avatar_contradiction_clause,[],[f52049])).

fof(f52049,plain,
    ( $false
    | ~ spl14_4
    | ~ spl14_10
    | ~ spl14_16
    | ~ spl14_18
    | ~ spl14_40
    | ~ spl14_112 ),
    inference(unit_resulting_resolution,[],[f55,f2097,f30740,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | ~ r2_hidden(sK2(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t92_mcart_1.p',t2_tarski)).

fof(f30740,plain,
    ( r2_hidden(sK2(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | ~ spl14_112 ),
    inference(backward_demodulation,[],[f30452,f16524])).

fof(f16524,plain,
    ( r2_hidden(k2_mcart_1(k4_tarski(sK1,sK2(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)))),a_2_0_mcart_1(sK0,sK1))
    | ~ spl14_112 ),
    inference(forward_demodulation,[],[f3247,f14752])).

fof(f14752,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(equality_resolution,[],[f14665])).

fof(f14665,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | k1_mcart_1(k4_tarski(X0,X1)) = X2 ) ),
    inference(equality_factoring,[],[f14595])).

fof(f14595,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(k4_tarski(X0,X1)) = X0
      | k1_mcart_1(k4_tarski(X0,X1)) = X2 ) ),
    inference(duplicate_literal_removal,[],[f14589])).

fof(f14589,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(k4_tarski(X0,X1)) = X0
      | k1_mcart_1(k4_tarski(X0,X1)) = X2
      | k1_mcart_1(k4_tarski(X0,X1)) = X2 ) ),
    inference(superposition,[],[f10320,f91])).

fof(f91,plain,(
    ! [X2,X3,X1] :
      ( k4_tarski(X1,X2) = k4_tarski(sK5(k4_tarski(X1,X2),X3),sK6(k4_tarski(X1,X2),X3))
      | k1_mcart_1(k4_tarski(X1,X2)) = X3 ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X1,X2) != X0
      | k4_tarski(sK5(X0,X3),sK6(X0,X3)) = X0
      | k1_mcart_1(X0) = X3 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X3] :
          ( k1_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( X3 = X4
              | k4_tarski(X4,X5) != X0 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X3] :
          ( k1_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( k4_tarski(X4,X5) = X0
             => X3 = X4 ) ) ) ),
    inference(rectify,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X1] :
          ( k1_mcart_1(X0) = X1
        <=> ! [X2,X3] :
              ( k4_tarski(X2,X3) = X0
             => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t92_mcart_1.p',d1_mcart_1)).

fof(f10320,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(k4_tarski(sK5(k4_tarski(X0,X1),X2),sK6(k4_tarski(X0,X1),X2))) = X0
      | k1_mcart_1(k4_tarski(X0,X1)) = X2 ) ),
    inference(equality_resolution,[],[f8727])).

fof(f8727,plain,(
    ! [X6,X4,X8,X7,X5] :
      ( k4_tarski(X4,X5) != k4_tarski(X7,X8)
      | k1_mcart_1(k4_tarski(sK5(k4_tarski(X4,X5),X6),sK6(k4_tarski(X4,X5),X6))) = X7
      | k1_mcart_1(k4_tarski(X4,X5)) = X6 ) ),
    inference(superposition,[],[f93,f91])).

fof(f93,plain,(
    ! [X4,X2,X5,X1] :
      ( k4_tarski(X1,X2) != k4_tarski(X4,X5)
      | k1_mcart_1(k4_tarski(X1,X2)) = X4 ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X4,X2,X5,X3,X1] :
      ( k4_tarski(X1,X2) != k4_tarski(X4,X5)
      | X3 = X4
      | k1_mcart_1(k4_tarski(X1,X2)) != X3 ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k4_tarski(X1,X2) != X0
      | k4_tarski(X4,X5) != X0
      | X3 = X4
      | k1_mcart_1(X0) != X3 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f3247,plain,
    ( r2_hidden(k2_mcart_1(k4_tarski(sK1,sK2(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)))),a_2_0_mcart_1(sK0,k1_mcart_1(k4_tarski(sK1,sK2(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1))))))
    | ~ spl14_112 ),
    inference(unit_resulting_resolution,[],[f53,f54,f3221,f89])).

fof(f89,plain,(
    ! [X3,X1] :
      ( r2_hidden(k2_mcart_1(X3),a_2_0_mcart_1(X1,k1_mcart_1(X3)))
      | ~ v1_relat_1(X1)
      | ~ m1_subset_1(X3,X1)
      | v1_xboole_0(X1) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X2,X3,X1] :
      ( v1_xboole_0(X1)
      | ~ v1_relat_1(X1)
      | ~ m1_subset_1(X3,X1)
      | k1_mcart_1(X3) != X2
      | r2_hidden(k2_mcart_1(X3),a_2_0_mcart_1(X1,X2)) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_xboole_0(X1)
      | ~ v1_relat_1(X1)
      | ~ m1_subset_1(X3,X1)
      | k2_mcart_1(X3) != X0
      | k1_mcart_1(X3) != X2
      | r2_hidden(X0,a_2_0_mcart_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_mcart_1(X1,X2))
      <=> ? [X3] :
            ( k1_mcart_1(X3) = X2
            & k2_mcart_1(X3) = X0
            & m1_subset_1(X3,X1) ) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_mcart_1(X1,X2))
      <=> ? [X3] :
            ( k1_mcart_1(X3) = X2
            & k2_mcart_1(X3) = X0
            & m1_subset_1(X3,X1) ) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_relat_1(X1)
        & ~ v1_xboole_0(X1) )
     => ( r2_hidden(X0,a_2_0_mcart_1(X1,X2))
      <=> ? [X3] :
            ( k1_mcart_1(X3) = X2
            & k2_mcart_1(X3) = X0
            & m1_subset_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t92_mcart_1.p',fraenkel_a_2_0_mcart_1)).

fof(f3221,plain,
    ( m1_subset_1(k4_tarski(sK1,sK2(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1))),sK0)
    | ~ spl14_112 ),
    inference(unit_resulting_resolution,[],[f3129,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t92_mcart_1.p',t1_subset)).

fof(f3129,plain,
    ( r2_hidden(k4_tarski(sK1,sK2(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1))),sK0)
    | ~ spl14_112 ),
    inference(avatar_component_clause,[],[f3128])).

fof(f3128,plain,
    ( spl14_112
  <=> r2_hidden(k4_tarski(sK1,sK2(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_112])])).

fof(f54,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] : k11_relat_1(X0,X1) != a_2_0_mcart_1(X0,X1)
      & v1_relat_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] : k11_relat_1(X0,X1) != a_2_0_mcart_1(X0,X1)
      & v1_relat_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_relat_1(X0)
          & ~ v1_xboole_0(X0) )
       => ! [X1] : k11_relat_1(X0,X1) = a_2_0_mcart_1(X0,X1) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] : k11_relat_1(X0,X1) = a_2_0_mcart_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t92_mcart_1.p',t92_mcart_1)).

fof(f53,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f30452,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X4,X2,X5,X1] :
      ( k4_tarski(X1,X2) != k4_tarski(X4,X5)
      | k2_mcart_1(k4_tarski(X1,X2)) = X5 ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X4,X2,X5,X3,X1] :
      ( k4_tarski(X1,X2) != k4_tarski(X4,X5)
      | X3 = X5
      | k2_mcart_1(k4_tarski(X1,X2)) != X3 ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k4_tarski(X1,X2) != X0
      | k4_tarski(X4,X5) != X0
      | X3 = X5
      | k2_mcart_1(X0) != X3 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X3] :
          ( k2_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( X3 = X5
              | k4_tarski(X4,X5) != X0 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X3] :
          ( k2_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( k4_tarski(X4,X5) = X0
             => X3 = X5 ) ) ) ),
    inference(rectify,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X1] :
          ( k2_mcart_1(X0) = X1
        <=> ! [X2,X3] :
              ( k4_tarski(X2,X3) = X0
             => X1 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t92_mcart_1.p',d2_mcart_1)).

fof(f2097,plain,
    ( r2_hidden(sK2(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)),k11_relat_1(sK0,sK1))
    | ~ spl14_4
    | ~ spl14_10
    | ~ spl14_16
    | ~ spl14_18
    | ~ spl14_40 ),
    inference(unit_resulting_resolution,[],[f55,f2096])).

fof(f2096,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(k11_relat_1(sK0,X0),a_2_0_mcart_1(sK0,X0)),k11_relat_1(sK0,X0))
        | k11_relat_1(sK0,X0) = a_2_0_mcart_1(sK0,X0) )
    | ~ spl14_4
    | ~ spl14_10
    | ~ spl14_16
    | ~ spl14_18
    | ~ spl14_40 ),
    inference(factoring,[],[f1697])).

fof(f1697,plain,
    ( ! [X6,X5] :
        ( r2_hidden(sK2(X5,a_2_0_mcart_1(sK0,X6)),k11_relat_1(sK0,X6))
        | r2_hidden(sK2(X5,a_2_0_mcart_1(sK0,X6)),X5)
        | a_2_0_mcart_1(sK0,X6) = X5 )
    | ~ spl14_4
    | ~ spl14_10
    | ~ spl14_16
    | ~ spl14_18
    | ~ spl14_40 ),
    inference(resolution,[],[f1686,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r2_hidden(sK2(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f1686,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,a_2_0_mcart_1(sK0,X1))
        | r2_hidden(X0,k11_relat_1(sK0,X1)) )
    | ~ spl14_4
    | ~ spl14_10
    | ~ spl14_16
    | ~ spl14_18
    | ~ spl14_40 ),
    inference(duplicate_literal_removal,[],[f1685])).

fof(f1685,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,k11_relat_1(sK0,X1))
        | ~ r2_hidden(X0,a_2_0_mcart_1(sK0,X1))
        | ~ r2_hidden(X0,a_2_0_mcart_1(sK0,X1)) )
    | ~ spl14_4
    | ~ spl14_10
    | ~ spl14_16
    | ~ spl14_18
    | ~ spl14_40 ),
    inference(superposition,[],[f1669,f333])).

fof(f333,plain,
    ( ! [X2,X3] :
        ( k2_mcart_1(sK3(X2,sK0,X3)) = X2
        | ~ r2_hidden(X2,a_2_0_mcart_1(sK0,X3)) )
    | ~ spl14_16 ),
    inference(avatar_component_clause,[],[f332])).

fof(f332,plain,
    ( spl14_16
  <=> ! [X3,X2] :
        ( k2_mcart_1(sK3(X2,sK0,X3)) = X2
        | ~ r2_hidden(X2,a_2_0_mcart_1(sK0,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_16])])).

fof(f1669,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k2_mcart_1(sK3(X0,sK0,X1)),k11_relat_1(sK0,X1))
        | ~ r2_hidden(X0,a_2_0_mcart_1(sK0,X1)) )
    | ~ spl14_4
    | ~ spl14_10
    | ~ spl14_16
    | ~ spl14_18
    | ~ spl14_40 ),
    inference(resolution,[],[f1551,f103])).

fof(f103,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t92_mcart_1.p',d1_tarski)).

fof(f1551,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,k1_tarski(X0))
        | r2_hidden(k2_mcart_1(sK3(X1,sK0,X2)),k11_relat_1(sK0,X0))
        | ~ r2_hidden(X1,a_2_0_mcart_1(sK0,X2)) )
    | ~ spl14_4
    | ~ spl14_10
    | ~ spl14_16
    | ~ spl14_18
    | ~ spl14_40 ),
    inference(superposition,[],[f1492,f105])).

fof(f105,plain,(
    ! [X0] : k11_relat_1(sK0,X0) = k9_relat_1(sK0,k1_tarski(X0)) ),
    inference(unit_resulting_resolution,[],[f54,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t92_mcart_1.p',d16_relat_1)).

fof(f1492,plain,
    ( ! [X6,X8,X7] :
        ( r2_hidden(k2_mcart_1(sK3(X6,sK0,X7)),k9_relat_1(sK0,X8))
        | ~ r2_hidden(X7,X8)
        | ~ r2_hidden(X6,a_2_0_mcart_1(sK0,X7)) )
    | ~ spl14_4
    | ~ spl14_10
    | ~ spl14_16
    | ~ spl14_18
    | ~ spl14_40 ),
    inference(resolution,[],[f1479,f845])).

fof(f845,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k2_mcart_1(sK3(X0,sK0,X1)),a_2_0_mcart_1(sK0,X1))
        | ~ r2_hidden(X0,a_2_0_mcart_1(sK0,X1)) )
    | ~ spl14_4
    | ~ spl14_40 ),
    inference(duplicate_literal_removal,[],[f842])).

fof(f842,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,a_2_0_mcart_1(sK0,X1))
        | r2_hidden(k2_mcart_1(sK3(X0,sK0,X1)),a_2_0_mcart_1(sK0,X1))
        | ~ r2_hidden(X0,a_2_0_mcart_1(sK0,X1)) )
    | ~ spl14_4
    | ~ spl14_40 ),
    inference(resolution,[],[f840,f221])).

fof(f221,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK3(X0,sK0,X1),sK0)
        | ~ r2_hidden(X0,a_2_0_mcart_1(sK0,X1)) )
    | ~ spl14_4 ),
    inference(avatar_component_clause,[],[f220])).

fof(f220,plain,
    ( spl14_4
  <=> ! [X1,X0] :
        ( m1_subset_1(sK3(X0,sK0,X1),sK0)
        | ~ r2_hidden(X0,a_2_0_mcart_1(sK0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_4])])).

fof(f840,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK3(X2,sK0,X3),sK0)
        | ~ r2_hidden(X2,a_2_0_mcart_1(sK0,X3))
        | r2_hidden(k2_mcart_1(sK3(X2,sK0,X3)),a_2_0_mcart_1(sK0,X3)) )
    | ~ spl14_40 ),
    inference(avatar_component_clause,[],[f839])).

fof(f839,plain,
    ( spl14_40
  <=> ! [X3,X2] :
        ( r2_hidden(k2_mcart_1(sK3(X2,sK0,X3)),a_2_0_mcart_1(sK0,X3))
        | ~ r2_hidden(X2,a_2_0_mcart_1(sK0,X3))
        | ~ m1_subset_1(sK3(X2,sK0,X3),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_40])])).

fof(f1479,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,a_2_0_mcart_1(sK0,X1))
        | r2_hidden(X0,k9_relat_1(sK0,X2))
        | ~ r2_hidden(X1,X2) )
    | ~ spl14_10
    | ~ spl14_16
    | ~ spl14_18 ),
    inference(duplicate_literal_removal,[],[f1478])).

fof(f1478,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X1,X2)
        | r2_hidden(X0,k9_relat_1(sK0,X2))
        | ~ r2_hidden(X0,a_2_0_mcart_1(sK0,X1))
        | ~ r2_hidden(X0,a_2_0_mcart_1(sK0,X1)) )
    | ~ spl14_10
    | ~ spl14_16
    | ~ spl14_18 ),
    inference(superposition,[],[f1459,f342])).

fof(f342,plain,
    ( ! [X4,X5] :
        ( k1_mcart_1(sK3(X4,sK0,X5)) = X5
        | ~ r2_hidden(X4,a_2_0_mcart_1(sK0,X5)) )
    | ~ spl14_18 ),
    inference(avatar_component_clause,[],[f341])).

fof(f341,plain,
    ( spl14_18
  <=> ! [X5,X4] :
        ( k1_mcart_1(sK3(X4,sK0,X5)) = X5
        | ~ r2_hidden(X4,a_2_0_mcart_1(sK0,X5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_18])])).

fof(f1459,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k1_mcart_1(sK3(X0,sK0,X1)),X2)
        | r2_hidden(X0,k9_relat_1(sK0,X2))
        | ~ r2_hidden(X0,a_2_0_mcart_1(sK0,X1)) )
    | ~ spl14_10
    | ~ spl14_16 ),
    inference(duplicate_literal_removal,[],[f1456])).

fof(f1456,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k1_mcart_1(sK3(X0,sK0,X1)),X2)
        | r2_hidden(X0,k9_relat_1(sK0,X2))
        | ~ r2_hidden(X0,a_2_0_mcart_1(sK0,X1))
        | ~ r2_hidden(X0,a_2_0_mcart_1(sK0,X1)) )
    | ~ spl14_10
    | ~ spl14_16 ),
    inference(resolution,[],[f442,f257])).

fof(f257,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(X0,sK0,X1),sK0)
        | ~ r2_hidden(X0,a_2_0_mcart_1(sK0,X1)) )
    | ~ spl14_10 ),
    inference(avatar_component_clause,[],[f256])).

fof(f256,plain,
    ( spl14_10
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,a_2_0_mcart_1(sK0,X1))
        | r2_hidden(sK3(X0,sK0,X1),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_10])])).

fof(f442,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK3(X0,sK0,X1),sK0)
        | ~ r2_hidden(k1_mcart_1(sK3(X0,sK0,X1)),X2)
        | r2_hidden(X0,k9_relat_1(sK0,X2))
        | ~ r2_hidden(X0,a_2_0_mcart_1(sK0,X1)) )
    | ~ spl14_16 ),
    inference(superposition,[],[f434,f333])).

fof(f434,plain,(
    ! [X2,X3] :
      ( r2_hidden(k2_mcart_1(X2),k9_relat_1(sK0,X3))
      | ~ r2_hidden(k1_mcart_1(X2),X3)
      | ~ r2_hidden(X2,sK0) ) ),
    inference(duplicate_literal_removal,[],[f433])).

fof(f433,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k1_mcart_1(X2),X3)
      | r2_hidden(k2_mcart_1(X2),k9_relat_1(sK0,X3))
      | ~ r2_hidden(X2,sK0)
      | ~ r2_hidden(X2,sK0) ) ),
    inference(resolution,[],[f249,f54])).

fof(f249,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k1_mcart_1(X0),X1)
      | r2_hidden(k2_mcart_1(X0),k9_relat_1(sK0,X1))
      | ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(superposition,[],[f113,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t92_mcart_1.p',t23_mcart_1)).

fof(f113,plain,(
    ! [X12,X13,X11] :
      ( ~ r2_hidden(k4_tarski(X11,X12),sK0)
      | ~ r2_hidden(X11,X13)
      | r2_hidden(X12,k9_relat_1(sK0,X13)) ) ),
    inference(resolution,[],[f54,f98])).

fof(f98,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t92_mcart_1.p',d13_relat_1)).

fof(f55,plain,(
    k11_relat_1(sK0,sK1) != a_2_0_mcart_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f3167,plain,
    ( ~ spl14_4
    | ~ spl14_10
    | ~ spl14_16
    | ~ spl14_18
    | ~ spl14_40
    | spl14_115 ),
    inference(avatar_contradiction_clause,[],[f3157])).

fof(f3157,plain,
    ( $false
    | ~ spl14_4
    | ~ spl14_10
    | ~ spl14_16
    | ~ spl14_18
    | ~ spl14_40
    | ~ spl14_115 ),
    inference(unit_resulting_resolution,[],[f2104,f2105,f3135,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t92_mcart_1.p',t2_subset)).

fof(f3135,plain,
    ( ~ r2_hidden(sK2(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)),k11_relat_1(sK0,sK1))
    | ~ spl14_115 ),
    inference(avatar_component_clause,[],[f3134])).

fof(f3134,plain,
    ( spl14_115
  <=> ~ r2_hidden(sK2(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)),k11_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_115])])).

fof(f2105,plain,
    ( m1_subset_1(sK2(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)),k11_relat_1(sK0,sK1))
    | ~ spl14_4
    | ~ spl14_10
    | ~ spl14_16
    | ~ spl14_18
    | ~ spl14_40 ),
    inference(unit_resulting_resolution,[],[f2097,f69])).

fof(f2104,plain,
    ( ~ v1_xboole_0(k11_relat_1(sK0,sK1))
    | ~ spl14_4
    | ~ spl14_10
    | ~ spl14_16
    | ~ spl14_18
    | ~ spl14_40 ),
    inference(unit_resulting_resolution,[],[f2097,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t92_mcart_1.p',t7_boole)).

fof(f3136,plain,
    ( spl14_112
    | ~ spl14_115
    | ~ spl14_4
    | ~ spl14_10
    | ~ spl14_16
    | ~ spl14_18
    | ~ spl14_40 ),
    inference(avatar_split_clause,[],[f2184,f839,f341,f332,f256,f220,f3134,f3128])).

fof(f2184,plain,
    ( ~ r2_hidden(sK2(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)),k11_relat_1(sK0,sK1))
    | r2_hidden(k4_tarski(sK1,sK2(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1))),sK0)
    | ~ spl14_4
    | ~ spl14_10
    | ~ spl14_16
    | ~ spl14_18
    | ~ spl14_40 ),
    inference(forward_demodulation,[],[f2178,f105])).

fof(f2178,plain,
    ( r2_hidden(k4_tarski(sK1,sK2(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1))),sK0)
    | ~ r2_hidden(sK2(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)),k9_relat_1(sK0,k1_tarski(sK1)))
    | ~ spl14_4
    | ~ spl14_10
    | ~ spl14_16
    | ~ spl14_18
    | ~ spl14_40 ),
    inference(superposition,[],[f115,f2103])).

fof(f2103,plain,
    ( sK1 = sK11(sK0,k1_tarski(sK1),sK2(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)))
    | ~ spl14_4
    | ~ spl14_10
    | ~ spl14_16
    | ~ spl14_18
    | ~ spl14_40 ),
    inference(unit_resulting_resolution,[],[f2097,f151])).

fof(f151,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k11_relat_1(sK0,X3))
      | sK11(sK0,k1_tarski(X3),X2) = X3 ) ),
    inference(forward_demodulation,[],[f150,f105])).

fof(f150,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k9_relat_1(sK0,k1_tarski(X3)))
      | sK11(sK0,k1_tarski(X3),X2) = X3 ) ),
    inference(resolution,[],[f114,f101])).

fof(f101,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f114,plain,(
    ! [X14,X15] :
      ( r2_hidden(sK11(sK0,X14,X15),X14)
      | ~ r2_hidden(X15,k9_relat_1(sK0,X14)) ) ),
    inference(resolution,[],[f54,f99])).

fof(f99,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK11(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK11(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f115,plain,(
    ! [X17,X16] :
      ( r2_hidden(k4_tarski(sK11(sK0,X16,X17),X17),sK0)
      | ~ r2_hidden(X17,k9_relat_1(sK0,X16)) ) ),
    inference(resolution,[],[f54,f100])).

fof(f100,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK11(X0,X1,X3),X3),X0)
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK11(X0,X1,X3),X3),X0)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f841,plain,
    ( spl14_6
    | spl14_40
    | ~ spl14_18 ),
    inference(avatar_split_clause,[],[f653,f341,f839,f226])).

fof(f226,plain,
    ( spl14_6
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_6])])).

fof(f653,plain,
    ( ! [X2,X3] :
        ( r2_hidden(k2_mcart_1(sK3(X2,sK0,X3)),a_2_0_mcart_1(sK0,X3))
        | ~ m1_subset_1(sK3(X2,sK0,X3),sK0)
        | v1_xboole_0(sK0)
        | ~ r2_hidden(X2,a_2_0_mcart_1(sK0,X3)) )
    | ~ spl14_18 ),
    inference(resolution,[],[f347,f54])).

fof(f347,plain,
    ( ! [X4,X5,X3] :
        ( ~ v1_relat_1(X5)
        | r2_hidden(k2_mcart_1(sK3(X3,sK0,X4)),a_2_0_mcart_1(X5,X4))
        | ~ m1_subset_1(sK3(X3,sK0,X4),X5)
        | v1_xboole_0(X5)
        | ~ r2_hidden(X3,a_2_0_mcart_1(sK0,X4)) )
    | ~ spl14_18 ),
    inference(superposition,[],[f89,f342])).

fof(f343,plain,
    ( spl14_18
    | spl14_6 ),
    inference(avatar_split_clause,[],[f109,f226,f341])).

fof(f109,plain,(
    ! [X4,X5] :
      ( v1_xboole_0(sK0)
      | k1_mcart_1(sK3(X4,sK0,X5)) = X5
      | ~ r2_hidden(X4,a_2_0_mcart_1(sK0,X5)) ) ),
    inference(resolution,[],[f54,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | v1_xboole_0(X1)
      | k1_mcart_1(sK3(X0,X1,X2)) = X2
      | ~ r2_hidden(X0,a_2_0_mcart_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f334,plain,
    ( spl14_16
    | spl14_6 ),
    inference(avatar_split_clause,[],[f108,f226,f332])).

fof(f108,plain,(
    ! [X2,X3] :
      ( v1_xboole_0(sK0)
      | k2_mcart_1(sK3(X2,sK0,X3)) = X2
      | ~ r2_hidden(X2,a_2_0_mcart_1(sK0,X3)) ) ),
    inference(resolution,[],[f54,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | v1_xboole_0(X1)
      | k2_mcart_1(sK3(X0,X1,X2)) = X0
      | ~ r2_hidden(X0,a_2_0_mcart_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f258,plain,
    ( spl14_6
    | spl14_10
    | ~ spl14_4 ),
    inference(avatar_split_clause,[],[f242,f220,f256,f226])).

fof(f242,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,a_2_0_mcart_1(sK0,X1))
        | v1_xboole_0(sK0)
        | r2_hidden(sK3(X0,sK0,X1),sK0) )
    | ~ spl14_4 ),
    inference(resolution,[],[f221,f68])).

fof(f239,plain,(
    ~ spl14_6 ),
    inference(avatar_contradiction_clause,[],[f231])).

fof(f231,plain,
    ( $false
    | ~ spl14_6 ),
    inference(unit_resulting_resolution,[],[f104,f227,f67])).

fof(f227,plain,
    ( v1_xboole_0(sK0)
    | ~ spl14_6 ),
    inference(avatar_component_clause,[],[f226])).

fof(f104,plain,(
    r2_hidden(sK9(sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f77,f53,f68])).

fof(f77,plain,(
    ! [X0] : m1_subset_1(sK9(X0),X0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t92_mcart_1.p',existence_m1_subset_1)).

fof(f228,plain,
    ( spl14_4
    | spl14_6 ),
    inference(avatar_split_clause,[],[f107,f226,f220])).

fof(f107,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(sK0)
      | m1_subset_1(sK3(X0,sK0,X1),sK0)
      | ~ r2_hidden(X0,a_2_0_mcart_1(sK0,X1)) ) ),
    inference(resolution,[],[f54,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | v1_xboole_0(X1)
      | m1_subset_1(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(X0,a_2_0_mcart_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
