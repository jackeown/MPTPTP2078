%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t167_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:19 EDT 2019

% Result     : Theorem 0.97s
% Output     : Refutation 0.97s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 620 expanded)
%              Number of leaves         :   33 ( 209 expanded)
%              Depth                    :   16
%              Number of atoms          :  652 (2040 expanded)
%              Number of equality atoms :  107 ( 357 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2911,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f82,f89,f231,f250,f295,f297,f1467,f1573,f1582,f1585,f1613,f1618,f1701,f1721,f1782,f1801,f2034,f2123,f2809,f2820,f2845,f2884,f2910])).

fof(f2910,plain,
    ( spl7_5
    | ~ spl7_40 ),
    inference(avatar_contradiction_clause,[],[f2909])).

fof(f2909,plain,
    ( $false
    | ~ spl7_5
    | ~ spl7_40 ),
    inference(subsumption_resolution,[],[f2908,f88])).

fof(f88,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl7_5
  <=> ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f2908,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))
    | ~ spl7_40 ),
    inference(subsumption_resolution,[],[f2898,f68])).

fof(f68,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t167_funct_1.p',d1_tarski)).

fof(f2898,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK0),k1_tarski(k1_funct_1(sK1,sK0)))
    | r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))
    | ~ spl7_40 ),
    inference(superposition,[],[f46,f2883])).

fof(f2883,plain,
    ( k1_funct_1(sK1,sK0) = sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))
    | ~ spl7_40 ),
    inference(avatar_component_clause,[],[f2882])).

fof(f2882,plain,
    ( spl7_40
  <=> k1_funct_1(sK1,sK0) = sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t167_funct_1.p',d3_tarski)).

fof(f2884,plain,
    ( spl7_40
    | ~ spl7_0
    | ~ spl7_6
    | ~ spl7_12
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f2719,f1571,f1465,f214,f73,f2882])).

fof(f73,plain,
    ( spl7_0
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_0])])).

fof(f214,plain,
    ( spl7_6
  <=> v1_funct_1(k7_relat_1(sK1,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f1465,plain,
    ( spl7_12
  <=> k1_funct_1(sK1,sK4(k7_relat_1(sK1,k1_tarski(sK0)),sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))))) = sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f1571,plain,
    ( spl7_16
  <=> r2_hidden(sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))),k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f2719,plain,
    ( k1_funct_1(sK1,sK0) = sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))
    | ~ spl7_0
    | ~ spl7_6
    | ~ spl7_12
    | ~ spl7_16 ),
    inference(backward_demodulation,[],[f2717,f1466])).

fof(f1466,plain,
    ( k1_funct_1(sK1,sK4(k7_relat_1(sK1,k1_tarski(sK0)),sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))))) = sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f1465])).

fof(f2717,plain,
    ( sK0 = sK4(k7_relat_1(sK1,k1_tarski(sK0)),sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))))
    | ~ spl7_0
    | ~ spl7_6
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f2716,f74])).

fof(f74,plain,
    ( v1_relat_1(sK1)
    | ~ spl7_0 ),
    inference(avatar_component_clause,[],[f73])).

fof(f2716,plain,
    ( sK0 = sK4(k7_relat_1(sK1,k1_tarski(sK0)),sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))))
    | ~ v1_relat_1(sK1)
    | ~ spl7_6
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f2678,f215])).

fof(f215,plain,
    ( v1_funct_1(k7_relat_1(sK1,k1_tarski(sK0)))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f214])).

fof(f2678,plain,
    ( ~ v1_funct_1(k7_relat_1(sK1,k1_tarski(sK0)))
    | sK0 = sK4(k7_relat_1(sK1,k1_tarski(sK0)),sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))))
    | ~ v1_relat_1(sK1)
    | ~ spl7_16 ),
    inference(resolution,[],[f436,f1572])).

fof(f1572,plain,
    ( r2_hidden(sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))),k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f1571])).

fof(f436,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_relat_1(k7_relat_1(X1,k1_tarski(X2))))
      | ~ v1_funct_1(k7_relat_1(X1,k1_tarski(X2)))
      | sK4(k7_relat_1(X1,k1_tarski(X2)),X0) = X2
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f434,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t167_funct_1.p',dt_k7_relat_1)).

fof(f434,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_relat_1(k7_relat_1(X1,k1_tarski(X2))))
      | ~ v1_funct_1(k7_relat_1(X1,k1_tarski(X2)))
      | ~ v1_relat_1(k7_relat_1(X1,k1_tarski(X2)))
      | sK4(k7_relat_1(X1,k1_tarski(X2)),X0) = X2
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f171,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t167_funct_1.p',t87_relat_1)).

fof(f171,plain,(
    ! [X6,X4,X5] :
      ( ~ r1_tarski(k1_relat_1(X4),k1_tarski(X6))
      | ~ r2_hidden(X5,k2_relat_1(X4))
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | sK4(X4,X5) = X6 ) ),
    inference(resolution,[],[f103,f66])).

fof(f66,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1),X2)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ r1_tarski(k1_relat_1(X0),X2) ) ),
    inference(resolution,[],[f65,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f65,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK4(X0,X2),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK4(X0,X2),k1_relat_1(X0))
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t167_funct_1.p',d5_funct_1)).

fof(f2845,plain,
    ( spl7_38
    | ~ spl7_0
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f2753,f1571,f1465,f229,f214,f73,f2843])).

fof(f2843,plain,
    ( spl7_38
  <=> r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f229,plain,
    ( spl7_10
  <=> k1_funct_1(k7_relat_1(sK1,k1_tarski(sK0)),sK4(k7_relat_1(sK1,k1_tarski(sK0)),sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))))) = sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f2753,plain,
    ( r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
    | ~ spl7_0
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_16 ),
    inference(backward_demodulation,[],[f2752,f2726])).

fof(f2726,plain,
    ( r2_hidden(k1_funct_1(k7_relat_1(sK1,k1_tarski(sK0)),sK0),k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
    | ~ spl7_0
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_16 ),
    inference(backward_demodulation,[],[f2718,f1572])).

fof(f2718,plain,
    ( k1_funct_1(k7_relat_1(sK1,k1_tarski(sK0)),sK0) = sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))
    | ~ spl7_0
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_16 ),
    inference(backward_demodulation,[],[f2717,f230])).

fof(f230,plain,
    ( k1_funct_1(k7_relat_1(sK1,k1_tarski(sK0)),sK4(k7_relat_1(sK1,k1_tarski(sK0)),sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))))) = sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f229])).

fof(f2752,plain,
    ( k1_funct_1(sK1,sK0) = k1_funct_1(k7_relat_1(sK1,k1_tarski(sK0)),sK0)
    | ~ spl7_0
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_16 ),
    inference(backward_demodulation,[],[f2719,f2718])).

fof(f2820,plain,
    ( spl7_36
    | ~ spl7_0
    | ~ spl7_6
    | ~ spl7_14
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f2723,f1571,f1562,f214,f73,f2818])).

fof(f2818,plain,
    ( spl7_36
  <=> r2_hidden(sK0,k1_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f1562,plain,
    ( spl7_14
  <=> r2_hidden(sK4(k7_relat_1(sK1,k1_tarski(sK0)),sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))),k1_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f2723,plain,
    ( r2_hidden(sK0,k1_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
    | ~ spl7_0
    | ~ spl7_6
    | ~ spl7_14
    | ~ spl7_16 ),
    inference(backward_demodulation,[],[f2717,f1563])).

fof(f1563,plain,
    ( r2_hidden(sK4(k7_relat_1(sK1,k1_tarski(sK0)),sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))),k1_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f1562])).

fof(f2809,plain,
    ( spl7_34
    | ~ spl7_0
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f2752,f1571,f1465,f229,f214,f73,f2807])).

fof(f2807,plain,
    ( spl7_34
  <=> k1_funct_1(sK1,sK0) = k1_funct_1(k7_relat_1(sK1,k1_tarski(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f2123,plain,
    ( ~ spl7_9
    | spl7_32
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f288,f214,f2121,f223])).

fof(f223,plain,
    ( spl7_9
  <=> ~ v1_relat_1(k7_relat_1(sK1,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f2121,plain,
    ( spl7_32
  <=> ! [X4] :
        ( k1_funct_1(X4,sK5(X4,k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))) = sK3(X4,k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
        | k1_funct_1(k7_relat_1(sK1,k1_tarski(sK0)),sK4(k7_relat_1(sK1,k1_tarski(sK0)),sK3(X4,k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))))) = sK3(X4,k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
        | ~ v1_funct_1(X4)
        | k2_relat_1(X4) = k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))
        | ~ v1_relat_1(X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f288,plain,
    ( ! [X4] :
        ( k1_funct_1(X4,sK5(X4,k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))) = sK3(X4,k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
        | ~ v1_relat_1(X4)
        | k2_relat_1(X4) = k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))
        | ~ v1_funct_1(X4)
        | k1_funct_1(k7_relat_1(sK1,k1_tarski(sK0)),sK4(k7_relat_1(sK1,k1_tarski(sK0)),sK3(X4,k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))))) = sK3(X4,k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
        | ~ v1_relat_1(k7_relat_1(sK1,k1_tarski(sK0))) )
    | ~ spl7_6 ),
    inference(resolution,[],[f124,f215])).

fof(f124,plain,(
    ! [X6,X5] :
      ( ~ v1_funct_1(X6)
      | k1_funct_1(X5,sK5(X5,k2_relat_1(X6))) = sK3(X5,k2_relat_1(X6))
      | ~ v1_relat_1(X5)
      | k2_relat_1(X5) = k2_relat_1(X6)
      | ~ v1_funct_1(X5)
      | k1_funct_1(X6,sK4(X6,sK3(X5,k2_relat_1(X6)))) = sK3(X5,k2_relat_1(X6))
      | ~ v1_relat_1(X6) ) ),
    inference(resolution,[],[f51,f64])).

fof(f64,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK4(X0,X2)) = X2
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK4(X0,X2)) = X2
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK5(X0,X1)) = sK3(X0,X1)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f2034,plain,
    ( ~ spl7_15
    | spl7_30
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f334,f229,f220,f214,f2032,f1565])).

fof(f1565,plain,
    ( spl7_15
  <=> ~ r2_hidden(sK4(k7_relat_1(sK1,k1_tarski(sK0)),sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))),k1_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f2032,plain,
    ( spl7_30
  <=> ! [X1] :
        ( sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) != sK3(k7_relat_1(sK1,k1_tarski(sK0)),X1)
        | k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))) = X1
        | ~ r2_hidden(sK3(k7_relat_1(sK1,k1_tarski(sK0)),X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f220,plain,
    ( spl7_8
  <=> v1_relat_1(k7_relat_1(sK1,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f334,plain,
    ( ! [X1] :
        ( sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) != sK3(k7_relat_1(sK1,k1_tarski(sK0)),X1)
        | ~ r2_hidden(sK4(k7_relat_1(sK1,k1_tarski(sK0)),sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))),k1_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
        | ~ r2_hidden(sK3(k7_relat_1(sK1,k1_tarski(sK0)),X1),X1)
        | k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))) = X1 )
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f333,f221])).

fof(f221,plain,
    ( v1_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f220])).

fof(f333,plain,
    ( ! [X1] :
        ( sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) != sK3(k7_relat_1(sK1,k1_tarski(sK0)),X1)
        | ~ r2_hidden(sK4(k7_relat_1(sK1,k1_tarski(sK0)),sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))),k1_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
        | ~ v1_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))
        | ~ r2_hidden(sK3(k7_relat_1(sK1,k1_tarski(sK0)),X1),X1)
        | k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))) = X1 )
    | ~ spl7_6
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f329,f215])).

fof(f329,plain,
    ( ! [X1] :
        ( sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) != sK3(k7_relat_1(sK1,k1_tarski(sK0)),X1)
        | ~ v1_funct_1(k7_relat_1(sK1,k1_tarski(sK0)))
        | ~ r2_hidden(sK4(k7_relat_1(sK1,k1_tarski(sK0)),sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))),k1_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
        | ~ v1_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))
        | ~ r2_hidden(sK3(k7_relat_1(sK1,k1_tarski(sK0)),X1),X1)
        | k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))) = X1 )
    | ~ spl7_10 ),
    inference(superposition,[],[f49,f230])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(X0,X3) != sK3(X0,X1)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(sK3(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f1801,plain,
    ( spl7_24
    | spl7_26
    | spl7_28
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f352,f220,f214,f80,f73,f1799,f1793,f1787])).

fof(f1787,plain,
    ( spl7_24
  <=> k1_funct_1(sK1,sK4(sK1,sK3(k7_relat_1(sK1,k1_tarski(sK0)),k2_relat_1(sK1)))) = sK3(k7_relat_1(sK1,k1_tarski(sK0)),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f1793,plain,
    ( spl7_26
  <=> k1_funct_1(k7_relat_1(sK1,k1_tarski(sK0)),sK5(k7_relat_1(sK1,k1_tarski(sK0)),k2_relat_1(sK1))) = sK3(k7_relat_1(sK1,k1_tarski(sK0)),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f1799,plain,
    ( spl7_28
  <=> k2_relat_1(sK1) = k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f80,plain,
    ( spl7_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f352,plain,
    ( k2_relat_1(sK1) = k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))
    | k1_funct_1(k7_relat_1(sK1,k1_tarski(sK0)),sK5(k7_relat_1(sK1,k1_tarski(sK0)),k2_relat_1(sK1))) = sK3(k7_relat_1(sK1,k1_tarski(sK0)),k2_relat_1(sK1))
    | k1_funct_1(sK1,sK4(sK1,sK3(k7_relat_1(sK1,k1_tarski(sK0)),k2_relat_1(sK1)))) = sK3(k7_relat_1(sK1,k1_tarski(sK0)),k2_relat_1(sK1))
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f350,f221])).

fof(f350,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))
    | k2_relat_1(sK1) = k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))
    | k1_funct_1(k7_relat_1(sK1,k1_tarski(sK0)),sK5(k7_relat_1(sK1,k1_tarski(sK0)),k2_relat_1(sK1))) = sK3(k7_relat_1(sK1,k1_tarski(sK0)),k2_relat_1(sK1))
    | k1_funct_1(sK1,sK4(sK1,sK3(k7_relat_1(sK1,k1_tarski(sK0)),k2_relat_1(sK1)))) = sK3(k7_relat_1(sK1,k1_tarski(sK0)),k2_relat_1(sK1))
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(resolution,[],[f289,f215])).

fof(f289,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k2_relat_1(sK1) = k2_relat_1(X0)
        | k1_funct_1(X0,sK5(X0,k2_relat_1(sK1))) = sK3(X0,k2_relat_1(sK1))
        | k1_funct_1(sK1,sK4(sK1,sK3(X0,k2_relat_1(sK1)))) = sK3(X0,k2_relat_1(sK1)) )
    | ~ spl7_0
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f286,f74])).

fof(f286,plain,
    ( ! [X0] :
        ( k1_funct_1(X0,sK5(X0,k2_relat_1(sK1))) = sK3(X0,k2_relat_1(sK1))
        | ~ v1_relat_1(X0)
        | k2_relat_1(sK1) = k2_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_funct_1(sK1,sK4(sK1,sK3(X0,k2_relat_1(sK1)))) = sK3(X0,k2_relat_1(sK1))
        | ~ v1_relat_1(sK1) )
    | ~ spl7_2 ),
    inference(resolution,[],[f124,f81])).

fof(f81,plain,
    ( v1_funct_1(sK1)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f1782,plain,
    ( ~ spl7_9
    | spl7_22
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f272,f214,f1780,f223])).

fof(f1780,plain,
    ( spl7_22
  <=> ! [X0] :
        ( k1_funct_1(k7_relat_1(sK1,k1_tarski(sK0)),sK4(k7_relat_1(sK1,k1_tarski(sK0)),sK6(X0,k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))))) = sK6(X0,k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
        | k1_tarski(X0) = k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))
        | sK6(X0,k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f272,plain,
    ( ! [X0] :
        ( k1_funct_1(k7_relat_1(sK1,k1_tarski(sK0)),sK4(k7_relat_1(sK1,k1_tarski(sK0)),sK6(X0,k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))))) = sK6(X0,k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
        | ~ v1_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))
        | sK6(X0,k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))) = X0
        | k1_tarski(X0) = k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))) )
    | ~ spl7_6 ),
    inference(resolution,[],[f215,f106])).

fof(f106,plain,(
    ! [X4,X5] :
      ( ~ v1_funct_1(X4)
      | k1_funct_1(X4,sK4(X4,sK6(X5,k2_relat_1(X4)))) = sK6(X5,k2_relat_1(X4))
      | ~ v1_relat_1(X4)
      | sK6(X5,k2_relat_1(X4)) = X5
      | k1_tarski(X5) = k2_relat_1(X4) ) ),
    inference(resolution,[],[f64,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X1)
      | sK6(X0,X1) = X0
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f1721,plain,
    ( ~ spl7_9
    | spl7_20
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f273,f214,f1719,f223])).

fof(f1719,plain,
    ( spl7_20
  <=> ! [X1] :
        ( k1_funct_1(k7_relat_1(sK1,k1_tarski(sK0)),sK5(k7_relat_1(sK1,k1_tarski(sK0)),k1_tarski(X1))) = sK3(k7_relat_1(sK1,k1_tarski(sK0)),k1_tarski(X1))
        | sK3(k7_relat_1(sK1,k1_tarski(sK0)),k1_tarski(X1)) = X1
        | k1_tarski(X1) = k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f273,plain,
    ( ! [X1] :
        ( k1_funct_1(k7_relat_1(sK1,k1_tarski(sK0)),sK5(k7_relat_1(sK1,k1_tarski(sK0)),k1_tarski(X1))) = sK3(k7_relat_1(sK1,k1_tarski(sK0)),k1_tarski(X1))
        | ~ v1_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))
        | k1_tarski(X1) = k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))
        | sK3(k7_relat_1(sK1,k1_tarski(sK0)),k1_tarski(X1)) = X1 )
    | ~ spl7_6 ),
    inference(resolution,[],[f215,f123])).

fof(f123,plain,(
    ! [X4,X3] :
      ( ~ v1_funct_1(X3)
      | k1_funct_1(X3,sK5(X3,k1_tarski(X4))) = sK3(X3,k1_tarski(X4))
      | ~ v1_relat_1(X3)
      | k1_tarski(X4) = k2_relat_1(X3)
      | sK3(X3,k1_tarski(X4)) = X4 ) ),
    inference(resolution,[],[f51,f66])).

fof(f1701,plain,
    ( ~ spl7_15
    | spl7_18
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f332,f229,f220,f214,f1699,f1565])).

fof(f1699,plain,
    ( spl7_18
  <=> ! [X0] :
        ( r2_hidden(sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))),X0)
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f332,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))),X0)
        | ~ r2_hidden(sK4(k7_relat_1(sK1,k1_tarski(sK0)),sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))),k1_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),X0) )
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f331,f215])).

fof(f331,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))),X0)
        | ~ r2_hidden(sK4(k7_relat_1(sK1,k1_tarski(sK0)),sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))),k1_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
        | ~ v1_funct_1(k7_relat_1(sK1,k1_tarski(sK0)))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),X0) )
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f328,f221])).

fof(f328,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))),X0)
        | ~ r2_hidden(sK4(k7_relat_1(sK1,k1_tarski(sK0)),sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))),k1_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
        | ~ v1_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))
        | ~ v1_funct_1(k7_relat_1(sK1,k1_tarski(sK0)))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),X0) )
    | ~ spl7_10 ),
    inference(superposition,[],[f101,f230])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X1),X2)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),X2) ) ),
    inference(resolution,[],[f63,f44])).

fof(f63,plain,(
    ! [X0,X3] :
      ( r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | r2_hidden(k1_funct_1(X0,X3),X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f1618,plain,
    ( ~ spl7_6
    | ~ spl7_8
    | spl7_15
    | ~ spl7_16 ),
    inference(avatar_contradiction_clause,[],[f1617])).

fof(f1617,plain,
    ( $false
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_15
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f1616,f94])).

fof(f94,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f93])).

fof(f93,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f46,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1616,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_15
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f1615,f215])).

fof(f1615,plain,
    ( ~ v1_funct_1(k7_relat_1(sK1,k1_tarski(sK0)))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
    | ~ spl7_8
    | ~ spl7_15
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f1614,f1572])).

fof(f1614,plain,
    ( ~ r2_hidden(sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))),k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
    | ~ v1_funct_1(k7_relat_1(sK1,k1_tarski(sK0)))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
    | ~ spl7_8
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f1604,f221])).

fof(f1604,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))
    | ~ r2_hidden(sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))),k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
    | ~ v1_funct_1(k7_relat_1(sK1,k1_tarski(sK0)))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
    | ~ spl7_15 ),
    inference(resolution,[],[f1566,f103])).

fof(f1566,plain,
    ( ~ r2_hidden(sK4(k7_relat_1(sK1,k1_tarski(sK0)),sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))),k1_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f1565])).

fof(f1613,plain,
    ( ~ spl7_6
    | ~ spl7_8
    | spl7_15
    | ~ spl7_16 ),
    inference(avatar_contradiction_clause,[],[f1612])).

fof(f1612,plain,
    ( $false
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_15
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f1611,f1572])).

fof(f1611,plain,
    ( ~ r2_hidden(sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))),k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f1610,f221])).

fof(f1610,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))
    | ~ r2_hidden(sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))),k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
    | ~ spl7_6
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f1603,f215])).

fof(f1603,plain,
    ( ~ v1_funct_1(k7_relat_1(sK1,k1_tarski(sK0)))
    | ~ v1_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))
    | ~ r2_hidden(sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))),k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
    | ~ spl7_15 ),
    inference(resolution,[],[f1566,f65])).

fof(f1585,plain,
    ( spl7_5
    | spl7_17 ),
    inference(avatar_contradiction_clause,[],[f1584])).

fof(f1584,plain,
    ( $false
    | ~ spl7_5
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f1583,f88])).

fof(f1583,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f1575,f94])).

fof(f1575,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
    | r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))
    | ~ spl7_17 ),
    inference(resolution,[],[f1569,f96])).

fof(f96,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(sK2(X2,X3),X4)
      | ~ r1_tarski(X2,X4)
      | r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f44,f45])).

fof(f1569,plain,
    ( ~ r2_hidden(sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))),k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f1568])).

fof(f1568,plain,
    ( spl7_17
  <=> ~ r2_hidden(sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))),k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f1582,plain,
    ( spl7_5
    | spl7_17 ),
    inference(avatar_contradiction_clause,[],[f1581])).

fof(f1581,plain,
    ( $false
    | ~ spl7_5
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f1574,f88])).

fof(f1574,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))
    | ~ spl7_17 ),
    inference(resolution,[],[f1569,f45])).

fof(f1573,plain,
    ( ~ spl7_15
    | spl7_16
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f336,f229,f220,f214,f1571,f1565])).

fof(f336,plain,
    ( r2_hidden(sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))),k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
    | ~ r2_hidden(sK4(k7_relat_1(sK1,k1_tarski(sK0)),sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))),k1_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f335,f221])).

fof(f335,plain,
    ( r2_hidden(sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))),k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
    | ~ r2_hidden(sK4(k7_relat_1(sK1,k1_tarski(sK0)),sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))),k1_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
    | ~ v1_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))
    | ~ spl7_6
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f330,f215])).

fof(f330,plain,
    ( r2_hidden(sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))),k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
    | ~ v1_funct_1(k7_relat_1(sK1,k1_tarski(sK0)))
    | ~ r2_hidden(sK4(k7_relat_1(sK1,k1_tarski(sK0)),sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))),k1_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
    | ~ v1_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))
    | ~ spl7_10 ),
    inference(superposition,[],[f63,f230])).

fof(f1467,plain,
    ( spl7_12
    | ~ spl7_0
    | ~ spl7_2
    | spl7_5
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f1021,f229,f87,f80,f73,f1465])).

fof(f1021,plain,
    ( k1_funct_1(sK1,sK4(k7_relat_1(sK1,k1_tarski(sK0)),sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))))) = sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_5
    | ~ spl7_10 ),
    inference(forward_demodulation,[],[f1020,f230])).

fof(f1020,plain,
    ( k1_funct_1(sK1,sK4(k7_relat_1(sK1,k1_tarski(sK0)),sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))))) = k1_funct_1(k7_relat_1(sK1,k1_tarski(sK0)),sK4(k7_relat_1(sK1,k1_tarski(sK0)),sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))))
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f1019,f74])).

fof(f1019,plain,
    ( k1_funct_1(sK1,sK4(k7_relat_1(sK1,k1_tarski(sK0)),sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))))) = k1_funct_1(k7_relat_1(sK1,k1_tarski(sK0)),sK4(k7_relat_1(sK1,k1_tarski(sK0)),sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))))
    | ~ v1_relat_1(sK1)
    | ~ spl7_2
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f993,f81])).

fof(f993,plain,
    ( k1_funct_1(sK1,sK4(k7_relat_1(sK1,k1_tarski(sK0)),sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))))) = k1_funct_1(k7_relat_1(sK1,k1_tarski(sK0)),sK4(k7_relat_1(sK1,k1_tarski(sK0)),sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl7_5 ),
    inference(resolution,[],[f254,f88])).

fof(f254,plain,(
    ! [X12,X10,X11] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X10,X11)),X12)
      | k1_funct_1(X10,sK4(k7_relat_1(X10,X11),sK2(k2_relat_1(k7_relat_1(X10,X11)),X12))) = k1_funct_1(k7_relat_1(X10,X11),sK4(k7_relat_1(X10,X11),sK2(k2_relat_1(k7_relat_1(X10,X11)),X12)))
      | ~ v1_funct_1(X10)
      | ~ v1_relat_1(X10) ) ),
    inference(resolution,[],[f112,f45])).

fof(f112,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X5,k2_relat_1(k7_relat_1(X3,X4)))
      | ~ v1_relat_1(X3)
      | k1_funct_1(X3,sK4(k7_relat_1(X3,X4),X5)) = k1_funct_1(k7_relat_1(X3,X4),sK4(k7_relat_1(X3,X4),X5))
      | ~ v1_funct_1(X3) ) ),
    inference(subsumption_resolution,[],[f111,f57])).

fof(f111,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | k1_funct_1(X3,sK4(k7_relat_1(X3,X4),X5)) = k1_funct_1(k7_relat_1(X3,X4),sK4(k7_relat_1(X3,X4),X5))
      | ~ v1_relat_1(k7_relat_1(X3,X4))
      | ~ r2_hidden(X5,k2_relat_1(k7_relat_1(X3,X4))) ) ),
    inference(subsumption_resolution,[],[f109,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t167_funct_1.p',fc8_funct_1)).

fof(f109,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | k1_funct_1(X3,sK4(k7_relat_1(X3,X4),X5)) = k1_funct_1(k7_relat_1(X3,X4),sK4(k7_relat_1(X3,X4),X5))
      | ~ v1_funct_1(k7_relat_1(X3,X4))
      | ~ v1_relat_1(k7_relat_1(X3,X4))
      | ~ r2_hidden(X5,k2_relat_1(k7_relat_1(X3,X4))) ) ),
    inference(resolution,[],[f48,f65])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
       => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t167_funct_1.p',t70_funct_1)).

fof(f297,plain,
    ( ~ spl7_0
    | spl7_9 ),
    inference(avatar_contradiction_clause,[],[f296])).

fof(f296,plain,
    ( $false
    | ~ spl7_0
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f292,f74])).

fof(f292,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl7_9 ),
    inference(resolution,[],[f224,f57])).

fof(f224,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f223])).

fof(f295,plain,
    ( ~ spl7_0
    | ~ spl7_2
    | spl7_9 ),
    inference(avatar_contradiction_clause,[],[f294])).

fof(f294,plain,
    ( $false
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f293,f74])).

fof(f293,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl7_2
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f291,f81])).

fof(f291,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl7_9 ),
    inference(resolution,[],[f224,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f250,plain,
    ( ~ spl7_0
    | ~ spl7_2
    | spl7_7 ),
    inference(avatar_contradiction_clause,[],[f249])).

fof(f249,plain,
    ( $false
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f248,f74])).

fof(f248,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl7_2
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f247,f81])).

fof(f247,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl7_7 ),
    inference(resolution,[],[f218,f56])).

fof(f218,plain,
    ( ~ v1_funct_1(k7_relat_1(sK1,k1_tarski(sK0)))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl7_7
  <=> ~ v1_funct_1(k7_relat_1(sK1,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f231,plain,
    ( ~ spl7_7
    | ~ spl7_9
    | spl7_10
    | spl7_5 ),
    inference(avatar_split_clause,[],[f190,f87,f229,f223,f217])).

fof(f190,plain,
    ( k1_funct_1(k7_relat_1(sK1,k1_tarski(sK0)),sK4(k7_relat_1(sK1,k1_tarski(sK0)),sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))))) = sK2(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))
    | ~ v1_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))
    | ~ v1_funct_1(k7_relat_1(sK1,k1_tarski(sK0)))
    | ~ spl7_5 ),
    inference(resolution,[],[f105,f88])).

fof(f105,plain,(
    ! [X2,X3] :
      ( r1_tarski(k2_relat_1(X2),X3)
      | k1_funct_1(X2,sK4(X2,sK2(k2_relat_1(X2),X3))) = sK2(k2_relat_1(X2),X3)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2) ) ),
    inference(resolution,[],[f64,f45])).

fof(f89,plain,(
    ~ spl7_5 ),
    inference(avatar_split_clause,[],[f41,f87])).

fof(f41,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t167_funct_1.p',t167_funct_1)).

fof(f82,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f40,f80])).

fof(f40,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f75,plain,(
    spl7_0 ),
    inference(avatar_split_clause,[],[f39,f73])).

fof(f39,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
