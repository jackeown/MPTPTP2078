%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relset_1__t38_relset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:10 EDT 2019

% Result     : Theorem 22.93s
% Output     : Refutation 22.93s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 563 expanded)
%              Number of leaves         :   24 ( 161 expanded)
%              Depth                    :   15
%              Number of atoms          :  418 (1388 expanded)
%              Number of equality atoms :   42 ( 340 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f34595,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f185,f203,f2073,f2087,f5615,f8200,f33123,f34594])).

fof(f34594,plain,
    ( spl19_1
    | spl19_7 ),
    inference(avatar_contradiction_clause,[],[f34593])).

fof(f34593,plain,
    ( $false
    | ~ spl19_1
    | ~ spl19_7 ),
    inference(subsumption_resolution,[],[f34574,f2662])).

fof(f2662,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK6(sK2,sK1,k1_relat_1(sK2)),X0),sK2)
    | ~ spl19_1
    | ~ spl19_7 ),
    inference(subsumption_resolution,[],[f2661,f507])).

fof(f507,plain,
    ( ! [X28,X27] :
        ( ~ r2_hidden(k4_tarski(X27,X28),sK2)
        | r2_hidden(X28,sK1) )
    | ~ spl19_7 ),
    inference(resolution,[],[f237,f110])).

fof(f110,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t38_relset_1.p',t106_zfmisc_1)).

fof(f237,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(X0,sK2) )
    | ~ spl19_7 ),
    inference(subsumption_resolution,[],[f236,f202])).

fof(f202,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl19_7 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl19_7
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_7])])).

fof(f236,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | v1_xboole_0(k2_zfmisc_1(sK0,sK1))
      | r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) ) ),
    inference(resolution,[],[f156,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t38_relset_1.p',t2_subset)).

fof(f156,plain,(
    ! [X4] :
      ( m1_subset_1(X4,k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X4,sK2) ) ),
    inference(resolution,[],[f65,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t38_relset_1.p',t4_subset)).

fof(f65,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) != k1_relset_1(X0,X1,X2)
        | k7_relset_1(X0,X1,X2,X0) != k2_relset_1(X0,X1,X2) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
          & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t38_relset_1.p',t38_relset_1)).

fof(f2661,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK6(sK2,sK1,k1_relat_1(sK2)),X0),sK2)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl19_1 ),
    inference(subsumption_resolution,[],[f2660,f2659])).

fof(f2659,plain,
    ( r2_hidden(sK6(sK2,sK1,k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ spl19_1 ),
    inference(subsumption_resolution,[],[f2649,f119])).

fof(f119,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t38_relset_1.p',d4_relat_1)).

fof(f2649,plain,
    ( r2_hidden(sK6(sK2,sK1,k1_relat_1(sK2)),k1_relat_1(sK2))
    | r2_hidden(k4_tarski(sK6(sK2,sK1,k1_relat_1(sK2)),sK8(sK2,sK1,k1_relat_1(sK2))),sK2)
    | ~ spl19_1 ),
    inference(resolution,[],[f2376,f171])).

fof(f171,plain,(
    ! [X28,X27] :
      ( sQ18_eqProxy(k10_relat_1(sK2,X27),X28)
      | r2_hidden(sK6(sK2,X27,X28),X28)
      | r2_hidden(k4_tarski(sK6(sK2,X27,X28),sK8(sK2,X27,X28)),sK2) ) ),
    inference(resolution,[],[f147,f130])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK8(X0,X1,X2)),X0)
      | r2_hidden(sK6(X0,X1,X2),X2)
      | sQ18_eqProxy(k10_relat_1(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f74,f124])).

fof(f124,plain,(
    ! [X1,X0] :
      ( sQ18_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ18_eqProxy])])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK8(X0,X1,X2)),X0)
      | r2_hidden(sK6(X0,X1,X2),X2)
      | k10_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t38_relset_1.p',d14_relat_1)).

fof(f147,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f65,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t38_relset_1.p',cc1_relset_1)).

fof(f2376,plain,
    ( ~ sQ18_eqProxy(k10_relat_1(sK2,sK1),k1_relat_1(sK2))
    | ~ spl19_1 ),
    inference(resolution,[],[f488,f289])).

fof(f289,plain,
    ( ~ sQ18_eqProxy(k10_relat_1(sK2,sK1),k1_relset_1(sK0,sK1,sK2))
    | ~ spl19_1 ),
    inference(resolution,[],[f190,f155])).

fof(f155,plain,(
    ! [X3] : sQ18_eqProxy(k8_relset_1(sK0,sK1,sK2,X3),k10_relat_1(sK2,X3)) ),
    inference(resolution,[],[f65,f143])).

fof(f143,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sQ18_eqProxy(k8_relset_1(X0,X1,X2,X3),k10_relat_1(X2,X3)) ) ),
    inference(equality_proxy_replacement,[],[f108,f124])).

fof(f108,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t38_relset_1.p',redefinition_k8_relset_1)).

fof(f190,plain,
    ( ! [X0] :
        ( ~ sQ18_eqProxy(k8_relset_1(sK0,sK1,sK2,sK1),X0)
        | ~ sQ18_eqProxy(X0,k1_relset_1(sK0,sK1,sK2)) )
    | ~ spl19_1 ),
    inference(resolution,[],[f178,f146])).

fof(f146,plain,(
    ! [X2,X0,X1] :
      ( ~ sQ18_eqProxy(X0,X1)
      | ~ sQ18_eqProxy(X1,X2)
      | sQ18_eqProxy(X0,X2) ) ),
    inference(equality_proxy_axiom,[],[f124])).

fof(f178,plain,
    ( ~ sQ18_eqProxy(k8_relset_1(sK0,sK1,sK2,sK1),k1_relset_1(sK0,sK1,sK2))
    | ~ spl19_1 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl19_1
  <=> ~ sQ18_eqProxy(k8_relset_1(sK0,sK1,sK2,sK1),k1_relset_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_1])])).

fof(f488,plain,(
    ! [X0] :
      ( sQ18_eqProxy(X0,k1_relset_1(sK0,sK1,sK2))
      | ~ sQ18_eqProxy(X0,k1_relat_1(sK2)) ) ),
    inference(resolution,[],[f214,f146])).

fof(f214,plain,(
    sQ18_eqProxy(k1_relat_1(sK2),k1_relset_1(sK0,sK1,sK2)) ),
    inference(resolution,[],[f153,f145])).

fof(f145,plain,(
    ! [X0,X1] :
      ( ~ sQ18_eqProxy(X0,X1)
      | sQ18_eqProxy(X1,X0) ) ),
    inference(equality_proxy_axiom,[],[f124])).

fof(f153,plain,(
    sQ18_eqProxy(k1_relset_1(sK0,sK1,sK2),k1_relat_1(sK2)) ),
    inference(resolution,[],[f65,f141])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sQ18_eqProxy(k1_relset_1(X0,X1,X2),k1_relat_1(X2)) ) ),
    inference(equality_proxy_replacement,[],[f100,f124])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t38_relset_1.p',redefinition_k1_relset_1)).

fof(f2660,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK6(sK2,sK1,k1_relat_1(sK2)),X0),sK2)
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(sK6(sK2,sK1,k1_relat_1(sK2)),k1_relat_1(sK2)) )
    | ~ spl19_1 ),
    inference(subsumption_resolution,[],[f2651,f147])).

fof(f2651,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK2)
        | ~ r2_hidden(k4_tarski(sK6(sK2,sK1,k1_relat_1(sK2)),X0),sK2)
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(sK6(sK2,sK1,k1_relat_1(sK2)),k1_relat_1(sK2)) )
    | ~ spl19_1 ),
    inference(resolution,[],[f2376,f131])).

fof(f131,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),X4),X0)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(sK6(X0,X1,X2),X2)
      | sQ18_eqProxy(k10_relat_1(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f73,f124])).

fof(f73,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),X4),X0)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(sK6(X0,X1,X2),X2)
      | k10_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f34574,plain,
    ( r2_hidden(k4_tarski(sK6(sK2,sK1,k1_relat_1(sK2)),sK12(sK2,sK6(sK2,sK1,k1_relat_1(sK2)))),sK2)
    | ~ spl19_1 ),
    inference(resolution,[],[f2659,f118])).

fof(f118,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,sK12(X0,X2)),X0)
      | ~ r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK12(X0,X2)),X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f33123,plain,
    ( spl19_3
    | spl19_7 ),
    inference(avatar_contradiction_clause,[],[f33122])).

fof(f33122,plain,
    ( $false
    | ~ spl19_3
    | ~ spl19_7 ),
    inference(subsumption_resolution,[],[f33103,f9006])).

fof(f9006,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK3(sK2,sK0,k2_relat_1(sK2))),sK2)
    | ~ spl19_3
    | ~ spl19_7 ),
    inference(subsumption_resolution,[],[f9005,f506])).

fof(f506,plain,
    ( ! [X26,X25] :
        ( ~ r2_hidden(k4_tarski(X25,X26),sK2)
        | r2_hidden(X25,sK0) )
    | ~ spl19_7 ),
    inference(resolution,[],[f237,f109])).

fof(f109,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9005,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK3(sK2,sK0,k2_relat_1(sK2))),sK2)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl19_3 ),
    inference(subsumption_resolution,[],[f9004,f8995])).

fof(f8995,plain,
    ( r2_hidden(sK3(sK2,sK0,k2_relat_1(sK2)),k2_relat_1(sK2))
    | ~ spl19_3 ),
    inference(subsumption_resolution,[],[f8994,f121])).

fof(f121,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t38_relset_1.p',d5_relat_1)).

fof(f8994,plain,
    ( r2_hidden(k4_tarski(sK5(sK2,sK0,k2_relat_1(sK2)),sK3(sK2,sK0,k2_relat_1(sK2))),sK2)
    | r2_hidden(sK3(sK2,sK0,k2_relat_1(sK2)),k2_relat_1(sK2))
    | ~ spl19_3 ),
    inference(subsumption_resolution,[],[f8983,f147])).

fof(f8983,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(k4_tarski(sK5(sK2,sK0,k2_relat_1(sK2)),sK3(sK2,sK0,k2_relat_1(sK2))),sK2)
    | r2_hidden(sK3(sK2,sK0,k2_relat_1(sK2)),k2_relat_1(sK2))
    | ~ spl19_3 ),
    inference(resolution,[],[f4847,f127])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK3(X0,X1,X2)),X0)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | sQ18_eqProxy(k9_relat_1(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f68,f124])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK3(X0,X1,X2)),X0)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k9_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t38_relset_1.p',d13_relat_1)).

fof(f4847,plain,
    ( ~ sQ18_eqProxy(k9_relat_1(sK2,sK0),k2_relat_1(sK2))
    | ~ spl19_3 ),
    inference(resolution,[],[f364,f485])).

fof(f485,plain,(
    ! [X0] :
      ( sQ18_eqProxy(X0,k2_relset_1(sK0,sK1,sK2))
      | ~ sQ18_eqProxy(X0,k2_relat_1(sK2)) ) ),
    inference(resolution,[],[f211,f146])).

fof(f211,plain,(
    sQ18_eqProxy(k2_relat_1(sK2),k2_relset_1(sK0,sK1,sK2)) ),
    inference(resolution,[],[f152,f145])).

fof(f152,plain,(
    sQ18_eqProxy(k2_relset_1(sK0,sK1,sK2),k2_relat_1(sK2)) ),
    inference(resolution,[],[f65,f140])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sQ18_eqProxy(k2_relset_1(X0,X1,X2),k2_relat_1(X2)) ) ),
    inference(equality_proxy_replacement,[],[f99,f124])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t38_relset_1.p',redefinition_k2_relset_1)).

fof(f364,plain,
    ( ~ sQ18_eqProxy(k9_relat_1(sK2,sK0),k2_relset_1(sK0,sK1,sK2))
    | ~ spl19_3 ),
    inference(resolution,[],[f317,f154])).

fof(f154,plain,(
    ! [X2] : sQ18_eqProxy(k7_relset_1(sK0,sK1,sK2,X2),k9_relat_1(sK2,X2)) ),
    inference(resolution,[],[f65,f142])).

fof(f142,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sQ18_eqProxy(k7_relset_1(X0,X1,X2,X3),k9_relat_1(X2,X3)) ) ),
    inference(equality_proxy_replacement,[],[f107,f124])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t38_relset_1.p',redefinition_k7_relset_1)).

fof(f317,plain,
    ( ! [X0] :
        ( ~ sQ18_eqProxy(k7_relset_1(sK0,sK1,sK2,sK0),X0)
        | ~ sQ18_eqProxy(X0,k2_relset_1(sK0,sK1,sK2)) )
    | ~ spl19_3 ),
    inference(resolution,[],[f184,f146])).

fof(f184,plain,
    ( ~ sQ18_eqProxy(k7_relset_1(sK0,sK1,sK2,sK0),k2_relset_1(sK0,sK1,sK2))
    | ~ spl19_3 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl19_3
  <=> ~ sQ18_eqProxy(k7_relset_1(sK0,sK1,sK2,sK0),k2_relset_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_3])])).

fof(f9004,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK3(sK2,sK0,k2_relat_1(sK2))),sK2)
        | ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(sK3(sK2,sK0,k2_relat_1(sK2)),k2_relat_1(sK2)) )
    | ~ spl19_3 ),
    inference(subsumption_resolution,[],[f8982,f147])).

fof(f8982,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK2)
        | ~ r2_hidden(k4_tarski(X0,sK3(sK2,sK0,k2_relat_1(sK2))),sK2)
        | ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(sK3(sK2,sK0,k2_relat_1(sK2)),k2_relat_1(sK2)) )
    | ~ spl19_3 ),
    inference(resolution,[],[f4847,f128])).

fof(f128,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,sK3(X0,X1,X2)),X0)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | sQ18_eqProxy(k9_relat_1(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f67,f124])).

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,sK3(X0,X1,X2)),X0)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | k9_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f33103,plain,
    ( r2_hidden(k4_tarski(sK15(sK2,sK3(sK2,sK0,k2_relat_1(sK2))),sK3(sK2,sK0,k2_relat_1(sK2))),sK2)
    | ~ spl19_3 ),
    inference(resolution,[],[f8995,f120])).

fof(f120,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK15(X0,X2),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK15(X0,X2),X2),X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f8200,plain,
    ( spl19_3
    | ~ spl19_66
    | ~ spl19_68 ),
    inference(avatar_contradiction_clause,[],[f8199])).

fof(f8199,plain,
    ( $false
    | ~ spl19_3
    | ~ spl19_66
    | ~ spl19_68 ),
    inference(subsumption_resolution,[],[f8196,f5488])).

fof(f5488,plain,
    ( ! [X70,X71] :
        ( ~ r2_hidden(X70,X71)
        | ~ r2_hidden(X70,k2_relat_1(sK2)) )
    | ~ spl19_68 ),
    inference(resolution,[],[f2085,f998])).

fof(f998,plain,(
    ! [X14,X15] :
      ( r2_hidden(sK15(sK2,X14),k10_relat_1(sK2,X15))
      | ~ r2_hidden(X14,X15)
      | ~ r2_hidden(X14,k2_relat_1(sK2)) ) ),
    inference(resolution,[],[f164,f120])).

fof(f164,plain,(
    ! [X12,X13,X11] :
      ( ~ r2_hidden(k4_tarski(X11,X12),sK2)
      | ~ r2_hidden(X12,X13)
      | r2_hidden(X11,k10_relat_1(sK2,X13)) ) ),
    inference(resolution,[],[f147,f115])).

fof(f115,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f2085,plain,
    ( ! [X31,X32] : ~ r2_hidden(X31,k10_relat_1(sK2,X32))
    | ~ spl19_68 ),
    inference(avatar_component_clause,[],[f2084])).

fof(f2084,plain,
    ( spl19_68
  <=> ! [X32,X31] : ~ r2_hidden(X31,k10_relat_1(sK2,X32)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_68])])).

fof(f8196,plain,
    ( r2_hidden(sK10(k2_relat_1(sK2),k9_relat_1(sK2,sK0)),k2_relat_1(sK2))
    | ~ spl19_3
    | ~ spl19_66 ),
    inference(subsumption_resolution,[],[f8186,f2070])).

fof(f2070,plain,
    ( ! [X28,X29] : ~ r2_hidden(X28,k9_relat_1(sK2,X29))
    | ~ spl19_66 ),
    inference(avatar_component_clause,[],[f2069])).

fof(f2069,plain,
    ( spl19_66
  <=> ! [X29,X28] : ~ r2_hidden(X28,k9_relat_1(sK2,X29)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_66])])).

fof(f8186,plain,
    ( r2_hidden(sK10(k2_relat_1(sK2),k9_relat_1(sK2,sK0)),k9_relat_1(sK2,sK0))
    | r2_hidden(sK10(k2_relat_1(sK2),k9_relat_1(sK2,sK0)),k2_relat_1(sK2))
    | ~ spl19_3 ),
    inference(resolution,[],[f4846,f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK10(X0,X1),X1)
      | r2_hidden(sK10(X0,X1),X0)
      | sQ18_eqProxy(X0,X1) ) ),
    inference(equality_proxy_replacement,[],[f84,f124])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK10(X0,X1),X1)
      | r2_hidden(sK10(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t38_relset_1.p',t2_tarski)).

fof(f4846,plain,
    ( ~ sQ18_eqProxy(k2_relat_1(sK2),k9_relat_1(sK2,sK0))
    | ~ spl19_3 ),
    inference(resolution,[],[f364,f670])).

fof(f670,plain,(
    ! [X0] :
      ( sQ18_eqProxy(X0,k2_relset_1(sK0,sK1,sK2))
      | ~ sQ18_eqProxy(k2_relat_1(sK2),X0) ) ),
    inference(resolution,[],[f213,f145])).

fof(f213,plain,(
    ! [X1] :
      ( sQ18_eqProxy(k2_relset_1(sK0,sK1,sK2),X1)
      | ~ sQ18_eqProxy(k2_relat_1(sK2),X1) ) ),
    inference(resolution,[],[f152,f146])).

fof(f5615,plain,
    ( spl19_1
    | ~ spl19_66 ),
    inference(avatar_contradiction_clause,[],[f5614])).

fof(f5614,plain,
    ( $false
    | ~ spl19_1
    | ~ spl19_66 ),
    inference(subsumption_resolution,[],[f2659,f4777])).

fof(f4777,plain,
    ( ! [X68,X69] :
        ( ~ r2_hidden(X68,X69)
        | ~ r2_hidden(X68,k1_relat_1(sK2)) )
    | ~ spl19_66 ),
    inference(resolution,[],[f2070,f960])).

fof(f960,plain,(
    ! [X19,X18] :
      ( r2_hidden(sK12(sK2,X18),k9_relat_1(sK2,X19))
      | ~ r2_hidden(X18,X19)
      | ~ r2_hidden(X18,k1_relat_1(sK2)) ) ),
    inference(resolution,[],[f161,f118])).

fof(f161,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),sK2)
      | ~ r2_hidden(X4,X6)
      | r2_hidden(X5,k9_relat_1(sK2,X6)) ) ),
    inference(resolution,[],[f147,f112])).

fof(f112,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f2087,plain,
    ( ~ spl19_5
    | spl19_68 ),
    inference(avatar_split_clause,[],[f1027,f2084,f192])).

fof(f192,plain,
    ( spl19_5
  <=> ~ sP17(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_5])])).

fof(f1027,plain,(
    ! [X52,X53] :
      ( ~ r2_hidden(X52,k10_relat_1(sK2,X53))
      | ~ sP17(sK2) ) ),
    inference(resolution,[],[f166,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP17(X1) ) ),
    inference(general_splitting,[],[f104,f122_D])).

fof(f122,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | sP17(X1) ) ),
    inference(cnf_transformation,[],[f122_D])).

fof(f122_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
          | ~ v1_xboole_0(X2) )
    <=> ~ sP17(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP17])])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t38_relset_1.p',t5_subset)).

fof(f166,plain,(
    ! [X17,X16] :
      ( r2_hidden(k4_tarski(X16,sK7(sK2,X17,X16)),sK2)
      | ~ r2_hidden(X16,k10_relat_1(sK2,X17)) ) ),
    inference(resolution,[],[f147,f117])).

fof(f117,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,sK7(X0,X1,X3)),X0)
      | ~ r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,sK7(X0,X1,X3)),X0)
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f2073,plain,
    ( ~ spl19_5
    | spl19_66 ),
    inference(avatar_split_clause,[],[f986,f2069,f192])).

fof(f986,plain,(
    ! [X50,X49] :
      ( ~ r2_hidden(X49,k9_relat_1(sK2,X50))
      | ~ sP17(sK2) ) ),
    inference(resolution,[],[f163,f123])).

fof(f163,plain,(
    ! [X10,X9] :
      ( r2_hidden(k4_tarski(sK4(sK2,X9,X10),X10),sK2)
      | ~ r2_hidden(X10,k9_relat_1(sK2,X9)) ) ),
    inference(resolution,[],[f147,f114])).

fof(f114,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK4(X0,X1,X3),X3),X0)
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK4(X0,X1,X3),X3),X0)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f203,plain,
    ( spl19_4
    | ~ spl19_7 ),
    inference(avatar_split_clause,[],[f157,f201,f195])).

fof(f195,plain,
    ( spl19_4
  <=> sP17(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_4])])).

fof(f157,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | sP17(sK2) ),
    inference(resolution,[],[f65,f122])).

fof(f185,plain,
    ( ~ spl19_1
    | ~ spl19_3 ),
    inference(avatar_split_clause,[],[f125,f183,f177])).

fof(f125,plain,
    ( ~ sQ18_eqProxy(k7_relset_1(sK0,sK1,sK2,sK0),k2_relset_1(sK0,sK1,sK2))
    | ~ sQ18_eqProxy(k8_relset_1(sK0,sK1,sK2,sK1),k1_relset_1(sK0,sK1,sK2)) ),
    inference(equality_proxy_replacement,[],[f64,f124,f124])).

fof(f64,plain,
    ( k7_relset_1(sK0,sK1,sK2,sK0) != k2_relset_1(sK0,sK1,sK2)
    | k8_relset_1(sK0,sK1,sK2,sK1) != k1_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
