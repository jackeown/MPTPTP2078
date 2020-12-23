%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relset_1__t33_relset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:09 EDT 2019

% Result     : Theorem 2.27s
% Output     : Refutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 167 expanded)
%              Number of leaves         :   18 (  61 expanded)
%              Depth                    :   10
%              Number of atoms          :  221 ( 428 expanded)
%              Number of equality atoms :    6 (  13 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13526,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f90,f97,f132,f155,f826,f1887,f2105,f13366,f13511,f13525])).

fof(f13525,plain,
    ( ~ spl10_0
    | ~ spl10_370 ),
    inference(avatar_contradiction_clause,[],[f13521])).

fof(f13521,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_370 ),
    inference(resolution,[],[f13520,f81])).

fof(f81,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl10_0 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl10_0
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_0])])).

fof(f13520,plain,
    ( ! [X2] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,sK2)))
    | ~ spl10_370 ),
    inference(resolution,[],[f13362,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t33_relset_1.p',t3_subset)).

fof(f13362,plain,
    ( ! [X3] : ~ r1_tarski(sK3,k2_zfmisc_1(X3,sK2))
    | ~ spl10_370 ),
    inference(avatar_component_clause,[],[f13361])).

fof(f13361,plain,
    ( spl10_370
  <=> ! [X3] : ~ r1_tarski(sK3,k2_zfmisc_1(X3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_370])])).

fof(f13511,plain,
    ( ~ spl10_4
    | spl10_11
    | ~ spl10_372 ),
    inference(avatar_contradiction_clause,[],[f13510])).

fof(f13510,plain,
    ( $false
    | ~ spl10_4
    | ~ spl10_11
    | ~ spl10_372 ),
    inference(subsumption_resolution,[],[f13506,f154])).

fof(f154,plain,
    ( ~ r1_tarski(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2))
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl10_11
  <=> ~ r1_tarski(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f13506,plain,
    ( r1_tarski(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2))
    | ~ spl10_4
    | ~ spl10_372 ),
    inference(resolution,[],[f13445,f122])).

fof(f122,plain,
    ( ! [X19,X18] :
        ( r2_hidden(k4_tarski(sK4(k7_relat_1(sK3,X18),X19),sK5(k7_relat_1(sK3,X18),X19)),k7_relat_1(sK3,X18))
        | r1_tarski(k7_relat_1(sK3,X18),X19) )
    | ~ spl10_4 ),
    inference(resolution,[],[f103,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox/benchmark/relset_1__t33_relset_1.p',d3_relat_1)).

fof(f103,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK3,X0))
    | ~ spl10_4 ),
    inference(resolution,[],[f96,f58])).

fof(f58,plain,(
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
    file('/export/starexec/sandbox/benchmark/relset_1__t33_relset_1.p',dt_k7_relat_1)).

fof(f96,plain,
    ( v1_relat_1(sK3)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl10_4
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f13445,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(X0,sK5(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2))),k7_relat_1(sK3,X1))
    | ~ spl10_4
    | ~ spl10_372 ),
    inference(resolution,[],[f13373,f125])).

fof(f125,plain,
    ( ! [X4,X5,X3] :
        ( sP8(X3,X4,X5,sK3)
        | ~ r2_hidden(k4_tarski(X4,X3),k7_relat_1(sK3,X5)) )
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f117,f96])).

fof(f117,plain,
    ( ! [X4,X5,X3] :
        ( ~ v1_relat_1(sK3)
        | sP8(X3,X4,X5,sK3)
        | ~ r2_hidden(k4_tarski(X4,X3),k7_relat_1(sK3,X5)) )
    | ~ spl10_4 ),
    inference(resolution,[],[f103,f74])).

fof(f74,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0)
      | sP8(X4,X3,X1,X0)
      | ~ r2_hidden(k4_tarski(X3,X4),k7_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X2)
      | sP8(X4,X3,X1,X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t33_relset_1.p',d11_relat_1)).

fof(f13373,plain,
    ( ! [X2,X1] : ~ sP8(sK5(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2)),X1,X2,sK3)
    | ~ spl10_372 ),
    inference(resolution,[],[f13365,f51])).

fof(f51,plain,(
    ! [X4,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X3,X4),X0)
      | ~ sP8(X4,X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f13365,plain,
    ( ! [X2] : ~ r2_hidden(k4_tarski(X2,sK5(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2))),sK3)
    | ~ spl10_372 ),
    inference(avatar_component_clause,[],[f13364])).

fof(f13364,plain,
    ( spl10_372
  <=> ! [X2] : ~ r2_hidden(k4_tarski(X2,sK5(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_372])])).

fof(f13366,plain,
    ( spl10_370
    | spl10_372
    | ~ spl10_4
    | spl10_71 ),
    inference(avatar_split_clause,[],[f1930,f1885,f95,f13364,f13361])).

fof(f1885,plain,
    ( spl10_71
  <=> ~ r2_hidden(sK5(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_71])])).

fof(f1930,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,sK5(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2))),sK3)
        | ~ r1_tarski(sK3,k2_zfmisc_1(X3,sK2)) )
    | ~ spl10_4
    | ~ spl10_71 ),
    inference(resolution,[],[f1892,f106])).

fof(f106,plain,
    ( ! [X6,X7,X5] :
        ( r2_hidden(k4_tarski(X5,X6),X7)
        | ~ r2_hidden(k4_tarski(X5,X6),sK3)
        | ~ r1_tarski(sK3,X7) )
    | ~ spl10_4 ),
    inference(resolution,[],[f96,f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(k4_tarski(X2,X3),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1892,plain,
    ( ! [X2,X3] : ~ r2_hidden(k4_tarski(X2,sK5(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2))),k2_zfmisc_1(X3,sK2))
    | ~ spl10_71 ),
    inference(resolution,[],[f1886,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t33_relset_1.p',t106_zfmisc_1)).

fof(f1886,plain,
    ( ~ r2_hidden(sK5(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2)),sK2)
    | ~ spl10_71 ),
    inference(avatar_component_clause,[],[f1885])).

fof(f2105,plain,
    ( ~ spl10_4
    | spl10_11
    | spl10_69 ),
    inference(avatar_contradiction_clause,[],[f2104])).

fof(f2104,plain,
    ( $false
    | ~ spl10_4
    | ~ spl10_11
    | ~ spl10_69 ),
    inference(subsumption_resolution,[],[f2097,f154])).

fof(f2097,plain,
    ( r1_tarski(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2))
    | ~ spl10_4
    | ~ spl10_69 ),
    inference(resolution,[],[f1895,f122])).

fof(f1895,plain,
    ( ! [X2] : ~ r2_hidden(k4_tarski(sK4(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2)),X2),k7_relat_1(sK3,sK1))
    | ~ spl10_4
    | ~ spl10_69 ),
    inference(resolution,[],[f1890,f125])).

fof(f1890,plain,
    ( ! [X4,X5] : ~ sP8(X4,sK4(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2)),sK1,X5)
    | ~ spl10_69 ),
    inference(resolution,[],[f1880,f50])).

fof(f50,plain,(
    ! [X4,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ sP8(X4,X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1880,plain,
    ( ~ r2_hidden(sK4(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2)),sK1)
    | ~ spl10_69 ),
    inference(avatar_component_clause,[],[f1879])).

fof(f1879,plain,
    ( spl10_69
  <=> ~ r2_hidden(sK4(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_69])])).

fof(f1887,plain,
    ( ~ spl10_69
    | ~ spl10_71
    | spl10_31 ),
    inference(avatar_split_clause,[],[f834,f824,f1885,f1879])).

fof(f824,plain,
    ( spl10_31
  <=> ~ r2_hidden(k4_tarski(sK4(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2)),sK5(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2))),k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_31])])).

fof(f834,plain,
    ( ~ r2_hidden(sK5(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2)),sK2)
    | ~ r2_hidden(sK4(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2)),sK1)
    | ~ spl10_31 ),
    inference(resolution,[],[f825,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f825,plain,
    ( ~ r2_hidden(k4_tarski(sK4(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2)),sK5(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2))),k2_zfmisc_1(sK1,sK2))
    | ~ spl10_31 ),
    inference(avatar_component_clause,[],[f824])).

fof(f826,plain,
    ( ~ spl10_31
    | ~ spl10_4
    | spl10_11 ),
    inference(avatar_split_clause,[],[f364,f153,f95,f824])).

fof(f364,plain,
    ( ~ r2_hidden(k4_tarski(sK4(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2)),sK5(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2))),k2_zfmisc_1(sK1,sK2))
    | ~ spl10_4
    | ~ spl10_11 ),
    inference(resolution,[],[f123,f154])).

fof(f123,plain,
    ( ! [X21,X20] :
        ( r1_tarski(k7_relat_1(sK3,X20),X21)
        | ~ r2_hidden(k4_tarski(sK4(k7_relat_1(sK3,X20),X21),sK5(k7_relat_1(sK3,X20),X21)),X21) )
    | ~ spl10_4 ),
    inference(resolution,[],[f103,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f155,plain,
    ( ~ spl10_11
    | spl10_9 ),
    inference(avatar_split_clause,[],[f133,f130,f153])).

fof(f130,plain,
    ( spl10_9
  <=> ~ m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f133,plain,
    ( ~ r1_tarski(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2))
    | ~ spl10_9 ),
    inference(resolution,[],[f131,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f131,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f130])).

fof(f132,plain,
    ( ~ spl10_9
    | ~ spl10_0
    | spl10_3 ),
    inference(avatar_split_clause,[],[f102,f88,f80,f130])).

fof(f88,plain,
    ( spl10_3
  <=> ~ m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f102,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl10_0
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f101,f81])).

fof(f101,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl10_3 ),
    inference(superposition,[],[f89,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t33_relset_1.p',redefinition_k5_relset_1)).

fof(f89,plain,
    ( ~ m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f88])).

fof(f97,plain,
    ( spl10_4
    | ~ spl10_0 ),
    inference(avatar_split_clause,[],[f83,f80,f95])).

fof(f83,plain,
    ( v1_relat_1(sK3)
    | ~ spl10_0 ),
    inference(resolution,[],[f81,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t33_relset_1.p',cc1_relset_1)).

fof(f90,plain,(
    ~ spl10_3 ),
    inference(avatar_split_clause,[],[f44,f88])).

fof(f44,plain,(
    ~ m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t33_relset_1.p',t33_relset_1)).

fof(f82,plain,(
    spl10_0 ),
    inference(avatar_split_clause,[],[f43,f80])).

fof(f43,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
