%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relset_1__t48_relset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:10 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 149 expanded)
%              Number of leaves         :   22 (  64 expanded)
%              Depth                    :    7
%              Number of atoms          :  233 ( 372 expanded)
%              Number of equality atoms :    9 (  17 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3456,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f102,f111,f125,f129,f149,f200,f239,f282,f300,f327,f732,f2649,f3300,f3455])).

fof(f3455,plain,
    ( spl10_53
    | ~ spl10_344 ),
    inference(avatar_contradiction_clause,[],[f3454])).

fof(f3454,plain,
    ( $false
    | ~ spl10_53
    | ~ spl10_344 ),
    inference(subsumption_resolution,[],[f3439,f238])).

fof(f238,plain,
    ( ~ m1_subset_1(sK7(sK2,sK3),sK1)
    | ~ spl10_53 ),
    inference(avatar_component_clause,[],[f237])).

fof(f237,plain,
    ( spl10_53
  <=> ~ m1_subset_1(sK7(sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_53])])).

fof(f3439,plain,
    ( m1_subset_1(sK7(sK2,sK3),sK1)
    | ~ spl10_344 ),
    inference(resolution,[],[f3299,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t48_relset_1.p',t1_subset)).

fof(f3299,plain,
    ( r2_hidden(sK7(sK2,sK3),sK1)
    | ~ spl10_344 ),
    inference(avatar_component_clause,[],[f3298])).

fof(f3298,plain,
    ( spl10_344
  <=> r2_hidden(sK7(sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_344])])).

fof(f3300,plain,
    ( spl10_344
    | ~ spl10_320 ),
    inference(avatar_split_clause,[],[f3251,f2647,f3298])).

fof(f2647,plain,
    ( spl10_320
  <=> r2_hidden(k4_tarski(sK7(sK2,sK3),sK3),k2_zfmisc_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_320])])).

fof(f3251,plain,
    ( r2_hidden(sK7(sK2,sK3),sK1)
    | ~ spl10_320 ),
    inference(resolution,[],[f2648,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t48_relset_1.p',t106_zfmisc_1)).

fof(f2648,plain,
    ( r2_hidden(k4_tarski(sK7(sK2,sK3),sK3),k2_zfmisc_1(sK1,sK0))
    | ~ spl10_320 ),
    inference(avatar_component_clause,[],[f2647])).

fof(f2649,plain,
    ( spl10_320
    | spl10_61
    | ~ spl10_120 ),
    inference(avatar_split_clause,[],[f751,f730,f280,f2647])).

fof(f280,plain,
    ( spl10_61
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_61])])).

fof(f730,plain,
    ( spl10_120
  <=> m1_subset_1(k4_tarski(sK7(sK2,sK3),sK3),k2_zfmisc_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_120])])).

fof(f751,plain,
    ( r2_hidden(k4_tarski(sK7(sK2,sK3),sK3),k2_zfmisc_1(sK1,sK0))
    | ~ spl10_61
    | ~ spl10_120 ),
    inference(subsumption_resolution,[],[f750,f281])).

fof(f281,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK1,sK0))
    | ~ spl10_61 ),
    inference(avatar_component_clause,[],[f280])).

fof(f750,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK1,sK0))
    | r2_hidden(k4_tarski(sK7(sK2,sK3),sK3),k2_zfmisc_1(sK1,sK0))
    | ~ spl10_120 ),
    inference(resolution,[],[f731,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t48_relset_1.p',t2_subset)).

fof(f731,plain,
    ( m1_subset_1(k4_tarski(sK7(sK2,sK3),sK3),k2_zfmisc_1(sK1,sK0))
    | ~ spl10_120 ),
    inference(avatar_component_clause,[],[f730])).

fof(f732,plain,
    ( spl10_120
    | ~ spl10_4
    | ~ spl10_42 ),
    inference(avatar_split_clause,[],[f518,f198,f79,f730])).

fof(f79,plain,
    ( spl10_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f198,plain,
    ( spl10_42
  <=> r2_hidden(k4_tarski(sK7(sK2,sK3),sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_42])])).

fof(f518,plain,
    ( m1_subset_1(k4_tarski(sK7(sK2,sK3),sK3),k2_zfmisc_1(sK1,sK0))
    | ~ spl10_4
    | ~ spl10_42 ),
    inference(resolution,[],[f363,f80])).

fof(f80,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f363,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X3))
        | m1_subset_1(k4_tarski(sK7(sK2,sK3),sK3),X3) )
    | ~ spl10_42 ),
    inference(resolution,[],[f199,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t48_relset_1.p',t4_subset)).

fof(f199,plain,
    ( r2_hidden(k4_tarski(sK7(sK2,sK3),sK3),sK2)
    | ~ spl10_42 ),
    inference(avatar_component_clause,[],[f198])).

fof(f327,plain,
    ( spl10_20
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f317,f100,f127])).

fof(f127,plain,
    ( spl10_20
  <=> sP6(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f100,plain,
    ( spl10_12
  <=> r2_hidden(k4_tarski(sK4,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f317,plain,
    ( sP6(sK3,sK2)
    | ~ spl10_12 ),
    inference(resolution,[],[f101,f52])).

fof(f52,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | sP6(X2,X0) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t48_relset_1.p',d5_relat_1)).

fof(f101,plain,
    ( r2_hidden(k4_tarski(sK4,sK3),sK2)
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f100])).

fof(f300,plain,
    ( spl10_9
    | ~ spl10_20
    | ~ spl10_28 ),
    inference(avatar_contradiction_clause,[],[f299])).

fof(f299,plain,
    ( $false
    | ~ spl10_9
    | ~ spl10_20
    | ~ spl10_28 ),
    inference(subsumption_resolution,[],[f135,f296])).

fof(f296,plain,
    ( ~ r2_hidden(sK3,k2_relat_1(sK2))
    | ~ spl10_9
    | ~ spl10_28 ),
    inference(forward_demodulation,[],[f121,f148])).

fof(f148,plain,
    ( k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2)
    | ~ spl10_28 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl10_28
  <=> k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_28])])).

fof(f121,plain,
    ( ~ r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl10_9
  <=> ~ r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f135,plain,
    ( r2_hidden(sK3,k2_relat_1(sK2))
    | ~ spl10_20 ),
    inference(resolution,[],[f128,f69])).

fof(f69,plain,(
    ! [X2,X0] :
      ( ~ sP6(X2,X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ sP6(X2,X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f128,plain,
    ( sP6(sK3,sK2)
    | ~ spl10_20 ),
    inference(avatar_component_clause,[],[f127])).

fof(f282,plain,
    ( ~ spl10_61
    | ~ spl10_4
    | ~ spl10_42 ),
    inference(avatar_split_clause,[],[f274,f198,f79,f280])).

fof(f274,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK1,sK0))
    | ~ spl10_4
    | ~ spl10_42 ),
    inference(resolution,[],[f204,f80])).

fof(f204,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X2))
        | ~ v1_xboole_0(X2) )
    | ~ spl10_42 ),
    inference(resolution,[],[f199,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t48_relset_1.p',t5_subset)).

fof(f239,plain,
    ( ~ spl10_53
    | ~ spl10_18
    | ~ spl10_42 ),
    inference(avatar_split_clause,[],[f201,f198,f123,f237])).

fof(f123,plain,
    ( spl10_18
  <=> ! [X4] :
        ( ~ m1_subset_1(X4,sK1)
        | ~ r2_hidden(k4_tarski(X4,sK3),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f201,plain,
    ( ~ m1_subset_1(sK7(sK2,sK3),sK1)
    | ~ spl10_18
    | ~ spl10_42 ),
    inference(resolution,[],[f199,f124])).

fof(f124,plain,
    ( ! [X4] :
        ( ~ r2_hidden(k4_tarski(X4,sK3),sK2)
        | ~ m1_subset_1(X4,sK1) )
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f123])).

fof(f200,plain,
    ( spl10_42
    | ~ spl10_20 ),
    inference(avatar_split_clause,[],[f134,f127,f198])).

fof(f134,plain,
    ( r2_hidden(k4_tarski(sK7(sK2,sK3),sK3),sK2)
    | ~ spl10_20 ),
    inference(resolution,[],[f128,f51])).

fof(f51,plain,(
    ! [X2,X0] :
      ( ~ sP6(X2,X0)
      | r2_hidden(k4_tarski(sK7(X0,X2),X2),X0) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f149,plain,
    ( spl10_28
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f82,f79,f147])).

fof(f82,plain,
    ( k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2)
    | ~ spl10_4 ),
    inference(resolution,[],[f80,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t48_relset_1.p',redefinition_k2_relset_1)).

fof(f129,plain,
    ( spl10_20
    | ~ spl10_16 ),
    inference(avatar_split_clause,[],[f112,f109,f127])).

fof(f109,plain,
    ( spl10_16
  <=> r2_hidden(sK3,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f112,plain,
    ( sP6(sK3,sK2)
    | ~ spl10_16 ),
    inference(resolution,[],[f110,f68])).

fof(f68,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_relat_1(X0))
      | sP6(X2,X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( sP6(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f110,plain,
    ( r2_hidden(sK3,k2_relat_1(sK2))
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f109])).

fof(f125,plain,
    ( ~ spl10_9
    | spl10_18 ),
    inference(avatar_split_clause,[],[f42,f123,f120])).

fof(f42,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK1)
      | ~ r2_hidden(k4_tarski(X4,sK3),sK2)
      | ~ r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( r2_hidden(X3,k2_relset_1(X1,X0,X2))
                <~> ? [X4] :
                      ( r2_hidden(k4_tarski(X4,X3),X2)
                      & m1_subset_1(X4,X1) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
               => ! [X3] :
                    ( r2_hidden(X3,k2_relset_1(X1,X0,X2))
                  <=> ? [X4] :
                        ( r2_hidden(k4_tarski(X4,X3),X2)
                        & m1_subset_1(X4,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
             => ! [X3] :
                  ( r2_hidden(X3,k2_relset_1(X1,X0,X2))
                <=> ? [X4] :
                      ( r2_hidden(k4_tarski(X4,X3),X2)
                      & m1_subset_1(X4,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t48_relset_1.p',t48_relset_1)).

fof(f111,plain,
    ( spl10_16
    | ~ spl10_4
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f103,f91,f79,f109])).

fof(f91,plain,
    ( spl10_8
  <=> r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f103,plain,
    ( r2_hidden(sK3,k2_relat_1(sK2))
    | ~ spl10_4
    | ~ spl10_8 ),
    inference(forward_demodulation,[],[f92,f82])).

fof(f92,plain,
    ( r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f91])).

fof(f102,plain,
    ( spl10_8
    | spl10_12 ),
    inference(avatar_split_clause,[],[f44,f100,f91])).

fof(f44,plain,
    ( r2_hidden(k4_tarski(sK4,sK3),sK2)
    | r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) ),
    inference(cnf_transformation,[],[f30])).

fof(f81,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f45,f79])).

fof(f45,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
