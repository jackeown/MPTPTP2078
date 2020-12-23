%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 236 expanded)
%              Number of leaves         :   25 (  90 expanded)
%              Depth                    :   15
%              Number of atoms          :  396 ( 812 expanded)
%              Number of equality atoms :   26 (  37 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f285,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f63,f69,f73,f77,f92,f96,f112,f121,f130,f136,f203,f207,f257,f263,f284])).

fof(f284,plain,
    ( spl5_20
    | ~ spl5_1
    | ~ spl5_7
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f274,f261,f90,f53,f189])).

fof(f189,plain,
    ( spl5_20
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f53,plain,
    ( spl5_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f90,plain,
    ( spl5_7
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f261,plain,
    ( spl5_28
  <=> r2_hidden(k1_funct_1(sK3,sK4(k1_relat_1(sK3),sK0,sK3)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f274,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK0)))
    | ~ spl5_1
    | ~ spl5_7
    | ~ spl5_28 ),
    inference(subsumption_resolution,[],[f273,f91])).

fof(f91,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f90])).

fof(f273,plain,
    ( ~ v1_relat_1(sK3)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK0)))
    | ~ spl5_1
    | ~ spl5_28 ),
    inference(subsumption_resolution,[],[f270,f54])).

fof(f54,plain,
    ( v1_funct_1(sK3)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f270,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK0)))
    | ~ spl5_28 ),
    inference(resolution,[],[f262,f50])).

fof(f50,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(k1_funct_1(X2,sK4(k1_relat_1(X2),X1,X2)),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k1_relat_1(X2) != X0
      | ~ r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( ! [X3] :
              ( r2_hidden(X3,X0)
             => r2_hidden(k1_funct_1(X2,X3),X1) )
          & k1_relat_1(X2) = X0 )
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).

fof(f262,plain,
    ( r2_hidden(k1_funct_1(sK3,sK4(k1_relat_1(sK3),sK0,sK3)),sK0)
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f261])).

fof(f263,plain,
    ( spl5_20
    | spl5_28
    | ~ spl5_1
    | ~ spl5_5
    | ~ spl5_15
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f258,f255,f134,f71,f53,f261,f189])).

fof(f71,plain,
    ( spl5_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f134,plain,
    ( spl5_15
  <=> m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f255,plain,
    ( spl5_27
  <=> k3_funct_2(sK1,sK2,sK3,sK4(k1_relat_1(sK3),sK0,sK3)) = k1_funct_1(sK3,sK4(k1_relat_1(sK3),sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f258,plain,
    ( r2_hidden(k1_funct_1(sK3,sK4(k1_relat_1(sK3),sK0,sK3)),sK0)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK0)))
    | ~ spl5_1
    | ~ spl5_5
    | ~ spl5_15
    | ~ spl5_27 ),
    inference(superposition,[],[f148,f256])).

fof(f256,plain,
    ( k3_funct_2(sK1,sK2,sK3,sK4(k1_relat_1(sK3),sK0,sK3)) = k1_funct_1(sK3,sK4(k1_relat_1(sK3),sK0,sK3))
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f255])).

fof(f148,plain,
    ( ! [X1] :
        ( r2_hidden(k3_funct_2(sK1,sK2,sK3,sK4(k1_relat_1(sK3),X1,sK3)),sK0)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X1))) )
    | ~ spl5_1
    | ~ spl5_5
    | ~ spl5_15 ),
    inference(resolution,[],[f141,f25])).

fof(f25,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK1)
      | r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                  | ~ m1_subset_1(X4,X1) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                  | ~ m1_subset_1(X4,X1) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_2(X3,X1,X2)
                  & v1_funct_1(X3) )
               => ( ! [X4] :
                      ( m1_subset_1(X4,X1)
                     => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) )
                 => r1_tarski(k2_relset_1(X1,X2,X3),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_2(X3,X1,X2)
                & v1_funct_1(X3) )
             => ( ! [X4] :
                    ( m1_subset_1(X4,X1)
                   => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) )
               => r1_tarski(k2_relset_1(X1,X2,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_funct_2)).

fof(f141,plain,
    ( ! [X0] :
        ( m1_subset_1(sK4(k1_relat_1(sK3),X0,sK3),sK1)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) )
    | ~ spl5_1
    | ~ spl5_5
    | ~ spl5_15 ),
    inference(resolution,[],[f135,f132])).

fof(f132,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(X1))
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0)))
        | m1_subset_1(sK4(k1_relat_1(sK3),X0,sK3),X1) )
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(resolution,[],[f85,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f85,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(k1_relat_1(sK3),X0,sK3),k1_relat_1(sK3))
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) )
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f64,f80])).

fof(f80,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_5 ),
    inference(resolution,[],[f72,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f72,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f71])).

fof(f64,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK3)
        | r2_hidden(sK4(k1_relat_1(sK3),X0,sK3),k1_relat_1(sK3))
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) )
    | ~ spl5_1 ),
    inference(resolution,[],[f54,f51])).

fof(f51,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(sK4(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k1_relat_1(X2) != X0
      | r2_hidden(sK4(X0,X1,X2),X0)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f135,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1))
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f134])).

fof(f257,plain,
    ( spl5_27
    | ~ spl5_1
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | spl5_14
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f253,f134,f128,f90,f71,f67,f61,f53,f255])).

fof(f61,plain,
    ( spl5_3
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f67,plain,
    ( spl5_4
  <=> v1_funct_2(sK3,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f128,plain,
    ( spl5_14
  <=> r1_tarski(k2_relat_1(sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f253,plain,
    ( k3_funct_2(sK1,sK2,sK3,sK4(k1_relat_1(sK3),sK0,sK3)) = k1_funct_1(sK3,sK4(k1_relat_1(sK3),sK0,sK3))
    | ~ spl5_1
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | spl5_14
    | ~ spl5_15 ),
    inference(resolution,[],[f160,f129])).

fof(f129,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK0)
    | spl5_14 ),
    inference(avatar_component_clause,[],[f128])).

fof(f160,plain,
    ( ! [X0] :
        ( r1_tarski(k2_relat_1(sK3),X0)
        | k3_funct_2(sK1,sK2,sK3,sK4(k1_relat_1(sK3),X0,sK3)) = k1_funct_1(sK3,sK4(k1_relat_1(sK3),X0,sK3)) )
    | ~ spl5_1
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f159,f91])).

fof(f159,plain,
    ( ! [X0] :
        ( k3_funct_2(sK1,sK2,sK3,sK4(k1_relat_1(sK3),X0,sK3)) = k1_funct_1(sK3,sK4(k1_relat_1(sK3),X0,sK3))
        | r1_tarski(k2_relat_1(sK3),X0)
        | ~ v1_relat_1(sK3) )
    | ~ spl5_1
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_15 ),
    inference(resolution,[],[f152,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f152,plain,
    ( ! [X1] :
        ( v5_relat_1(sK3,X1)
        | k3_funct_2(sK1,sK2,sK3,sK4(k1_relat_1(sK3),X1,sK3)) = k1_funct_1(sK3,sK4(k1_relat_1(sK3),X1,sK3)) )
    | ~ spl5_1
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_15 ),
    inference(resolution,[],[f147,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f147,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0)))
        | k3_funct_2(sK1,sK2,sK3,sK4(k1_relat_1(sK3),X0,sK3)) = k1_funct_1(sK3,sK4(k1_relat_1(sK3),X0,sK3)) )
    | ~ spl5_1
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_15 ),
    inference(resolution,[],[f141,f88])).

fof(f88,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0) )
    | ~ spl5_1
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f87,f62])).

fof(f62,plain,
    ( ~ v1_xboole_0(sK1)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f87,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK1)
        | ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0) )
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f86,f68])).

fof(f68,plain,
    ( v1_funct_2(sK3,sK1,sK2)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f86,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK3,sK1,sK2)
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0) )
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f81,f54])).

fof(f81,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,sK1,sK2)
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0) )
    | ~ spl5_5 ),
    inference(resolution,[],[f72,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f207,plain,
    ( ~ spl5_7
    | spl5_14
    | ~ spl5_21 ),
    inference(avatar_contradiction_clause,[],[f206])).

fof(f206,plain,
    ( $false
    | ~ spl5_7
    | spl5_14
    | ~ spl5_21 ),
    inference(subsumption_resolution,[],[f205,f91])).

fof(f205,plain,
    ( ~ v1_relat_1(sK3)
    | spl5_14
    | ~ spl5_21 ),
    inference(subsumption_resolution,[],[f204,f129])).

fof(f204,plain,
    ( r1_tarski(k2_relat_1(sK3),sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl5_21 ),
    inference(resolution,[],[f202,f35])).

fof(f202,plain,
    ( v5_relat_1(sK3,sK0)
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl5_21
  <=> v5_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f203,plain,
    ( spl5_21
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f193,f189,f201])).

fof(f193,plain,
    ( v5_relat_1(sK3,sK0)
    | ~ spl5_20 ),
    inference(resolution,[],[f190,f47])).

fof(f190,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK0)))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f189])).

fof(f136,plain,
    ( spl5_15
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f123,f110,f134])).

fof(f110,plain,
    ( spl5_11
  <=> r1_tarski(k1_relat_1(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f123,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1))
    | ~ spl5_11 ),
    inference(resolution,[],[f111,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f111,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f110])).

fof(f130,plain,
    ( ~ spl5_14
    | spl5_6
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f124,f119,f75,f128])).

fof(f75,plain,
    ( spl5_6
  <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f119,plain,
    ( spl5_13
  <=> k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f124,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK0)
    | spl5_6
    | ~ spl5_13 ),
    inference(superposition,[],[f76,f120])).

fof(f120,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f119])).

fof(f76,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f75])).

fof(f121,plain,
    ( spl5_13
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f82,f71,f119])).

fof(f82,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)
    | ~ spl5_5 ),
    inference(resolution,[],[f72,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f112,plain,
    ( spl5_11
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f102,f94,f90,f110])).

fof(f94,plain,
    ( spl5_8
  <=> v4_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f102,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1)
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f101,f91])).

fof(f101,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1)
    | ~ v1_relat_1(sK3)
    | ~ spl5_8 ),
    inference(resolution,[],[f95,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f95,plain,
    ( v4_relat_1(sK3,sK1)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f94])).

fof(f96,plain,
    ( spl5_8
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f78,f71,f94])).

fof(f78,plain,
    ( v4_relat_1(sK3,sK1)
    | ~ spl5_5 ),
    inference(resolution,[],[f72,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f92,plain,
    ( spl5_7
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f80,f71,f90])).

fof(f77,plain,(
    ~ spl5_6 ),
    inference(avatar_split_clause,[],[f29,f75])).

fof(f29,plain,(
    ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f73,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f28,f71])).

fof(f28,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f13])).

fof(f69,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f27,f67])).

fof(f27,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f63,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f31,f61])).

fof(f31,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f55,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f26,f53])).

fof(f26,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:40:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.45  % (9423)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.46  % (9415)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (9424)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.47  % (9415)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f285,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f55,f63,f69,f73,f77,f92,f96,f112,f121,f130,f136,f203,f207,f257,f263,f284])).
% 0.21/0.47  fof(f284,plain,(
% 0.21/0.47    spl5_20 | ~spl5_1 | ~spl5_7 | ~spl5_28),
% 0.21/0.47    inference(avatar_split_clause,[],[f274,f261,f90,f53,f189])).
% 0.21/0.47  fof(f189,plain,(
% 0.21/0.47    spl5_20 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    spl5_1 <=> v1_funct_1(sK3)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    spl5_7 <=> v1_relat_1(sK3)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.47  fof(f261,plain,(
% 0.21/0.47    spl5_28 <=> r2_hidden(k1_funct_1(sK3,sK4(k1_relat_1(sK3),sK0,sK3)),sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 0.21/0.47  fof(f274,plain,(
% 0.21/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK0))) | (~spl5_1 | ~spl5_7 | ~spl5_28)),
% 0.21/0.47    inference(subsumption_resolution,[],[f273,f91])).
% 0.21/0.47  fof(f91,plain,(
% 0.21/0.47    v1_relat_1(sK3) | ~spl5_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f90])).
% 0.21/0.47  fof(f273,plain,(
% 0.21/0.47    ~v1_relat_1(sK3) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK0))) | (~spl5_1 | ~spl5_28)),
% 0.21/0.47    inference(subsumption_resolution,[],[f270,f54])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    v1_funct_1(sK3) | ~spl5_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f53])).
% 0.21/0.47  fof(f270,plain,(
% 0.21/0.47    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK0))) | ~spl5_28),
% 0.21/0.47    inference(resolution,[],[f262,f50])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ( ! [X2,X1] : (~r2_hidden(k1_funct_1(X2,sK4(k1_relat_1(X2),X1,X2)),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))) )),
% 0.21/0.47    inference(equality_resolution,[],[f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_relat_1(X2) != X0 | ~r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.47    inference(flattening,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).
% 0.21/0.47  fof(f262,plain,(
% 0.21/0.47    r2_hidden(k1_funct_1(sK3,sK4(k1_relat_1(sK3),sK0,sK3)),sK0) | ~spl5_28),
% 0.21/0.47    inference(avatar_component_clause,[],[f261])).
% 0.21/0.47  fof(f263,plain,(
% 0.21/0.47    spl5_20 | spl5_28 | ~spl5_1 | ~spl5_5 | ~spl5_15 | ~spl5_27),
% 0.21/0.47    inference(avatar_split_clause,[],[f258,f255,f134,f71,f53,f261,f189])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    spl5_5 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.47  fof(f134,plain,(
% 0.21/0.47    spl5_15 <=> m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.21/0.47  fof(f255,plain,(
% 0.21/0.47    spl5_27 <=> k3_funct_2(sK1,sK2,sK3,sK4(k1_relat_1(sK3),sK0,sK3)) = k1_funct_1(sK3,sK4(k1_relat_1(sK3),sK0,sK3))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.21/0.47  fof(f258,plain,(
% 0.21/0.47    r2_hidden(k1_funct_1(sK3,sK4(k1_relat_1(sK3),sK0,sK3)),sK0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK0))) | (~spl5_1 | ~spl5_5 | ~spl5_15 | ~spl5_27)),
% 0.21/0.47    inference(superposition,[],[f148,f256])).
% 0.21/0.47  fof(f256,plain,(
% 0.21/0.47    k3_funct_2(sK1,sK2,sK3,sK4(k1_relat_1(sK3),sK0,sK3)) = k1_funct_1(sK3,sK4(k1_relat_1(sK3),sK0,sK3)) | ~spl5_27),
% 0.21/0.47    inference(avatar_component_clause,[],[f255])).
% 0.21/0.47  fof(f148,plain,(
% 0.21/0.47    ( ! [X1] : (r2_hidden(k3_funct_2(sK1,sK2,sK3,sK4(k1_relat_1(sK3),X1,sK3)),sK0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X1)))) ) | (~spl5_1 | ~spl5_5 | ~spl5_15)),
% 0.21/0.47    inference(resolution,[],[f141,f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ( ! [X4] : (~m1_subset_1(X4,sK1) | r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 0.21/0.47    inference(flattening,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ? [X0,X1] : (? [X2] : (? [X3] : ((~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 0.21/0.47    inference(negated_conjecture,[],[f10])).
% 0.21/0.47  fof(f10,conjecture,(
% 0.21/0.47    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_funct_2)).
% 0.21/0.47  fof(f141,plain,(
% 0.21/0.47    ( ! [X0] : (m1_subset_1(sK4(k1_relat_1(sK3),X0,sK3),sK1) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0)))) ) | (~spl5_1 | ~spl5_5 | ~spl5_15)),
% 0.21/0.47    inference(resolution,[],[f135,f132])).
% 0.21/0.47  fof(f132,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(X1)) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) | m1_subset_1(sK4(k1_relat_1(sK3),X0,sK3),X1)) ) | (~spl5_1 | ~spl5_5)),
% 0.21/0.47    inference(resolution,[],[f85,f39])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.47    inference(flattening,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    ( ! [X0] : (r2_hidden(sK4(k1_relat_1(sK3),X0,sK3),k1_relat_1(sK3)) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0)))) ) | (~spl5_1 | ~spl5_5)),
% 0.21/0.47    inference(subsumption_resolution,[],[f64,f80])).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    v1_relat_1(sK3) | ~spl5_5),
% 0.21/0.47    inference(resolution,[],[f72,f45])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl5_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f71])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_relat_1(sK3) | r2_hidden(sK4(k1_relat_1(sK3),X0,sK3),k1_relat_1(sK3)) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0)))) ) | ~spl5_1),
% 0.21/0.47    inference(resolution,[],[f54,f51])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    ( ! [X2,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | r2_hidden(sK4(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))) )),
% 0.21/0.47    inference(equality_resolution,[],[f40])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_relat_1(X2) != X0 | r2_hidden(sK4(X0,X1,X2),X0) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f135,plain,(
% 0.21/0.47    m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1)) | ~spl5_15),
% 0.21/0.47    inference(avatar_component_clause,[],[f134])).
% 0.21/0.47  fof(f257,plain,(
% 0.21/0.47    spl5_27 | ~spl5_1 | spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | spl5_14 | ~spl5_15),
% 0.21/0.47    inference(avatar_split_clause,[],[f253,f134,f128,f90,f71,f67,f61,f53,f255])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    spl5_3 <=> v1_xboole_0(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    spl5_4 <=> v1_funct_2(sK3,sK1,sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.47  fof(f128,plain,(
% 0.21/0.47    spl5_14 <=> r1_tarski(k2_relat_1(sK3),sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.47  fof(f253,plain,(
% 0.21/0.47    k3_funct_2(sK1,sK2,sK3,sK4(k1_relat_1(sK3),sK0,sK3)) = k1_funct_1(sK3,sK4(k1_relat_1(sK3),sK0,sK3)) | (~spl5_1 | spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | spl5_14 | ~spl5_15)),
% 0.21/0.47    inference(resolution,[],[f160,f129])).
% 0.21/0.47  fof(f129,plain,(
% 0.21/0.47    ~r1_tarski(k2_relat_1(sK3),sK0) | spl5_14),
% 0.21/0.47    inference(avatar_component_clause,[],[f128])).
% 0.21/0.47  fof(f160,plain,(
% 0.21/0.47    ( ! [X0] : (r1_tarski(k2_relat_1(sK3),X0) | k3_funct_2(sK1,sK2,sK3,sK4(k1_relat_1(sK3),X0,sK3)) = k1_funct_1(sK3,sK4(k1_relat_1(sK3),X0,sK3))) ) | (~spl5_1 | spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_15)),
% 0.21/0.47    inference(subsumption_resolution,[],[f159,f91])).
% 0.21/0.47  fof(f159,plain,(
% 0.21/0.47    ( ! [X0] : (k3_funct_2(sK1,sK2,sK3,sK4(k1_relat_1(sK3),X0,sK3)) = k1_funct_1(sK3,sK4(k1_relat_1(sK3),X0,sK3)) | r1_tarski(k2_relat_1(sK3),X0) | ~v1_relat_1(sK3)) ) | (~spl5_1 | spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_15)),
% 0.21/0.47    inference(resolution,[],[f152,f35])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.47  fof(f152,plain,(
% 0.21/0.47    ( ! [X1] : (v5_relat_1(sK3,X1) | k3_funct_2(sK1,sK2,sK3,sK4(k1_relat_1(sK3),X1,sK3)) = k1_funct_1(sK3,sK4(k1_relat_1(sK3),X1,sK3))) ) | (~spl5_1 | spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_15)),
% 0.21/0.47    inference(resolution,[],[f147,f47])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.47  fof(f147,plain,(
% 0.21/0.47    ( ! [X0] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) | k3_funct_2(sK1,sK2,sK3,sK4(k1_relat_1(sK3),X0,sK3)) = k1_funct_1(sK3,sK4(k1_relat_1(sK3),X0,sK3))) ) | (~spl5_1 | spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_15)),
% 0.21/0.47    inference(resolution,[],[f141,f88])).
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0)) ) | (~spl5_1 | spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.21/0.47    inference(subsumption_resolution,[],[f87,f62])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    ~v1_xboole_0(sK1) | spl5_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f61])).
% 0.21/0.47  fof(f87,plain,(
% 0.21/0.47    ( ! [X0] : (v1_xboole_0(sK1) | ~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0)) ) | (~spl5_1 | ~spl5_4 | ~spl5_5)),
% 0.21/0.47    inference(subsumption_resolution,[],[f86,f68])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    v1_funct_2(sK3,sK1,sK2) | ~spl5_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f67])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_funct_2(sK3,sK1,sK2) | v1_xboole_0(sK1) | ~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0)) ) | (~spl5_1 | ~spl5_5)),
% 0.21/0.47    inference(subsumption_resolution,[],[f81,f54])).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK2) | v1_xboole_0(sK1) | ~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0)) ) | ~spl5_5),
% 0.21/0.47    inference(resolution,[],[f72,f44])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_xboole_0(X0) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.21/0.47    inference(flattening,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.21/0.47  fof(f207,plain,(
% 0.21/0.47    ~spl5_7 | spl5_14 | ~spl5_21),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f206])).
% 0.21/0.47  fof(f206,plain,(
% 0.21/0.47    $false | (~spl5_7 | spl5_14 | ~spl5_21)),
% 0.21/0.47    inference(subsumption_resolution,[],[f205,f91])).
% 0.21/0.47  fof(f205,plain,(
% 0.21/0.47    ~v1_relat_1(sK3) | (spl5_14 | ~spl5_21)),
% 0.21/0.47    inference(subsumption_resolution,[],[f204,f129])).
% 0.21/0.47  fof(f204,plain,(
% 0.21/0.47    r1_tarski(k2_relat_1(sK3),sK0) | ~v1_relat_1(sK3) | ~spl5_21),
% 0.21/0.47    inference(resolution,[],[f202,f35])).
% 0.21/0.47  fof(f202,plain,(
% 0.21/0.47    v5_relat_1(sK3,sK0) | ~spl5_21),
% 0.21/0.47    inference(avatar_component_clause,[],[f201])).
% 0.21/0.47  fof(f201,plain,(
% 0.21/0.47    spl5_21 <=> v5_relat_1(sK3,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.21/0.47  fof(f203,plain,(
% 0.21/0.47    spl5_21 | ~spl5_20),
% 0.21/0.47    inference(avatar_split_clause,[],[f193,f189,f201])).
% 0.21/0.47  fof(f193,plain,(
% 0.21/0.47    v5_relat_1(sK3,sK0) | ~spl5_20),
% 0.21/0.47    inference(resolution,[],[f190,f47])).
% 0.21/0.47  fof(f190,plain,(
% 0.21/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK0))) | ~spl5_20),
% 0.21/0.47    inference(avatar_component_clause,[],[f189])).
% 0.21/0.47  fof(f136,plain,(
% 0.21/0.47    spl5_15 | ~spl5_11),
% 0.21/0.47    inference(avatar_split_clause,[],[f123,f110,f134])).
% 0.21/0.47  fof(f110,plain,(
% 0.21/0.47    spl5_11 <=> r1_tarski(k1_relat_1(sK3),sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.47  fof(f123,plain,(
% 0.21/0.47    m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1)) | ~spl5_11),
% 0.21/0.47    inference(resolution,[],[f111,f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.47  fof(f111,plain,(
% 0.21/0.47    r1_tarski(k1_relat_1(sK3),sK1) | ~spl5_11),
% 0.21/0.47    inference(avatar_component_clause,[],[f110])).
% 0.21/0.47  fof(f130,plain,(
% 0.21/0.47    ~spl5_14 | spl5_6 | ~spl5_13),
% 0.21/0.47    inference(avatar_split_clause,[],[f124,f119,f75,f128])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    spl5_6 <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.47  fof(f119,plain,(
% 0.21/0.47    spl5_13 <=> k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.47  fof(f124,plain,(
% 0.21/0.47    ~r1_tarski(k2_relat_1(sK3),sK0) | (spl5_6 | ~spl5_13)),
% 0.21/0.47    inference(superposition,[],[f76,f120])).
% 0.21/0.47  fof(f120,plain,(
% 0.21/0.47    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) | ~spl5_13),
% 0.21/0.47    inference(avatar_component_clause,[],[f119])).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    ~r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0) | spl5_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f75])).
% 0.21/0.47  fof(f121,plain,(
% 0.21/0.47    spl5_13 | ~spl5_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f82,f71,f119])).
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) | ~spl5_5),
% 0.21/0.47    inference(resolution,[],[f72,f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.47  fof(f112,plain,(
% 0.21/0.47    spl5_11 | ~spl5_7 | ~spl5_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f102,f94,f90,f110])).
% 0.21/0.47  fof(f94,plain,(
% 0.21/0.47    spl5_8 <=> v4_relat_1(sK3,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.47  fof(f102,plain,(
% 0.21/0.47    r1_tarski(k1_relat_1(sK3),sK1) | (~spl5_7 | ~spl5_8)),
% 0.21/0.47    inference(subsumption_resolution,[],[f101,f91])).
% 0.21/0.47  fof(f101,plain,(
% 0.21/0.47    r1_tarski(k1_relat_1(sK3),sK1) | ~v1_relat_1(sK3) | ~spl5_8),
% 0.21/0.47    inference(resolution,[],[f95,f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.47  fof(f95,plain,(
% 0.21/0.47    v4_relat_1(sK3,sK1) | ~spl5_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f94])).
% 0.21/0.47  fof(f96,plain,(
% 0.21/0.47    spl5_8 | ~spl5_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f78,f71,f94])).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    v4_relat_1(sK3,sK1) | ~spl5_5),
% 0.21/0.47    inference(resolution,[],[f72,f46])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f92,plain,(
% 0.21/0.47    spl5_7 | ~spl5_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f80,f71,f90])).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    ~spl5_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f29,f75])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ~r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    spl5_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f28,f71])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    spl5_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f27,f67])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    v1_funct_2(sK3,sK1,sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    ~spl5_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f31,f61])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ~v1_xboole_0(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    spl5_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f26,f53])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    v1_funct_1(sK3)),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (9415)------------------------------
% 0.21/0.47  % (9415)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (9415)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (9415)Memory used [KB]: 6268
% 0.21/0.47  % (9415)Time elapsed: 0.068 s
% 0.21/0.47  % (9415)------------------------------
% 0.21/0.47  % (9415)------------------------------
% 0.21/0.48  % (9414)Success in time 0.11 s
%------------------------------------------------------------------------------
