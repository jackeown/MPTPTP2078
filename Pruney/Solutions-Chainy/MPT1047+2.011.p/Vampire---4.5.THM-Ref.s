%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:02 EST 2020

% Result     : Theorem 2.02s
% Output     : Refutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 452 expanded)
%              Number of leaves         :   26 ( 172 expanded)
%              Depth                    :   11
%              Number of atoms          :  599 (1730 expanded)
%              Number of equality atoms :   69 ( 271 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1399,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f61,f65,f69,f73,f107,f154,f379,f420,f431,f453,f520,f539,f554,f583,f638,f694,f770,f1270,f1285,f1287,f1292,f1386,f1398])).

fof(f1398,plain,
    ( spl7_30
    | ~ spl7_25 ),
    inference(avatar_split_clause,[],[f534,f515,f581])).

fof(f581,plain,
    ( spl7_30
  <=> v1_partfun1(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f515,plain,
    ( spl7_25
  <=> sP5(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),sK3,k1_tarski(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f534,plain,
    ( v1_partfun1(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),sK0)
    | ~ spl7_25 ),
    inference(forward_demodulation,[],[f529,f526])).

fof(f526,plain,
    ( sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)) = sK6(sK0,k1_tarski(sK1),sK3,sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)))
    | ~ spl7_25 ),
    inference(resolution,[],[f516,f31])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP5(X4,X2,X1,X0)
      | sK6(X0,X1,X2,X4) = X4 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_partfun1)).

fof(f516,plain,
    ( sP5(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),sK3,k1_tarski(sK1),sK0)
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f515])).

fof(f529,plain,
    ( v1_partfun1(sK6(sK0,k1_tarski(sK1),sK3,sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3))),sK0)
    | ~ spl7_25 ),
    inference(resolution,[],[f516,f32])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP5(X4,X2,X1,X0)
      | v1_partfun1(sK6(X0,X1,X2,X4),X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1386,plain,
    ( spl7_31
    | ~ spl7_2
    | ~ spl7_5
    | ~ spl7_28
    | ~ spl7_34 ),
    inference(avatar_split_clause,[],[f1324,f692,f537,f71,f59,f588])).

fof(f588,plain,
    ( spl7_31
  <=> r1_partfun1(sK2,sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f59,plain,
    ( spl7_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f71,plain,
    ( spl7_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f537,plain,
    ( spl7_28
  <=> v1_funct_1(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f692,plain,
    ( spl7_34
  <=> m1_subset_1(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f1324,plain,
    ( r1_partfun1(sK2,sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)))
    | ~ spl7_2
    | ~ spl7_5
    | ~ spl7_28
    | ~ spl7_34 ),
    inference(subsumption_resolution,[],[f1298,f538])).

fof(f538,plain,
    ( v1_funct_1(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)))
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f537])).

fof(f1298,plain,
    ( ~ v1_funct_1(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)))
    | r1_partfun1(sK2,sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)))
    | ~ spl7_2
    | ~ spl7_5
    | ~ spl7_34 ),
    inference(resolution,[],[f693,f96])).

fof(f96,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | ~ v1_funct_1(X0)
        | r1_partfun1(sK2,X0) )
    | ~ spl7_2
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f89,f60])).

fof(f60,plain,
    ( v1_funct_1(sK2)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f89,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK2)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | r1_partfun1(sK2,X0) )
    | ~ spl7_5 ),
    inference(resolution,[],[f72,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | r1_partfun1(X2,X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_1(X3) )
         => r1_partfun1(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_partfun1)).

fof(f72,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f71])).

fof(f693,plain,
    ( m1_subset_1(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ spl7_34 ),
    inference(avatar_component_clause,[],[f692])).

fof(f1292,plain,
    ( spl7_34
    | ~ spl7_25 ),
    inference(avatar_split_clause,[],[f1281,f515,f692])).

fof(f1281,plain,
    ( m1_subset_1(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ spl7_25 ),
    inference(forward_demodulation,[],[f1276,f1274])).

fof(f1274,plain,
    ( sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)) = sK6(sK0,k1_tarski(sK1),sK3,sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)))
    | ~ spl7_25 ),
    inference(resolution,[],[f516,f31])).

fof(f1276,plain,
    ( m1_subset_1(sK6(sK0,k1_tarski(sK1),sK3,sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3))),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ spl7_25 ),
    inference(resolution,[],[f516,f30])).

fof(f30,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP5(X4,X2,X1,X0)
      | m1_subset_1(sK6(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1287,plain,
    ( spl7_26
    | ~ spl7_28
    | ~ spl7_30
    | ~ spl7_31
    | ~ spl7_34 ),
    inference(avatar_split_clause,[],[f1244,f692,f588,f581,f537,f518])).

fof(f518,plain,
    ( spl7_26
  <=> sP5(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),sK2,k1_tarski(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f1244,plain,
    ( sP5(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),sK2,k1_tarski(sK1),sK0)
    | ~ spl7_28
    | ~ spl7_30
    | ~ spl7_31
    | ~ spl7_34 ),
    inference(resolution,[],[f753,f589])).

fof(f589,plain,
    ( r1_partfun1(sK2,sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)))
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f588])).

fof(f753,plain,
    ( ! [X4] :
        ( ~ r1_partfun1(X4,sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)))
        | sP5(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),X4,k1_tarski(sK1),sK0) )
    | ~ spl7_28
    | ~ spl7_30
    | ~ spl7_34 ),
    inference(subsumption_resolution,[],[f752,f582])).

fof(f582,plain,
    ( v1_partfun1(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),sK0)
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f581])).

fof(f752,plain,
    ( ! [X4] :
        ( ~ v1_partfun1(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),sK0)
        | ~ r1_partfun1(X4,sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)))
        | sP5(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),X4,k1_tarski(sK1),sK0) )
    | ~ spl7_28
    | ~ spl7_34 ),
    inference(subsumption_resolution,[],[f737,f538])).

fof(f737,plain,
    ( ! [X4] :
        ( ~ v1_funct_1(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)))
        | ~ v1_partfun1(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),sK0)
        | ~ r1_partfun1(X4,sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)))
        | sP5(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),X4,k1_tarski(sK1),sK0) )
    | ~ spl7_34 ),
    inference(resolution,[],[f693,f50])).

fof(f50,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_partfun1(X5,X0)
      | ~ r1_partfun1(X2,X5)
      | sP5(X5,X2,X1,X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X4 != X5
      | ~ v1_partfun1(X5,X0)
      | ~ r1_partfun1(X2,X5)
      | sP5(X4,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1285,plain,
    ( spl7_32
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_25 ),
    inference(avatar_split_clause,[],[f531,f515,f112,f67,f55,f636])).

fof(f636,plain,
    ( spl7_32
  <=> r2_hidden(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f55,plain,
    ( spl7_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f67,plain,
    ( spl7_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f112,plain,
    ( spl7_8
  <=> k1_tarski(sK3) = k5_partfun1(sK0,k1_tarski(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f531,plain,
    ( r2_hidden(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),k1_tarski(sK3))
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_25 ),
    inference(forward_demodulation,[],[f525,f449])).

fof(f449,plain,
    ( k1_tarski(sK3) = k5_partfun1(sK0,k1_tarski(sK1),sK3)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f112])).

fof(f525,plain,
    ( r2_hidden(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),k5_partfun1(sK0,k1_tarski(sK1),sK3))
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_25 ),
    inference(resolution,[],[f516,f87])).

fof(f87,plain,
    ( ! [X3] :
        ( ~ sP5(X3,sK3,k1_tarski(sK1),sK0)
        | r2_hidden(X3,k5_partfun1(sK0,k1_tarski(sK1),sK3)) )
    | ~ spl7_1
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f79,f56])).

fof(f56,plain,
    ( v1_funct_1(sK3)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f79,plain,
    ( ! [X3] :
        ( ~ v1_funct_1(sK3)
        | ~ sP5(X3,sK3,k1_tarski(sK1),sK0)
        | r2_hidden(X3,k5_partfun1(sK0,k1_tarski(sK1),sK3)) )
    | ~ spl7_4 ),
    inference(resolution,[],[f68,f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ sP5(X4,X2,X1,X0)
      | r2_hidden(X4,k5_partfun1(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ sP5(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k5_partfun1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f68,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f1270,plain,
    ( spl7_25
    | ~ spl7_28
    | ~ spl7_30
    | ~ spl7_34
    | ~ spl7_36 ),
    inference(avatar_split_clause,[],[f1243,f768,f692,f581,f537,f515])).

fof(f768,plain,
    ( spl7_36
  <=> r1_partfun1(sK3,sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f1243,plain,
    ( sP5(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),sK3,k1_tarski(sK1),sK0)
    | ~ spl7_28
    | ~ spl7_30
    | ~ spl7_34
    | ~ spl7_36 ),
    inference(resolution,[],[f753,f769])).

fof(f769,plain,
    ( r1_partfun1(sK3,sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)))
    | ~ spl7_36 ),
    inference(avatar_component_clause,[],[f768])).

fof(f770,plain,
    ( spl7_36
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_28
    | ~ spl7_34 ),
    inference(avatar_split_clause,[],[f743,f692,f537,f67,f55,f768])).

fof(f743,plain,
    ( r1_partfun1(sK3,sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)))
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_28
    | ~ spl7_34 ),
    inference(subsumption_resolution,[],[f730,f538])).

fof(f730,plain,
    ( ~ v1_funct_1(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)))
    | r1_partfun1(sK3,sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)))
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_34 ),
    inference(resolution,[],[f693,f81])).

fof(f81,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | ~ v1_funct_1(X0)
        | r1_partfun1(sK3,X0) )
    | ~ spl7_1
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f74,f56])).

fof(f74,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK3)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | r1_partfun1(sK3,X0) )
    | ~ spl7_4 ),
    inference(resolution,[],[f68,f42])).

fof(f694,plain,
    ( spl7_34
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f551,f518,f692])).

fof(f551,plain,
    ( m1_subset_1(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ spl7_26 ),
    inference(forward_demodulation,[],[f544,f542])).

fof(f542,plain,
    ( sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)) = sK6(sK0,k1_tarski(sK1),sK2,sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)))
    | ~ spl7_26 ),
    inference(resolution,[],[f519,f31])).

fof(f519,plain,
    ( sP5(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),sK2,k1_tarski(sK1),sK0)
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f518])).

fof(f544,plain,
    ( m1_subset_1(sK6(sK0,k1_tarski(sK1),sK2,sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3))),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ spl7_26 ),
    inference(resolution,[],[f519,f30])).

fof(f638,plain,
    ( ~ spl7_32
    | ~ spl7_2
    | ~ spl7_5
    | spl7_6
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f549,f518,f105,f71,f59,f636])).

fof(f105,plain,
    ( spl7_6
  <=> k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f549,plain,
    ( ~ r2_hidden(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),k1_tarski(sK3))
    | ~ spl7_2
    | ~ spl7_5
    | spl7_6
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f548,f106])).

fof(f106,plain,
    ( k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3)
    | spl7_6 ),
    inference(avatar_component_clause,[],[f105])).

fof(f548,plain,
    ( ~ r2_hidden(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),k1_tarski(sK3))
    | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(sK3)
    | ~ spl7_2
    | ~ spl7_5
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f547,f60])).

fof(f547,plain,
    ( ~ v1_funct_1(sK2)
    | ~ r2_hidden(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),k1_tarski(sK3))
    | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(sK3)
    | ~ spl7_5
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f540,f72])).

fof(f540,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ r2_hidden(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),k1_tarski(sK3))
    | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(sK3)
    | ~ spl7_26 ),
    inference(resolution,[],[f519,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP5(sK4(X0,X1,X2,X3),X2,X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(sK4(X0,X1,X2,X3),X3)
      | k5_partfun1(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f583,plain,
    ( spl7_30
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f552,f518,f581])).

fof(f552,plain,
    ( v1_partfun1(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),sK0)
    | ~ spl7_26 ),
    inference(forward_demodulation,[],[f545,f542])).

fof(f545,plain,
    ( v1_partfun1(sK6(sK0,k1_tarski(sK1),sK2,sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3))),sK0)
    | ~ spl7_26 ),
    inference(resolution,[],[f519,f32])).

fof(f554,plain,
    ( spl7_28
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f550,f518,f537])).

fof(f550,plain,
    ( v1_funct_1(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)))
    | ~ spl7_26 ),
    inference(forward_demodulation,[],[f543,f542])).

fof(f543,plain,
    ( v1_funct_1(sK6(sK0,k1_tarski(sK1),sK2,sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3))))
    | ~ spl7_26 ),
    inference(resolution,[],[f519,f29])).

fof(f29,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP5(X4,X2,X1,X0)
      | v1_funct_1(sK6(X0,X1,X2,X4)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f539,plain,
    ( spl7_28
    | ~ spl7_25 ),
    inference(avatar_split_clause,[],[f532,f515,f537])).

fof(f532,plain,
    ( v1_funct_1(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)))
    | ~ spl7_25 ),
    inference(forward_demodulation,[],[f527,f526])).

fof(f527,plain,
    ( v1_funct_1(sK6(sK0,k1_tarski(sK1),sK3,sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3))))
    | ~ spl7_25 ),
    inference(resolution,[],[f516,f29])).

fof(f520,plain,
    ( spl7_25
    | spl7_26
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f491,f112,f105,f71,f67,f59,f55,f518,f515])).

fof(f491,plain,
    ( sP5(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),sK2,k1_tarski(sK1),sK0)
    | sP5(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),sK3,k1_tarski(sK1),sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f489,f106])).

fof(f489,plain,
    ( sP5(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),sK2,k1_tarski(sK1),sK0)
    | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(sK3)
    | sP5(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),sK3,k1_tarski(sK1),sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_8 ),
    inference(resolution,[],[f103,f458])).

fof(f458,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_tarski(sK3))
        | sP5(X0,sK3,k1_tarski(sK1),sK0) )
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f457,f56])).

fof(f457,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_tarski(sK3))
        | sP5(X0,sK3,k1_tarski(sK1),sK0)
        | ~ v1_funct_1(sK3) )
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f456,f68])).

fof(f456,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_tarski(sK3))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | sP5(X0,sK3,k1_tarski(sK1),sK0)
        | ~ v1_funct_1(sK3) )
    | ~ spl7_8 ),
    inference(superposition,[],[f48,f449])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP5(X4,X2,X1,X0)
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP5(X4,X2,X1,X0)
      | ~ r2_hidden(X4,X3)
      | k5_partfun1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f103,plain,
    ( ! [X4] :
        ( sP5(sK4(sK0,k1_tarski(sK1),sK2,X4),sK2,k1_tarski(sK1),sK0)
        | r2_hidden(sK4(sK0,k1_tarski(sK1),sK2,X4),X4)
        | k5_partfun1(sK0,k1_tarski(sK1),sK2) = X4 )
    | ~ spl7_2
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f95,f60])).

fof(f95,plain,
    ( ! [X4] :
        ( ~ v1_funct_1(sK2)
        | sP5(sK4(sK0,k1_tarski(sK1),sK2,X4),sK2,k1_tarski(sK1),sK0)
        | r2_hidden(sK4(sK0,k1_tarski(sK1),sK2,X4),X4)
        | k5_partfun1(sK0,k1_tarski(sK1),sK2) = X4 )
    | ~ spl7_5 ),
    inference(resolution,[],[f72,f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | sP5(sK4(X0,X1,X2,X3),X2,X1,X0)
      | r2_hidden(sK4(X0,X1,X2,X3),X3)
      | k5_partfun1(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f453,plain,
    ( spl7_8
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f451,f429,f67,f55,f112])).

fof(f429,plain,
    ( spl7_19
  <=> sP5(sK3,sK3,k1_tarski(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f451,plain,
    ( k1_tarski(sK3) = k5_partfun1(sK0,k1_tarski(sK1),sK3)
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_19 ),
    inference(subsumption_resolution,[],[f450,f445])).

fof(f445,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ spl7_19 ),
    inference(forward_demodulation,[],[f441,f438])).

fof(f438,plain,
    ( sK3 = sK6(sK0,k1_tarski(sK1),sK3,sK3)
    | ~ spl7_19 ),
    inference(resolution,[],[f430,f31])).

fof(f430,plain,
    ( sP5(sK3,sK3,k1_tarski(sK1),sK0)
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f429])).

fof(f441,plain,
    ( v1_partfun1(sK6(sK0,k1_tarski(sK1),sK3,sK3),sK0)
    | ~ spl7_19 ),
    inference(resolution,[],[f430,f32])).

fof(f450,plain,
    ( k1_tarski(sK3) = k5_partfun1(sK0,k1_tarski(sK1),sK3)
    | ~ v1_partfun1(sK3,sK0)
    | ~ spl7_1
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f397,f56])).

fof(f397,plain,
    ( ~ v1_funct_1(sK3)
    | k1_tarski(sK3) = k5_partfun1(sK0,k1_tarski(sK1),sK3)
    | ~ v1_partfun1(sK3,sK0)
    | ~ spl7_4 ),
    inference(resolution,[],[f41,f68])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k5_partfun1(X0,X1,X2) = k1_tarski(X2)
      | ~ v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( v1_partfun1(X2,X0)
      <=> k5_partfun1(X0,X1,X2) = k1_tarski(X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( v1_partfun1(X2,X0)
      <=> k5_partfun1(X0,X1,X2) = k1_tarski(X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( v1_partfun1(X2,X0)
      <=> k5_partfun1(X0,X1,X2) = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_partfun1)).

fof(f431,plain,
    ( spl7_19
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_17 ),
    inference(avatar_split_clause,[],[f423,f418,f67,f55,f429])).

fof(f418,plain,
    ( spl7_17
  <=> r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f423,plain,
    ( sP5(sK3,sK3,k1_tarski(sK1),sK0)
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f422,f56])).

fof(f422,plain,
    ( sP5(sK3,sK3,k1_tarski(sK1),sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl7_4
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f421,f68])).

fof(f421,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | sP5(sK3,sK3,k1_tarski(sK1),sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl7_17 ),
    inference(resolution,[],[f419,f48])).

fof(f419,plain,
    ( r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK3))
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f418])).

fof(f420,plain,
    ( spl7_17
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f415,f152,f67,f63,f55,f418])).

fof(f63,plain,
    ( spl7_3
  <=> v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f152,plain,
    ( spl7_15
  <=> ! [X1] :
        ( ~ v1_funct_1(X1)
        | r2_hidden(X1,k5_partfun1(sK0,k1_tarski(sK1),sK3))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | ~ v1_funct_2(X1,sK0,k1_tarski(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f415,plain,
    ( r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK3))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f414,f64])).

fof(f64,plain,
    ( v1_funct_2(sK3,sK0,k1_tarski(sK1))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f414,plain,
    ( r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK3))
    | ~ v1_funct_2(sK3,sK0,k1_tarski(sK1))
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f412,f56])).

fof(f412,plain,
    ( r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,k1_tarski(sK1))
    | ~ spl7_4
    | ~ spl7_15 ),
    inference(resolution,[],[f153,f68])).

fof(f153,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | r2_hidden(X1,k5_partfun1(sK0,k1_tarski(sK1),sK3))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,sK0,k1_tarski(sK1)) )
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f152])).

fof(f379,plain,
    ( spl7_6
    | ~ spl7_14 ),
    inference(avatar_contradiction_clause,[],[f378])).

fof(f378,plain,
    ( $false
    | spl7_6
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f313,f235])).

fof(f235,plain,
    ( ! [X0,X1] : X0 = X1
    | ~ spl7_14 ),
    inference(superposition,[],[f176,f176])).

fof(f176,plain,
    ( ! [X4] : k1_xboole_0 = X4
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f169,f53])).

fof(f53,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f169,plain,
    ( ! [X4] :
        ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X4)
        | k1_xboole_0 = X4 )
    | ~ spl7_14 ),
    inference(superposition,[],[f43,f150])).

fof(f150,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl7_14
  <=> k1_xboole_0 = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
     => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).

fof(f313,plain,
    ( k1_tarski(sK3) != k5_partfun1(sK0,k1_tarski(sK1),k1_xboole_0)
    | spl7_6
    | ~ spl7_14 ),
    inference(superposition,[],[f106,f176])).

fof(f154,plain,
    ( spl7_14
    | spl7_15
    | ~ spl7_1
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f85,f67,f55,f152,f149])).

fof(f85,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,sK0,k1_tarski(sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | k1_xboole_0 = k1_tarski(sK1)
        | r2_hidden(X1,k5_partfun1(sK0,k1_tarski(sK1),sK3)) )
    | ~ spl7_1
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f84,f81])).

fof(f84,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,sK0,k1_tarski(sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | ~ r1_partfun1(sK3,X1)
        | k1_xboole_0 = k1_tarski(sK1)
        | r2_hidden(X1,k5_partfun1(sK0,k1_tarski(sK1),sK3)) )
    | ~ spl7_1
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f77,f56])).

fof(f77,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(sK3)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,sK0,k1_tarski(sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | ~ r1_partfun1(sK3,X1)
        | k1_xboole_0 = k1_tarski(sK1)
        | r2_hidden(X1,k5_partfun1(sK0,k1_tarski(sK1),sK3)) )
    | ~ spl7_4 ),
    inference(resolution,[],[f68,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_partfun1(X2,X3)
      | k1_xboole_0 = X1
      | r2_hidden(X3,k5_partfun1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r1_partfun1(X2,X3)
           => ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
              | ( k1_xboole_0 != X0
                & k1_xboole_0 = X1 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_2)).

fof(f107,plain,(
    ~ spl7_6 ),
    inference(avatar_split_clause,[],[f25,f105])).

fof(f25,plain,(
    k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
              & v1_funct_2(X3,X0,k1_tarski(X1))
              & v1_funct_1(X3) )
           => k5_partfun1(X0,k1_tarski(X1),X2) = k1_tarski(X3) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
         => k5_partfun1(X0,k1_tarski(X1),X2) = k1_tarski(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_2)).

fof(f73,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f27,f71])).

fof(f27,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f12])).

fof(f69,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f24,f67])).

fof(f24,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f12])).

fof(f65,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f23,f63])).

fof(f23,plain,(
    v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f61,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f26,f59])).

fof(f26,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f57,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f22,f55])).

fof(f22,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:00:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (17673)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (17692)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (17684)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (17698)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.52  % (17690)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.52  % (17675)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (17672)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (17674)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (17673)Refutation not found, incomplete strategy% (17673)------------------------------
% 0.21/0.54  % (17673)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (17673)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (17673)Memory used [KB]: 1918
% 0.21/0.54  % (17673)Time elapsed: 0.114 s
% 0.21/0.54  % (17673)------------------------------
% 0.21/0.54  % (17673)------------------------------
% 0.21/0.54  % (17695)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (17670)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.55  % (17693)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.55  % (17697)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (17678)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (17697)Refutation not found, incomplete strategy% (17697)------------------------------
% 0.21/0.55  % (17697)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (17697)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (17697)Memory used [KB]: 6268
% 0.21/0.55  % (17697)Time elapsed: 0.129 s
% 0.21/0.55  % (17697)------------------------------
% 0.21/0.55  % (17697)------------------------------
% 0.21/0.55  % (17676)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.55  % (17669)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.55  % (17699)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (17682)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.55  % (17677)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.55  % (17679)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.55  % (17689)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (17691)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (17688)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.56  % (17696)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (17694)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.56  % (17685)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.56  % (17694)Refutation not found, incomplete strategy% (17694)------------------------------
% 0.21/0.56  % (17694)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (17694)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (17694)Memory used [KB]: 10746
% 0.21/0.56  % (17694)Time elapsed: 0.137 s
% 0.21/0.56  % (17694)------------------------------
% 0.21/0.56  % (17694)------------------------------
% 0.21/0.56  % (17683)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.56  % (17687)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.56  % (17686)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.56  % (17680)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.57  % (17671)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.57  % (17699)Refutation not found, incomplete strategy% (17699)------------------------------
% 0.21/0.57  % (17699)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (17699)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (17699)Memory used [KB]: 1791
% 0.21/0.57  % (17699)Time elapsed: 0.148 s
% 0.21/0.57  % (17699)------------------------------
% 0.21/0.57  % (17699)------------------------------
% 0.21/0.58  % (17686)Refutation not found, incomplete strategy% (17686)------------------------------
% 0.21/0.58  % (17686)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (17686)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (17686)Memory used [KB]: 10746
% 0.21/0.58  % (17686)Time elapsed: 0.160 s
% 0.21/0.58  % (17686)------------------------------
% 0.21/0.58  % (17686)------------------------------
% 2.02/0.66  % (17672)Refutation not found, incomplete strategy% (17672)------------------------------
% 2.02/0.66  % (17672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.02/0.66  % (17672)Termination reason: Refutation not found, incomplete strategy
% 2.02/0.66  
% 2.02/0.66  % (17672)Memory used [KB]: 6140
% 2.02/0.66  % (17672)Time elapsed: 0.238 s
% 2.02/0.66  % (17672)------------------------------
% 2.02/0.66  % (17672)------------------------------
% 2.02/0.68  % (17709)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.02/0.68  % (17710)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.02/0.69  % (17696)Refutation found. Thanks to Tanya!
% 2.02/0.69  % SZS status Theorem for theBenchmark
% 2.02/0.69  % SZS output start Proof for theBenchmark
% 2.02/0.69  fof(f1399,plain,(
% 2.02/0.69    $false),
% 2.02/0.69    inference(avatar_sat_refutation,[],[f57,f61,f65,f69,f73,f107,f154,f379,f420,f431,f453,f520,f539,f554,f583,f638,f694,f770,f1270,f1285,f1287,f1292,f1386,f1398])).
% 2.02/0.69  fof(f1398,plain,(
% 2.02/0.69    spl7_30 | ~spl7_25),
% 2.02/0.69    inference(avatar_split_clause,[],[f534,f515,f581])).
% 2.02/0.69  fof(f581,plain,(
% 2.02/0.69    spl7_30 <=> v1_partfun1(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),sK0)),
% 2.02/0.69    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).
% 2.02/0.69  fof(f515,plain,(
% 2.02/0.69    spl7_25 <=> sP5(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),sK3,k1_tarski(sK1),sK0)),
% 2.02/0.69    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 2.02/0.69  fof(f534,plain,(
% 2.02/0.69    v1_partfun1(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),sK0) | ~spl7_25),
% 2.02/0.69    inference(forward_demodulation,[],[f529,f526])).
% 2.02/0.69  fof(f526,plain,(
% 2.02/0.69    sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)) = sK6(sK0,k1_tarski(sK1),sK3,sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3))) | ~spl7_25),
% 2.02/0.69    inference(resolution,[],[f516,f31])).
% 2.02/0.69  fof(f31,plain,(
% 2.02/0.69    ( ! [X4,X2,X0,X1] : (~sP5(X4,X2,X1,X0) | sK6(X0,X1,X2,X4) = X4) )),
% 2.02/0.69    inference(cnf_transformation,[],[f14])).
% 2.02/0.69  fof(f14,plain,(
% 2.02/0.69    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.02/0.69    inference(flattening,[],[f13])).
% 2.02/0.69  fof(f13,plain,(
% 2.02/0.69    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.02/0.69    inference(ennf_transformation,[],[f5])).
% 2.02/0.69  fof(f5,axiom,(
% 2.02/0.69    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))))),
% 2.02/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_partfun1)).
% 2.02/0.69  fof(f516,plain,(
% 2.02/0.69    sP5(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),sK3,k1_tarski(sK1),sK0) | ~spl7_25),
% 2.02/0.69    inference(avatar_component_clause,[],[f515])).
% 2.02/0.69  fof(f529,plain,(
% 2.02/0.69    v1_partfun1(sK6(sK0,k1_tarski(sK1),sK3,sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3))),sK0) | ~spl7_25),
% 2.02/0.69    inference(resolution,[],[f516,f32])).
% 2.02/0.69  fof(f32,plain,(
% 2.02/0.69    ( ! [X4,X2,X0,X1] : (~sP5(X4,X2,X1,X0) | v1_partfun1(sK6(X0,X1,X2,X4),X0)) )),
% 2.02/0.69    inference(cnf_transformation,[],[f14])).
% 2.02/0.69  fof(f1386,plain,(
% 2.02/0.69    spl7_31 | ~spl7_2 | ~spl7_5 | ~spl7_28 | ~spl7_34),
% 2.02/0.69    inference(avatar_split_clause,[],[f1324,f692,f537,f71,f59,f588])).
% 2.02/0.69  fof(f588,plain,(
% 2.02/0.69    spl7_31 <=> r1_partfun1(sK2,sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)))),
% 2.02/0.69    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 2.02/0.69  fof(f59,plain,(
% 2.02/0.69    spl7_2 <=> v1_funct_1(sK2)),
% 2.02/0.69    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 2.02/0.69  fof(f71,plain,(
% 2.02/0.69    spl7_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 2.02/0.69    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 2.02/0.69  fof(f537,plain,(
% 2.02/0.69    spl7_28 <=> v1_funct_1(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)))),
% 2.02/0.69    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 2.02/0.69  fof(f692,plain,(
% 2.02/0.69    spl7_34 <=> m1_subset_1(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 2.02/0.69    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).
% 2.02/0.69  fof(f1324,plain,(
% 2.02/0.69    r1_partfun1(sK2,sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3))) | (~spl7_2 | ~spl7_5 | ~spl7_28 | ~spl7_34)),
% 2.02/0.69    inference(subsumption_resolution,[],[f1298,f538])).
% 2.02/0.69  fof(f538,plain,(
% 2.02/0.69    v1_funct_1(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3))) | ~spl7_28),
% 2.02/0.69    inference(avatar_component_clause,[],[f537])).
% 2.02/0.69  fof(f1298,plain,(
% 2.02/0.69    ~v1_funct_1(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3))) | r1_partfun1(sK2,sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3))) | (~spl7_2 | ~spl7_5 | ~spl7_34)),
% 2.02/0.69    inference(resolution,[],[f693,f96])).
% 2.02/0.69  fof(f96,plain,(
% 2.02/0.69    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~v1_funct_1(X0) | r1_partfun1(sK2,X0)) ) | (~spl7_2 | ~spl7_5)),
% 2.02/0.69    inference(subsumption_resolution,[],[f89,f60])).
% 2.02/0.69  fof(f60,plain,(
% 2.02/0.69    v1_funct_1(sK2) | ~spl7_2),
% 2.02/0.69    inference(avatar_component_clause,[],[f59])).
% 2.02/0.69  fof(f89,plain,(
% 2.02/0.69    ( ! [X0] : (~v1_funct_1(sK2) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | r1_partfun1(sK2,X0)) ) | ~spl7_5),
% 2.02/0.69    inference(resolution,[],[f72,f42])).
% 2.02/0.69  fof(f42,plain,(
% 2.02/0.69    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | r1_partfun1(X2,X3)) )),
% 2.02/0.69    inference(cnf_transformation,[],[f20])).
% 2.02/0.69  fof(f20,plain,(
% 2.02/0.69    ! [X0,X1,X2] : (! [X3] : (r1_partfun1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2))),
% 2.02/0.69    inference(flattening,[],[f19])).
% 2.02/0.69  fof(f19,plain,(
% 2.02/0.69    ! [X0,X1,X2] : (! [X3] : (r1_partfun1(X2,X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2)))),
% 2.02/0.69    inference(ennf_transformation,[],[f6])).
% 2.02/0.69  fof(f6,axiom,(
% 2.02/0.69    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X3)) => r1_partfun1(X2,X3)))),
% 2.02/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_partfun1)).
% 2.02/0.69  fof(f72,plain,(
% 2.02/0.69    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~spl7_5),
% 2.02/0.69    inference(avatar_component_clause,[],[f71])).
% 2.02/0.69  fof(f693,plain,(
% 2.02/0.69    m1_subset_1(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~spl7_34),
% 2.02/0.69    inference(avatar_component_clause,[],[f692])).
% 2.02/0.69  fof(f1292,plain,(
% 2.02/0.69    spl7_34 | ~spl7_25),
% 2.02/0.69    inference(avatar_split_clause,[],[f1281,f515,f692])).
% 2.02/0.69  fof(f1281,plain,(
% 2.02/0.69    m1_subset_1(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~spl7_25),
% 2.02/0.69    inference(forward_demodulation,[],[f1276,f1274])).
% 2.02/0.69  fof(f1274,plain,(
% 2.02/0.69    sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)) = sK6(sK0,k1_tarski(sK1),sK3,sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3))) | ~spl7_25),
% 2.02/0.69    inference(resolution,[],[f516,f31])).
% 2.02/0.69  fof(f1276,plain,(
% 2.02/0.69    m1_subset_1(sK6(sK0,k1_tarski(sK1),sK3,sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3))),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~spl7_25),
% 2.02/0.69    inference(resolution,[],[f516,f30])).
% 2.02/0.69  fof(f30,plain,(
% 2.02/0.69    ( ! [X4,X2,X0,X1] : (~sP5(X4,X2,X1,X0) | m1_subset_1(sK6(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.02/0.69    inference(cnf_transformation,[],[f14])).
% 2.02/0.69  fof(f1287,plain,(
% 2.02/0.69    spl7_26 | ~spl7_28 | ~spl7_30 | ~spl7_31 | ~spl7_34),
% 2.02/0.69    inference(avatar_split_clause,[],[f1244,f692,f588,f581,f537,f518])).
% 2.02/0.69  fof(f518,plain,(
% 2.02/0.69    spl7_26 <=> sP5(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),sK2,k1_tarski(sK1),sK0)),
% 2.02/0.69    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 2.02/0.69  fof(f1244,plain,(
% 2.02/0.69    sP5(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),sK2,k1_tarski(sK1),sK0) | (~spl7_28 | ~spl7_30 | ~spl7_31 | ~spl7_34)),
% 2.02/0.69    inference(resolution,[],[f753,f589])).
% 2.02/0.69  fof(f589,plain,(
% 2.02/0.69    r1_partfun1(sK2,sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3))) | ~spl7_31),
% 2.02/0.69    inference(avatar_component_clause,[],[f588])).
% 2.02/0.69  fof(f753,plain,(
% 2.02/0.69    ( ! [X4] : (~r1_partfun1(X4,sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3))) | sP5(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),X4,k1_tarski(sK1),sK0)) ) | (~spl7_28 | ~spl7_30 | ~spl7_34)),
% 2.02/0.69    inference(subsumption_resolution,[],[f752,f582])).
% 2.02/0.69  fof(f582,plain,(
% 2.02/0.69    v1_partfun1(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),sK0) | ~spl7_30),
% 2.02/0.69    inference(avatar_component_clause,[],[f581])).
% 2.02/0.69  fof(f752,plain,(
% 2.02/0.69    ( ! [X4] : (~v1_partfun1(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),sK0) | ~r1_partfun1(X4,sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3))) | sP5(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),X4,k1_tarski(sK1),sK0)) ) | (~spl7_28 | ~spl7_34)),
% 2.02/0.69    inference(subsumption_resolution,[],[f737,f538])).
% 2.02/0.69  fof(f737,plain,(
% 2.02/0.69    ( ! [X4] : (~v1_funct_1(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3))) | ~v1_partfun1(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),sK0) | ~r1_partfun1(X4,sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3))) | sP5(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),X4,k1_tarski(sK1),sK0)) ) | ~spl7_34),
% 2.02/0.69    inference(resolution,[],[f693,f50])).
% 2.02/0.69  fof(f50,plain,(
% 2.02/0.69    ( ! [X2,X0,X5,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~v1_partfun1(X5,X0) | ~r1_partfun1(X2,X5) | sP5(X5,X2,X1,X0)) )),
% 2.02/0.69    inference(equality_resolution,[],[f28])).
% 2.02/0.69  fof(f28,plain,(
% 2.02/0.69    ( ! [X4,X2,X0,X5,X1] : (~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X4 != X5 | ~v1_partfun1(X5,X0) | ~r1_partfun1(X2,X5) | sP5(X4,X2,X1,X0)) )),
% 2.02/0.69    inference(cnf_transformation,[],[f14])).
% 2.02/0.69  fof(f1285,plain,(
% 2.02/0.69    spl7_32 | ~spl7_1 | ~spl7_4 | ~spl7_8 | ~spl7_25),
% 2.02/0.69    inference(avatar_split_clause,[],[f531,f515,f112,f67,f55,f636])).
% 2.02/0.69  fof(f636,plain,(
% 2.02/0.69    spl7_32 <=> r2_hidden(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),k1_tarski(sK3))),
% 2.02/0.69    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).
% 2.02/0.69  fof(f55,plain,(
% 2.02/0.69    spl7_1 <=> v1_funct_1(sK3)),
% 2.02/0.69    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 2.02/0.69  fof(f67,plain,(
% 2.02/0.69    spl7_4 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 2.02/0.69    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 2.02/0.69  fof(f112,plain,(
% 2.02/0.69    spl7_8 <=> k1_tarski(sK3) = k5_partfun1(sK0,k1_tarski(sK1),sK3)),
% 2.02/0.69    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 2.02/0.69  fof(f531,plain,(
% 2.02/0.69    r2_hidden(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),k1_tarski(sK3)) | (~spl7_1 | ~spl7_4 | ~spl7_8 | ~spl7_25)),
% 2.02/0.69    inference(forward_demodulation,[],[f525,f449])).
% 2.02/0.69  fof(f449,plain,(
% 2.02/0.69    k1_tarski(sK3) = k5_partfun1(sK0,k1_tarski(sK1),sK3) | ~spl7_8),
% 2.02/0.69    inference(avatar_component_clause,[],[f112])).
% 2.02/0.69  fof(f525,plain,(
% 2.02/0.69    r2_hidden(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),k5_partfun1(sK0,k1_tarski(sK1),sK3)) | (~spl7_1 | ~spl7_4 | ~spl7_25)),
% 2.02/0.69    inference(resolution,[],[f516,f87])).
% 2.02/0.69  fof(f87,plain,(
% 2.02/0.69    ( ! [X3] : (~sP5(X3,sK3,k1_tarski(sK1),sK0) | r2_hidden(X3,k5_partfun1(sK0,k1_tarski(sK1),sK3))) ) | (~spl7_1 | ~spl7_4)),
% 2.02/0.69    inference(subsumption_resolution,[],[f79,f56])).
% 2.02/0.69  fof(f56,plain,(
% 2.02/0.69    v1_funct_1(sK3) | ~spl7_1),
% 2.02/0.69    inference(avatar_component_clause,[],[f55])).
% 2.02/0.69  fof(f79,plain,(
% 2.02/0.69    ( ! [X3] : (~v1_funct_1(sK3) | ~sP5(X3,sK3,k1_tarski(sK1),sK0) | r2_hidden(X3,k5_partfun1(sK0,k1_tarski(sK1),sK3))) ) | ~spl7_4),
% 2.02/0.69    inference(resolution,[],[f68,f49])).
% 2.02/0.69  fof(f49,plain,(
% 2.02/0.69    ( ! [X4,X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~sP5(X4,X2,X1,X0) | r2_hidden(X4,k5_partfun1(X0,X1,X2))) )),
% 2.02/0.69    inference(equality_resolution,[],[f34])).
% 2.02/0.69  fof(f34,plain,(
% 2.02/0.69    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~sP5(X4,X2,X1,X0) | r2_hidden(X4,X3) | k5_partfun1(X0,X1,X2) != X3) )),
% 2.02/0.69    inference(cnf_transformation,[],[f14])).
% 2.02/0.69  fof(f68,plain,(
% 2.02/0.69    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~spl7_4),
% 2.02/0.69    inference(avatar_component_clause,[],[f67])).
% 2.02/0.69  fof(f1270,plain,(
% 2.02/0.69    spl7_25 | ~spl7_28 | ~spl7_30 | ~spl7_34 | ~spl7_36),
% 2.02/0.69    inference(avatar_split_clause,[],[f1243,f768,f692,f581,f537,f515])).
% 2.02/0.69  fof(f768,plain,(
% 2.02/0.69    spl7_36 <=> r1_partfun1(sK3,sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)))),
% 2.02/0.69    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).
% 2.02/0.69  fof(f1243,plain,(
% 2.02/0.69    sP5(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),sK3,k1_tarski(sK1),sK0) | (~spl7_28 | ~spl7_30 | ~spl7_34 | ~spl7_36)),
% 2.02/0.69    inference(resolution,[],[f753,f769])).
% 2.02/0.69  fof(f769,plain,(
% 2.02/0.69    r1_partfun1(sK3,sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3))) | ~spl7_36),
% 2.02/0.69    inference(avatar_component_clause,[],[f768])).
% 2.02/0.69  fof(f770,plain,(
% 2.02/0.69    spl7_36 | ~spl7_1 | ~spl7_4 | ~spl7_28 | ~spl7_34),
% 2.02/0.69    inference(avatar_split_clause,[],[f743,f692,f537,f67,f55,f768])).
% 2.02/0.69  fof(f743,plain,(
% 2.02/0.69    r1_partfun1(sK3,sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3))) | (~spl7_1 | ~spl7_4 | ~spl7_28 | ~spl7_34)),
% 2.02/0.69    inference(subsumption_resolution,[],[f730,f538])).
% 2.02/0.69  fof(f730,plain,(
% 2.02/0.69    ~v1_funct_1(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3))) | r1_partfun1(sK3,sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3))) | (~spl7_1 | ~spl7_4 | ~spl7_34)),
% 2.02/0.69    inference(resolution,[],[f693,f81])).
% 2.02/0.69  fof(f81,plain,(
% 2.02/0.69    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~v1_funct_1(X0) | r1_partfun1(sK3,X0)) ) | (~spl7_1 | ~spl7_4)),
% 2.02/0.69    inference(subsumption_resolution,[],[f74,f56])).
% 2.02/0.69  fof(f74,plain,(
% 2.02/0.69    ( ! [X0] : (~v1_funct_1(sK3) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | r1_partfun1(sK3,X0)) ) | ~spl7_4),
% 2.02/0.69    inference(resolution,[],[f68,f42])).
% 2.02/0.69  fof(f694,plain,(
% 2.02/0.69    spl7_34 | ~spl7_26),
% 2.02/0.69    inference(avatar_split_clause,[],[f551,f518,f692])).
% 2.02/0.69  fof(f551,plain,(
% 2.02/0.69    m1_subset_1(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~spl7_26),
% 2.02/0.69    inference(forward_demodulation,[],[f544,f542])).
% 2.02/0.69  fof(f542,plain,(
% 2.02/0.69    sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)) = sK6(sK0,k1_tarski(sK1),sK2,sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3))) | ~spl7_26),
% 2.02/0.69    inference(resolution,[],[f519,f31])).
% 2.02/0.69  fof(f519,plain,(
% 2.02/0.69    sP5(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),sK2,k1_tarski(sK1),sK0) | ~spl7_26),
% 2.02/0.69    inference(avatar_component_clause,[],[f518])).
% 2.02/0.69  fof(f544,plain,(
% 2.02/0.69    m1_subset_1(sK6(sK0,k1_tarski(sK1),sK2,sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3))),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~spl7_26),
% 2.02/0.69    inference(resolution,[],[f519,f30])).
% 2.02/0.69  fof(f638,plain,(
% 2.02/0.69    ~spl7_32 | ~spl7_2 | ~spl7_5 | spl7_6 | ~spl7_26),
% 2.02/0.69    inference(avatar_split_clause,[],[f549,f518,f105,f71,f59,f636])).
% 2.02/0.69  fof(f105,plain,(
% 2.02/0.69    spl7_6 <=> k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(sK3)),
% 2.02/0.69    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 2.02/0.69  fof(f549,plain,(
% 2.02/0.69    ~r2_hidden(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),k1_tarski(sK3)) | (~spl7_2 | ~spl7_5 | spl7_6 | ~spl7_26)),
% 2.02/0.69    inference(subsumption_resolution,[],[f548,f106])).
% 2.02/0.69  fof(f106,plain,(
% 2.02/0.69    k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3) | spl7_6),
% 2.02/0.69    inference(avatar_component_clause,[],[f105])).
% 2.02/0.69  fof(f548,plain,(
% 2.02/0.69    ~r2_hidden(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),k1_tarski(sK3)) | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(sK3) | (~spl7_2 | ~spl7_5 | ~spl7_26)),
% 2.02/0.69    inference(subsumption_resolution,[],[f547,f60])).
% 2.02/0.69  fof(f547,plain,(
% 2.02/0.69    ~v1_funct_1(sK2) | ~r2_hidden(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),k1_tarski(sK3)) | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(sK3) | (~spl7_5 | ~spl7_26)),
% 2.02/0.69    inference(subsumption_resolution,[],[f540,f72])).
% 2.02/0.69  fof(f540,plain,(
% 2.02/0.69    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~v1_funct_1(sK2) | ~r2_hidden(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),k1_tarski(sK3)) | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(sK3) | ~spl7_26),
% 2.02/0.69    inference(resolution,[],[f519,f37])).
% 2.02/0.69  fof(f37,plain,(
% 2.02/0.69    ( ! [X2,X0,X3,X1] : (~sP5(sK4(X0,X1,X2,X3),X2,X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~r2_hidden(sK4(X0,X1,X2,X3),X3) | k5_partfun1(X0,X1,X2) = X3) )),
% 2.02/0.69    inference(cnf_transformation,[],[f14])).
% 2.02/0.69  fof(f583,plain,(
% 2.02/0.69    spl7_30 | ~spl7_26),
% 2.02/0.69    inference(avatar_split_clause,[],[f552,f518,f581])).
% 2.02/0.69  fof(f552,plain,(
% 2.02/0.69    v1_partfun1(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),sK0) | ~spl7_26),
% 2.02/0.69    inference(forward_demodulation,[],[f545,f542])).
% 2.02/0.69  fof(f545,plain,(
% 2.02/0.69    v1_partfun1(sK6(sK0,k1_tarski(sK1),sK2,sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3))),sK0) | ~spl7_26),
% 2.02/0.69    inference(resolution,[],[f519,f32])).
% 2.02/0.69  fof(f554,plain,(
% 2.02/0.69    spl7_28 | ~spl7_26),
% 2.02/0.69    inference(avatar_split_clause,[],[f550,f518,f537])).
% 2.02/0.69  fof(f550,plain,(
% 2.02/0.69    v1_funct_1(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3))) | ~spl7_26),
% 2.02/0.69    inference(forward_demodulation,[],[f543,f542])).
% 2.02/0.69  fof(f543,plain,(
% 2.02/0.69    v1_funct_1(sK6(sK0,k1_tarski(sK1),sK2,sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)))) | ~spl7_26),
% 2.02/0.69    inference(resolution,[],[f519,f29])).
% 2.02/0.69  fof(f29,plain,(
% 2.02/0.69    ( ! [X4,X2,X0,X1] : (~sP5(X4,X2,X1,X0) | v1_funct_1(sK6(X0,X1,X2,X4))) )),
% 2.02/0.69    inference(cnf_transformation,[],[f14])).
% 2.02/0.69  fof(f539,plain,(
% 2.02/0.69    spl7_28 | ~spl7_25),
% 2.02/0.69    inference(avatar_split_clause,[],[f532,f515,f537])).
% 2.02/0.69  fof(f532,plain,(
% 2.02/0.69    v1_funct_1(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3))) | ~spl7_25),
% 2.02/0.69    inference(forward_demodulation,[],[f527,f526])).
% 2.02/0.69  fof(f527,plain,(
% 2.02/0.69    v1_funct_1(sK6(sK0,k1_tarski(sK1),sK3,sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)))) | ~spl7_25),
% 2.02/0.69    inference(resolution,[],[f516,f29])).
% 2.02/0.69  fof(f520,plain,(
% 2.02/0.69    spl7_25 | spl7_26 | ~spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_5 | spl7_6 | ~spl7_8),
% 2.02/0.69    inference(avatar_split_clause,[],[f491,f112,f105,f71,f67,f59,f55,f518,f515])).
% 2.02/0.69  fof(f491,plain,(
% 2.02/0.69    sP5(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),sK2,k1_tarski(sK1),sK0) | sP5(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),sK3,k1_tarski(sK1),sK0) | (~spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_5 | spl7_6 | ~spl7_8)),
% 2.02/0.69    inference(subsumption_resolution,[],[f489,f106])).
% 2.02/0.69  fof(f489,plain,(
% 2.02/0.69    sP5(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),sK2,k1_tarski(sK1),sK0) | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(sK3) | sP5(sK4(sK0,k1_tarski(sK1),sK2,k1_tarski(sK3)),sK3,k1_tarski(sK1),sK0) | (~spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_5 | ~spl7_8)),
% 2.02/0.69    inference(resolution,[],[f103,f458])).
% 2.02/0.69  fof(f458,plain,(
% 2.02/0.69    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK3)) | sP5(X0,sK3,k1_tarski(sK1),sK0)) ) | (~spl7_1 | ~spl7_4 | ~spl7_8)),
% 2.02/0.69    inference(subsumption_resolution,[],[f457,f56])).
% 2.02/0.69  fof(f457,plain,(
% 2.02/0.69    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK3)) | sP5(X0,sK3,k1_tarski(sK1),sK0) | ~v1_funct_1(sK3)) ) | (~spl7_4 | ~spl7_8)),
% 2.02/0.69    inference(subsumption_resolution,[],[f456,f68])).
% 2.02/0.69  fof(f456,plain,(
% 2.02/0.69    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | sP5(X0,sK3,k1_tarski(sK1),sK0) | ~v1_funct_1(sK3)) ) | ~spl7_8),
% 2.02/0.69    inference(superposition,[],[f48,f449])).
% 2.02/0.69  fof(f48,plain,(
% 2.02/0.69    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP5(X4,X2,X1,X0) | ~v1_funct_1(X2)) )),
% 2.02/0.69    inference(equality_resolution,[],[f35])).
% 2.02/0.69  fof(f35,plain,(
% 2.02/0.69    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP5(X4,X2,X1,X0) | ~r2_hidden(X4,X3) | k5_partfun1(X0,X1,X2) != X3) )),
% 2.02/0.69    inference(cnf_transformation,[],[f14])).
% 2.02/0.69  fof(f103,plain,(
% 2.02/0.69    ( ! [X4] : (sP5(sK4(sK0,k1_tarski(sK1),sK2,X4),sK2,k1_tarski(sK1),sK0) | r2_hidden(sK4(sK0,k1_tarski(sK1),sK2,X4),X4) | k5_partfun1(sK0,k1_tarski(sK1),sK2) = X4) ) | (~spl7_2 | ~spl7_5)),
% 2.02/0.69    inference(subsumption_resolution,[],[f95,f60])).
% 2.02/0.69  fof(f95,plain,(
% 2.02/0.69    ( ! [X4] : (~v1_funct_1(sK2) | sP5(sK4(sK0,k1_tarski(sK1),sK2,X4),sK2,k1_tarski(sK1),sK0) | r2_hidden(sK4(sK0,k1_tarski(sK1),sK2,X4),X4) | k5_partfun1(sK0,k1_tarski(sK1),sK2) = X4) ) | ~spl7_5),
% 2.02/0.69    inference(resolution,[],[f72,f36])).
% 2.02/0.69  fof(f36,plain,(
% 2.02/0.69    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | sP5(sK4(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK4(X0,X1,X2,X3),X3) | k5_partfun1(X0,X1,X2) = X3) )),
% 2.02/0.69    inference(cnf_transformation,[],[f14])).
% 2.02/0.69  fof(f453,plain,(
% 2.02/0.69    spl7_8 | ~spl7_1 | ~spl7_4 | ~spl7_19),
% 2.02/0.69    inference(avatar_split_clause,[],[f451,f429,f67,f55,f112])).
% 2.02/0.69  fof(f429,plain,(
% 2.02/0.69    spl7_19 <=> sP5(sK3,sK3,k1_tarski(sK1),sK0)),
% 2.02/0.69    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 2.02/0.69  fof(f451,plain,(
% 2.02/0.69    k1_tarski(sK3) = k5_partfun1(sK0,k1_tarski(sK1),sK3) | (~spl7_1 | ~spl7_4 | ~spl7_19)),
% 2.02/0.69    inference(subsumption_resolution,[],[f450,f445])).
% 2.02/0.69  fof(f445,plain,(
% 2.02/0.69    v1_partfun1(sK3,sK0) | ~spl7_19),
% 2.02/0.69    inference(forward_demodulation,[],[f441,f438])).
% 2.02/0.69  fof(f438,plain,(
% 2.02/0.69    sK3 = sK6(sK0,k1_tarski(sK1),sK3,sK3) | ~spl7_19),
% 2.02/0.69    inference(resolution,[],[f430,f31])).
% 2.02/0.69  fof(f430,plain,(
% 2.02/0.69    sP5(sK3,sK3,k1_tarski(sK1),sK0) | ~spl7_19),
% 2.02/0.69    inference(avatar_component_clause,[],[f429])).
% 2.02/0.69  fof(f441,plain,(
% 2.02/0.69    v1_partfun1(sK6(sK0,k1_tarski(sK1),sK3,sK3),sK0) | ~spl7_19),
% 2.02/0.69    inference(resolution,[],[f430,f32])).
% 2.02/0.69  fof(f450,plain,(
% 2.02/0.69    k1_tarski(sK3) = k5_partfun1(sK0,k1_tarski(sK1),sK3) | ~v1_partfun1(sK3,sK0) | (~spl7_1 | ~spl7_4)),
% 2.02/0.69    inference(subsumption_resolution,[],[f397,f56])).
% 2.02/0.69  fof(f397,plain,(
% 2.02/0.69    ~v1_funct_1(sK3) | k1_tarski(sK3) = k5_partfun1(sK0,k1_tarski(sK1),sK3) | ~v1_partfun1(sK3,sK0) | ~spl7_4),
% 2.02/0.69    inference(resolution,[],[f41,f68])).
% 2.02/0.69  fof(f41,plain,(
% 2.02/0.69    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k5_partfun1(X0,X1,X2) = k1_tarski(X2) | ~v1_partfun1(X2,X0)) )),
% 2.02/0.69    inference(cnf_transformation,[],[f18])).
% 2.02/0.69  fof(f18,plain,(
% 2.02/0.69    ! [X0,X1,X2] : ((v1_partfun1(X2,X0) <=> k5_partfun1(X0,X1,X2) = k1_tarski(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.02/0.69    inference(flattening,[],[f17])).
% 2.02/0.69  fof(f17,plain,(
% 2.02/0.69    ! [X0,X1,X2] : ((v1_partfun1(X2,X0) <=> k5_partfun1(X0,X1,X2) = k1_tarski(X2)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.02/0.69    inference(ennf_transformation,[],[f8])).
% 2.02/0.69  fof(f8,axiom,(
% 2.02/0.69    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) <=> k5_partfun1(X0,X1,X2) = k1_tarski(X2)))),
% 2.02/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_partfun1)).
% 2.02/0.69  fof(f431,plain,(
% 2.02/0.69    spl7_19 | ~spl7_1 | ~spl7_4 | ~spl7_17),
% 2.02/0.69    inference(avatar_split_clause,[],[f423,f418,f67,f55,f429])).
% 2.02/0.69  fof(f418,plain,(
% 2.02/0.69    spl7_17 <=> r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK3))),
% 2.02/0.69    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 2.02/0.69  fof(f423,plain,(
% 2.02/0.69    sP5(sK3,sK3,k1_tarski(sK1),sK0) | (~spl7_1 | ~spl7_4 | ~spl7_17)),
% 2.02/0.69    inference(subsumption_resolution,[],[f422,f56])).
% 2.02/0.69  fof(f422,plain,(
% 2.02/0.69    sP5(sK3,sK3,k1_tarski(sK1),sK0) | ~v1_funct_1(sK3) | (~spl7_4 | ~spl7_17)),
% 2.02/0.69    inference(subsumption_resolution,[],[f421,f68])).
% 2.02/0.69  fof(f421,plain,(
% 2.02/0.69    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | sP5(sK3,sK3,k1_tarski(sK1),sK0) | ~v1_funct_1(sK3) | ~spl7_17),
% 2.02/0.69    inference(resolution,[],[f419,f48])).
% 2.02/0.69  fof(f419,plain,(
% 2.02/0.69    r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK3)) | ~spl7_17),
% 2.02/0.69    inference(avatar_component_clause,[],[f418])).
% 2.02/0.69  fof(f420,plain,(
% 2.02/0.69    spl7_17 | ~spl7_1 | ~spl7_3 | ~spl7_4 | ~spl7_15),
% 2.02/0.69    inference(avatar_split_clause,[],[f415,f152,f67,f63,f55,f418])).
% 2.02/0.69  fof(f63,plain,(
% 2.02/0.69    spl7_3 <=> v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 2.02/0.69    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 2.02/0.69  fof(f152,plain,(
% 2.02/0.69    spl7_15 <=> ! [X1] : (~v1_funct_1(X1) | r2_hidden(X1,k5_partfun1(sK0,k1_tarski(sK1),sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~v1_funct_2(X1,sK0,k1_tarski(sK1)))),
% 2.02/0.69    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 2.02/0.69  fof(f415,plain,(
% 2.02/0.69    r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK3)) | (~spl7_1 | ~spl7_3 | ~spl7_4 | ~spl7_15)),
% 2.02/0.69    inference(subsumption_resolution,[],[f414,f64])).
% 2.02/0.69  fof(f64,plain,(
% 2.02/0.69    v1_funct_2(sK3,sK0,k1_tarski(sK1)) | ~spl7_3),
% 2.02/0.69    inference(avatar_component_clause,[],[f63])).
% 2.02/0.69  fof(f414,plain,(
% 2.02/0.69    r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK3)) | ~v1_funct_2(sK3,sK0,k1_tarski(sK1)) | (~spl7_1 | ~spl7_4 | ~spl7_15)),
% 2.02/0.69    inference(subsumption_resolution,[],[f412,f56])).
% 2.02/0.69  fof(f412,plain,(
% 2.02/0.69    r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK3)) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK0,k1_tarski(sK1)) | (~spl7_4 | ~spl7_15)),
% 2.02/0.69    inference(resolution,[],[f153,f68])).
% 2.02/0.69  fof(f153,plain,(
% 2.02/0.69    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | r2_hidden(X1,k5_partfun1(sK0,k1_tarski(sK1),sK3)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK0,k1_tarski(sK1))) ) | ~spl7_15),
% 2.02/0.69    inference(avatar_component_clause,[],[f152])).
% 2.02/0.69  fof(f379,plain,(
% 2.02/0.69    spl7_6 | ~spl7_14),
% 2.02/0.69    inference(avatar_contradiction_clause,[],[f378])).
% 2.02/0.69  fof(f378,plain,(
% 2.02/0.69    $false | (spl7_6 | ~spl7_14)),
% 2.02/0.69    inference(subsumption_resolution,[],[f313,f235])).
% 2.02/0.69  fof(f235,plain,(
% 2.02/0.69    ( ! [X0,X1] : (X0 = X1) ) | ~spl7_14),
% 2.02/0.69    inference(superposition,[],[f176,f176])).
% 2.02/0.69  fof(f176,plain,(
% 2.02/0.69    ( ! [X4] : (k1_xboole_0 = X4) ) | ~spl7_14),
% 2.02/0.69    inference(subsumption_resolution,[],[f169,f53])).
% 2.02/0.69  fof(f53,plain,(
% 2.02/0.69    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.02/0.69    inference(equality_resolution,[],[f46])).
% 2.02/0.69  fof(f46,plain,(
% 2.02/0.69    ( ! [X0,X1] : (k1_xboole_0 != X0 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 2.02/0.69    inference(cnf_transformation,[],[f3])).
% 2.02/0.69  fof(f3,axiom,(
% 2.02/0.69    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.02/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.02/0.69  fof(f169,plain,(
% 2.02/0.69    ( ! [X4] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X4) | k1_xboole_0 = X4) ) | ~spl7_14),
% 2.02/0.69    inference(superposition,[],[f43,f150])).
% 2.02/0.69  fof(f150,plain,(
% 2.02/0.69    k1_xboole_0 = k1_tarski(sK1) | ~spl7_14),
% 2.02/0.69    inference(avatar_component_clause,[],[f149])).
% 2.02/0.69  fof(f149,plain,(
% 2.02/0.69    spl7_14 <=> k1_xboole_0 = k1_tarski(sK1)),
% 2.02/0.69    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 2.02/0.69  fof(f43,plain,(
% 2.02/0.69    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) | k1_xboole_0 = X0) )),
% 2.02/0.69    inference(cnf_transformation,[],[f21])).
% 2.02/0.69  fof(f21,plain,(
% 2.02/0.69    ! [X0,X1] : ((k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)) | k1_xboole_0 = X0)),
% 2.02/0.69    inference(ennf_transformation,[],[f4])).
% 2.02/0.69  fof(f4,axiom,(
% 2.02/0.69    ! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 2.02/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).
% 2.02/0.69  fof(f313,plain,(
% 2.02/0.69    k1_tarski(sK3) != k5_partfun1(sK0,k1_tarski(sK1),k1_xboole_0) | (spl7_6 | ~spl7_14)),
% 2.02/0.69    inference(superposition,[],[f106,f176])).
% 2.02/0.69  fof(f154,plain,(
% 2.02/0.69    spl7_14 | spl7_15 | ~spl7_1 | ~spl7_4),
% 2.02/0.69    inference(avatar_split_clause,[],[f85,f67,f55,f152,f149])).
% 2.02/0.69  fof(f85,plain,(
% 2.02/0.69    ( ! [X1] : (~v1_funct_1(X1) | ~v1_funct_2(X1,sK0,k1_tarski(sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | k1_xboole_0 = k1_tarski(sK1) | r2_hidden(X1,k5_partfun1(sK0,k1_tarski(sK1),sK3))) ) | (~spl7_1 | ~spl7_4)),
% 2.02/0.69    inference(subsumption_resolution,[],[f84,f81])).
% 2.02/0.69  fof(f84,plain,(
% 2.02/0.69    ( ! [X1] : (~v1_funct_1(X1) | ~v1_funct_2(X1,sK0,k1_tarski(sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~r1_partfun1(sK3,X1) | k1_xboole_0 = k1_tarski(sK1) | r2_hidden(X1,k5_partfun1(sK0,k1_tarski(sK1),sK3))) ) | (~spl7_1 | ~spl7_4)),
% 2.02/0.69    inference(subsumption_resolution,[],[f77,f56])).
% 2.02/0.69  fof(f77,plain,(
% 2.02/0.69    ( ! [X1] : (~v1_funct_1(sK3) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK0,k1_tarski(sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~r1_partfun1(sK3,X1) | k1_xboole_0 = k1_tarski(sK1) | r2_hidden(X1,k5_partfun1(sK0,k1_tarski(sK1),sK3))) ) | ~spl7_4),
% 2.02/0.69    inference(resolution,[],[f68,f38])).
% 2.02/0.69  fof(f38,plain,(
% 2.02/0.69    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_partfun1(X2,X3) | k1_xboole_0 = X1 | r2_hidden(X3,k5_partfun1(X0,X1,X2))) )),
% 2.02/0.69    inference(cnf_transformation,[],[f16])).
% 2.02/0.69  fof(f16,plain,(
% 2.02/0.69    ! [X0,X1,X2] : (! [X3] : (r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_partfun1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.02/0.69    inference(flattening,[],[f15])).
% 2.02/0.69  fof(f15,plain,(
% 2.02/0.69    ! [X0,X1,X2] : (! [X3] : (((r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_partfun1(X2,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.02/0.69    inference(ennf_transformation,[],[f7])).
% 2.02/0.69  fof(f7,axiom,(
% 2.02/0.69    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 2.02/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_2)).
% 2.02/0.69  fof(f107,plain,(
% 2.02/0.69    ~spl7_6),
% 2.02/0.69    inference(avatar_split_clause,[],[f25,f105])).
% 2.02/0.69  fof(f25,plain,(
% 2.02/0.69    k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3)),
% 2.02/0.69    inference(cnf_transformation,[],[f12])).
% 2.02/0.69  fof(f12,plain,(
% 2.02/0.69    ? [X0,X1,X2] : (? [X3] : (k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2))),
% 2.02/0.69    inference(flattening,[],[f11])).
% 2.02/0.69  fof(f11,plain,(
% 2.02/0.69    ? [X0,X1,X2] : (? [X3] : (k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)))),
% 2.02/0.69    inference(ennf_transformation,[],[f10])).
% 2.02/0.69  fof(f10,negated_conjecture,(
% 2.02/0.69    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => k5_partfun1(X0,k1_tarski(X1),X2) = k1_tarski(X3)))),
% 2.02/0.69    inference(negated_conjecture,[],[f9])).
% 2.02/0.69  fof(f9,conjecture,(
% 2.02/0.69    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => k5_partfun1(X0,k1_tarski(X1),X2) = k1_tarski(X3)))),
% 2.02/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_2)).
% 2.02/0.69  fof(f73,plain,(
% 2.02/0.69    spl7_5),
% 2.02/0.69    inference(avatar_split_clause,[],[f27,f71])).
% 2.02/0.69  fof(f27,plain,(
% 2.02/0.69    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 2.02/0.69    inference(cnf_transformation,[],[f12])).
% 2.02/0.69  fof(f69,plain,(
% 2.02/0.69    spl7_4),
% 2.02/0.69    inference(avatar_split_clause,[],[f24,f67])).
% 2.02/0.69  fof(f24,plain,(
% 2.02/0.69    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 2.02/0.69    inference(cnf_transformation,[],[f12])).
% 2.02/0.69  fof(f65,plain,(
% 2.02/0.69    spl7_3),
% 2.02/0.69    inference(avatar_split_clause,[],[f23,f63])).
% 2.02/0.69  fof(f23,plain,(
% 2.02/0.69    v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 2.02/0.69    inference(cnf_transformation,[],[f12])).
% 2.02/0.69  fof(f61,plain,(
% 2.02/0.69    spl7_2),
% 2.02/0.69    inference(avatar_split_clause,[],[f26,f59])).
% 2.02/0.69  fof(f26,plain,(
% 2.02/0.69    v1_funct_1(sK2)),
% 2.02/0.69    inference(cnf_transformation,[],[f12])).
% 2.02/0.69  fof(f57,plain,(
% 2.02/0.69    spl7_1),
% 2.02/0.69    inference(avatar_split_clause,[],[f22,f55])).
% 2.02/0.69  fof(f22,plain,(
% 2.02/0.69    v1_funct_1(sK3)),
% 2.02/0.69    inference(cnf_transformation,[],[f12])).
% 2.02/0.69  % SZS output end Proof for theBenchmark
% 2.02/0.69  % (17696)------------------------------
% 2.02/0.69  % (17696)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.02/0.69  % (17696)Termination reason: Refutation
% 2.02/0.69  
% 2.02/0.69  % (17696)Memory used [KB]: 7036
% 2.02/0.69  % (17696)Time elapsed: 0.279 s
% 2.02/0.69  % (17696)------------------------------
% 2.02/0.69  % (17696)------------------------------
% 2.02/0.70  % (17668)Success in time 0.328 s
%------------------------------------------------------------------------------
