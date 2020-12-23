%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1884+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  312 (1115 expanded)
%              Number of leaves         :   58 ( 473 expanded)
%              Depth                    :   16
%              Number of atoms          : 1622 (6634 expanded)
%              Number of equality atoms :  119 ( 611 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2089,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f117,f122,f127,f132,f137,f146,f194,f230,f235,f240,f253,f343,f346,f360,f366,f375,f376,f377,f378,f379,f384,f461,f511,f516,f521,f554,f564,f702,f714,f729,f830,f862,f994,f1334,f1677,f1769,f1820,f1835,f1867,f2045,f2079])).

fof(f2079,plain,
    ( ~ spl5_3
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_39
    | ~ spl5_52
    | ~ spl5_64
    | spl5_110
    | ~ spl5_132 ),
    inference(avatar_contradiction_clause,[],[f2078])).

fof(f2078,plain,
    ( $false
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_39
    | ~ spl5_52
    | ~ spl5_64
    | spl5_110
    | ~ spl5_132 ),
    inference(subsumption_resolution,[],[f2049,f2072])).

fof(f2072,plain,
    ( sK4(sK0,u1_struct_0(sK1)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_39
    | ~ spl5_52
    | ~ spl5_64
    | ~ spl5_132 ),
    inference(forward_demodulation,[],[f2071,f1056])).

fof(f1056,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK4(sK0,u1_struct_0(sK1))
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_39
    | ~ spl5_52
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f1055,f861])).

fof(f861,plain,
    ( sK4(sK0,u1_struct_0(sK1)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK4(sK0,u1_struct_0(sK1))))
    | ~ spl5_52 ),
    inference(avatar_component_clause,[],[f859])).

fof(f859,plain,
    ( spl5_52
  <=> sK4(sK0,u1_struct_0(sK1)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK4(sK0,u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f1055,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK4(sK0,u1_struct_0(sK1))))
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_39
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f1041,f563])).

fof(f563,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK4(sK0,u1_struct_0(sK1)))
    | ~ spl5_39 ),
    inference(avatar_component_clause,[],[f561])).

fof(f561,plain,
    ( spl5_39
  <=> u1_struct_0(sK1) = u1_struct_0(sK4(sK0,u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f1041,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK4(sK0,u1_struct_0(sK1))),u1_pre_topc(sK4(sK0,u1_struct_0(sK1))))
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_39
    | ~ spl5_64 ),
    inference(unit_resulting_resolution,[],[f126,f136,f563,f993,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(X1) != u1_struct_0(X2)
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              | u1_struct_0(X1) != u1_struct_0(X2)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              | u1_struct_0(X1) != u1_struct_0(X2)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( u1_struct_0(X1) = u1_struct_0(X2)
               => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_tsep_1)).

fof(f993,plain,
    ( m1_pre_topc(sK4(sK0,u1_struct_0(sK1)),sK0)
    | ~ spl5_64 ),
    inference(avatar_component_clause,[],[f991])).

fof(f991,plain,
    ( spl5_64
  <=> m1_pre_topc(sK4(sK0,u1_struct_0(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).

fof(f136,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl5_5
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f126,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl5_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f2071,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_132 ),
    inference(forward_demodulation,[],[f2048,f2044])).

fof(f2044,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK2)
    | ~ spl5_132 ),
    inference(avatar_component_clause,[],[f2042])).

fof(f2042,plain,
    ( spl5_132
  <=> u1_struct_0(sK1) = u1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_132])])).

fof(f2048,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_132 ),
    inference(unit_resulting_resolution,[],[f126,f166,f136,f2044,f80])).

fof(f166,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl5_10
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f2049,plain,
    ( sK4(sK0,u1_struct_0(sK1)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))
    | spl5_110
    | ~ spl5_132 ),
    inference(superposition,[],[f1768,f2044])).

fof(f1768,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != sK4(sK0,u1_struct_0(sK1))
    | spl5_110 ),
    inference(avatar_component_clause,[],[f1766])).

fof(f1766,plain,
    ( spl5_110
  <=> g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK4(sK0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_110])])).

fof(f2045,plain,
    ( spl5_132
    | ~ spl5_3
    | ~ spl5_15
    | ~ spl5_18
    | ~ spl5_114
    | ~ spl5_115
    | ~ spl5_119 ),
    inference(avatar_split_clause,[],[f1880,f1864,f1832,f1817,f250,f227,f124,f2042])).

fof(f227,plain,
    ( spl5_15
  <=> v3_tex_2(u1_struct_0(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f250,plain,
    ( spl5_18
  <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f1817,plain,
    ( spl5_114
  <=> v2_tex_2(u1_struct_0(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_114])])).

fof(f1832,plain,
    ( spl5_115
  <=> m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_115])])).

fof(f1864,plain,
    ( spl5_119
  <=> r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_119])])).

fof(f1880,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK2)
    | ~ spl5_3
    | ~ spl5_15
    | ~ spl5_18
    | ~ spl5_114
    | ~ spl5_115
    | ~ spl5_119 ),
    inference(unit_resulting_resolution,[],[f126,f1819,f228,f252,f1834,f1866,f82])).

fof(f82,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X1,X3)
      | X1 = X3
      | ~ v2_tex_2(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ( sK3(X0,X1) != X1
                & r1_tarski(X1,sK3(X0,X1))
                & v2_tex_2(sK3(X0,X1),X0)
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f53,f54])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r1_tarski(X1,X2)
          & v2_tex_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK3(X0,X1) != X1
        & r1_tarski(X1,sK3(X0,X1))
        & v2_tex_2(sK3(X0,X1),X0)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_tex_2(X2,X0) )
                   => X1 = X2 ) )
              & v2_tex_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

fof(f1866,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl5_119 ),
    inference(avatar_component_clause,[],[f1864])).

fof(f1834,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_115 ),
    inference(avatar_component_clause,[],[f1832])).

fof(f252,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f250])).

fof(f228,plain,
    ( v3_tex_2(u1_struct_0(sK1),sK0)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f227])).

fof(f1819,plain,
    ( v2_tex_2(u1_struct_0(sK2),sK0)
    | ~ spl5_114 ),
    inference(avatar_component_clause,[],[f1817])).

fof(f1867,plain,
    ( spl5_119
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f1762,f169,f164,f134,f124,f119,f1864])).

fof(f119,plain,
    ( spl5_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f169,plain,
    ( spl5_11
  <=> m1_pre_topc(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f1762,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f166,f136,f171,f207])).

fof(f207,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,X1)
        | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) )
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f206,f126])).

fof(f206,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) )
    | ~ spl5_2 ),
    inference(resolution,[],[f98,f121])).

fof(f121,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f119])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
                  | ~ m1_pre_topc(X1,X2) )
                & ( m1_pre_topc(X1,X2)
                  | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f171,plain,
    ( m1_pre_topc(sK1,sK2)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f169])).

fof(f1835,plain,
    ( spl5_115
    | ~ spl5_3
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f1742,f164,f124,f1832])).

fof(f1742,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_3
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f126,f166,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f1820,plain,
    ( spl5_114
    | spl5_1
    | ~ spl5_3
    | spl5_8
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f1743,f164,f159,f153,f124,f114,f1817])).

fof(f114,plain,
    ( spl5_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f153,plain,
    ( spl5_8
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f159,plain,
    ( spl5_9
  <=> v1_tdlat_3(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f1743,plain,
    ( v2_tex_2(u1_struct_0(sK2),sK0)
    | spl5_1
    | ~ spl5_3
    | spl5_8
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f116,f126,f155,f161,f166,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( v2_tex_2(u1_struct_0(X1),X0)
      | ~ v1_tdlat_3(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f107,f79])).

fof(f107,plain,(
    ! [X0,X1] :
      ( v2_tex_2(u1_struct_0(X1),X0)
      | ~ v1_tdlat_3(X1)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v1_tdlat_3(X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_tex_2(X2,X0)
                  | ~ v1_tdlat_3(X1) )
                & ( v1_tdlat_3(X1)
                  | ~ v2_tex_2(X2,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v2_tex_2(X2,X0)
                <=> v1_tdlat_3(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tex_2)).

fof(f161,plain,
    ( v1_tdlat_3(sK2)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f159])).

fof(f155,plain,
    ( ~ v2_struct_0(sK2)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f153])).

fof(f116,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f114])).

fof(f1769,plain,
    ( ~ spl5_110
    | ~ spl5_3
    | ~ spl5_5
    | spl5_13
    | ~ spl5_39
    | ~ spl5_52
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f1727,f991,f859,f561,f186,f134,f124,f1766])).

fof(f186,plain,
    ( spl5_13
  <=> g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f1727,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != sK4(sK0,u1_struct_0(sK1))
    | ~ spl5_3
    | ~ spl5_5
    | spl5_13
    | ~ spl5_39
    | ~ spl5_52
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f188,f1056])).

fof(f188,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | spl5_13 ),
    inference(avatar_component_clause,[],[f186])).

fof(f1677,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_31
    | ~ spl5_34
    | ~ spl5_37
    | spl5_43
    | ~ spl5_50
    | spl5_87 ),
    inference(avatar_contradiction_clause,[],[f1676])).

fof(f1676,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_31
    | ~ spl5_34
    | ~ spl5_37
    | spl5_43
    | ~ spl5_50
    | spl5_87 ),
    inference(subsumption_resolution,[],[f1674,f782])).

fof(f782,plain,
    ( m1_pre_topc(sK4(sK0,sK3(sK0,u1_struct_0(sK1))),sK0)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_31
    | ~ spl5_37
    | spl5_43 ),
    inference(unit_resulting_resolution,[],[f116,f121,f126,f460,f553,f713,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK4(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK4(X0,X1)) = X1
            & m1_pre_topc(sK4(X0,X1),X0)
            & v1_tdlat_3(sK4(X0,X1))
            & v1_pre_topc(sK4(X0,X1))
            & ~ v2_struct_0(sK4(X0,X1)) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f56])).

fof(f56,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & v1_tdlat_3(X2)
          & v1_pre_topc(X2)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK4(X0,X1)) = X1
        & m1_pre_topc(sK4(X0,X1),X0)
        & v1_tdlat_3(sK4(X0,X1))
        & v1_pre_topc(sK4(X0,X1))
        & ~ v2_struct_0(sK4(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_tdlat_3(X2)
                    & v1_pre_topc(X2)
                    & ~ v2_struct_0(X2) )
                 => u1_struct_0(X2) != X1 )
              & v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tex_2)).

fof(f713,plain,
    ( ~ v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | spl5_43 ),
    inference(avatar_component_clause,[],[f711])).

fof(f711,plain,
    ( spl5_43
  <=> v1_xboole_0(sK3(sK0,u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f553,plain,
    ( m1_subset_1(sK3(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_37 ),
    inference(avatar_component_clause,[],[f551])).

fof(f551,plain,
    ( spl5_37
  <=> m1_subset_1(sK3(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f460,plain,
    ( v2_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0)
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f458])).

fof(f458,plain,
    ( spl5_31
  <=> v2_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f1674,plain,
    ( ~ m1_pre_topc(sK4(sK0,sK3(sK0,u1_struct_0(sK1))),sK0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_34
    | ~ spl5_50
    | spl5_87 ),
    inference(unit_resulting_resolution,[],[f121,f126,f136,f515,f1333,f844])).

fof(f844,plain,
    ( ! [X10,X9] :
        ( ~ v2_pre_topc(X10)
        | m1_pre_topc(X9,sK4(sK0,sK3(sK0,u1_struct_0(sK1))))
        | ~ m1_pre_topc(sK4(sK0,sK3(sK0,u1_struct_0(sK1))),X10)
        | ~ m1_pre_topc(X9,X10)
        | ~ l1_pre_topc(X10)
        | ~ r1_tarski(u1_struct_0(X9),sK3(sK0,u1_struct_0(sK1))) )
    | ~ spl5_50 ),
    inference(superposition,[],[f97,f829])).

fof(f829,plain,
    ( sK3(sK0,u1_struct_0(sK1)) = u1_struct_0(sK4(sK0,sK3(sK0,u1_struct_0(sK1))))
    | ~ spl5_50 ),
    inference(avatar_component_clause,[],[f827])).

fof(f827,plain,
    ( spl5_50
  <=> sK3(sK0,u1_struct_0(sK1)) = u1_struct_0(sK4(sK0,sK3(sK0,u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f1333,plain,
    ( ~ m1_pre_topc(sK1,sK4(sK0,sK3(sK0,u1_struct_0(sK1))))
    | spl5_87 ),
    inference(avatar_component_clause,[],[f1331])).

fof(f1331,plain,
    ( spl5_87
  <=> m1_pre_topc(sK1,sK4(sK0,sK3(sK0,u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_87])])).

fof(f515,plain,
    ( r1_tarski(u1_struct_0(sK1),sK3(sK0,u1_struct_0(sK1)))
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f513])).

fof(f513,plain,
    ( spl5_34
  <=> r1_tarski(u1_struct_0(sK1),sK3(sK0,u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f1334,plain,
    ( ~ spl5_87
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_6
    | spl5_15
    | ~ spl5_17
    | ~ spl5_18
    | spl5_23
    | ~ spl5_31
    | ~ spl5_33
    | spl5_35
    | ~ spl5_37
    | ~ spl5_42
    | spl5_43
    | ~ spl5_46 ),
    inference(avatar_split_clause,[],[f789,f726,f711,f699,f551,f518,f508,f458,f381,f250,f237,f227,f139,f124,f119,f114,f1331])).

fof(f139,plain,
    ( spl5_6
  <=> v4_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f237,plain,
    ( spl5_17
  <=> v2_tex_2(u1_struct_0(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f381,plain,
    ( spl5_23
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f508,plain,
    ( spl5_33
  <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f518,plain,
    ( spl5_35
  <=> u1_struct_0(sK1) = sK3(sK0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f699,plain,
    ( spl5_42
  <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(sK3(sK0,u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f726,plain,
    ( spl5_46
  <=> v1_tdlat_3(sK4(sK0,sK3(sK0,u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f789,plain,
    ( ~ m1_pre_topc(sK1,sK4(sK0,sK3(sK0,u1_struct_0(sK1))))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_6
    | spl5_15
    | ~ spl5_17
    | ~ spl5_18
    | spl5_23
    | ~ spl5_31
    | ~ spl5_33
    | spl5_35
    | ~ spl5_37
    | ~ spl5_42
    | spl5_43
    | ~ spl5_46 ),
    inference(subsumption_resolution,[],[f788,f779])).

fof(f779,plain,
    ( ~ v2_struct_0(sK4(sK0,sK3(sK0,u1_struct_0(sK1))))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_31
    | ~ spl5_37
    | spl5_43 ),
    inference(unit_resulting_resolution,[],[f116,f121,f126,f460,f553,f713,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK4(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f788,plain,
    ( ~ m1_pre_topc(sK1,sK4(sK0,sK3(sK0,u1_struct_0(sK1))))
    | v2_struct_0(sK4(sK0,sK3(sK0,u1_struct_0(sK1))))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_6
    | spl5_15
    | ~ spl5_17
    | ~ spl5_18
    | spl5_23
    | ~ spl5_31
    | ~ spl5_33
    | spl5_35
    | ~ spl5_37
    | ~ spl5_42
    | spl5_43
    | ~ spl5_46 ),
    inference(subsumption_resolution,[],[f770,f782])).

fof(f770,plain,
    ( ~ m1_pre_topc(sK1,sK4(sK0,sK3(sK0,u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4(sK0,sK3(sK0,u1_struct_0(sK1))),sK0)
    | v2_struct_0(sK4(sK0,sK3(sK0,u1_struct_0(sK1))))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_6
    | spl5_15
    | ~ spl5_17
    | ~ spl5_18
    | spl5_23
    | ~ spl5_31
    | ~ spl5_33
    | spl5_35
    | ~ spl5_42
    | ~ spl5_46 ),
    inference(subsumption_resolution,[],[f769,f537])).

fof(f537,plain,
    ( ! [X0] : g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(sK3(sK0,u1_struct_0(sK1)),X0)
    | ~ spl5_33
    | spl5_35 ),
    inference(unit_resulting_resolution,[],[f510,f520,f101])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f520,plain,
    ( u1_struct_0(sK1) != sK3(sK0,u1_struct_0(sK1))
    | spl5_35 ),
    inference(avatar_component_clause,[],[f518])).

fof(f510,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl5_33 ),
    inference(avatar_component_clause,[],[f508])).

fof(f769,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(sK3(sK0,u1_struct_0(sK1)),u1_pre_topc(sK4(sK0,sK3(sK0,u1_struct_0(sK1)))))
    | ~ m1_pre_topc(sK1,sK4(sK0,sK3(sK0,u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4(sK0,sK3(sK0,u1_struct_0(sK1))),sK0)
    | v2_struct_0(sK4(sK0,sK3(sK0,u1_struct_0(sK1))))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_6
    | spl5_15
    | ~ spl5_17
    | ~ spl5_18
    | spl5_23
    | ~ spl5_31
    | ~ spl5_42
    | ~ spl5_46 ),
    inference(forward_demodulation,[],[f759,f709])).

fof(f709,plain,
    ( sK3(sK0,u1_struct_0(sK1)) = u1_struct_0(sK4(sK0,sK3(sK0,u1_struct_0(sK1))))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_15
    | ~ spl5_17
    | ~ spl5_18
    | spl5_23
    | ~ spl5_31
    | ~ spl5_42 ),
    inference(subsumption_resolution,[],[f504,f703])).

fof(f703,plain,
    ( ~ v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | spl5_23
    | ~ spl5_42 ),
    inference(unit_resulting_resolution,[],[f383,f701,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f701,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(sK3(sK0,u1_struct_0(sK1))))
    | ~ spl5_42 ),
    inference(avatar_component_clause,[],[f699])).

fof(f383,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | spl5_23 ),
    inference(avatar_component_clause,[],[f381])).

fof(f504,plain,
    ( v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | sK3(sK0,u1_struct_0(sK1)) = u1_struct_0(sK4(sK0,sK3(sK0,u1_struct_0(sK1))))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_15
    | ~ spl5_17
    | ~ spl5_18
    | ~ spl5_31 ),
    inference(subsumption_resolution,[],[f501,f390])).

fof(f390,plain,
    ( m1_subset_1(sK3(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_3
    | spl5_15
    | ~ spl5_17
    | ~ spl5_18 ),
    inference(unit_resulting_resolution,[],[f126,f229,f252,f239,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f239,plain,
    ( v2_tex_2(u1_struct_0(sK1),sK0)
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f237])).

fof(f229,plain,
    ( ~ v3_tex_2(u1_struct_0(sK1),sK0)
    | spl5_15 ),
    inference(avatar_component_clause,[],[f227])).

fof(f501,plain,
    ( ~ m1_subset_1(sK3(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | sK3(sK0,u1_struct_0(sK1)) = u1_struct_0(sK4(sK0,sK3(sK0,u1_struct_0(sK1))))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_31 ),
    inference(resolution,[],[f460,f223])).

fof(f223,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | u1_struct_0(sK4(sK0,X0)) = X0 )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f222,f116])).

fof(f222,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | u1_struct_0(sK4(sK0,X0)) = X0
        | v2_struct_0(sK0) )
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f221,f126])).

fof(f221,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | ~ l1_pre_topc(sK0)
        | u1_struct_0(sK4(sK0,X0)) = X0
        | v2_struct_0(sK0) )
    | ~ spl5_2 ),
    inference(resolution,[],[f92,f121])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | u1_struct_0(sK4(X0,X1)) = X1
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f759,plain,
    ( ~ m1_pre_topc(sK1,sK4(sK0,sK3(sK0,u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4(sK0,sK3(sK0,u1_struct_0(sK1))),sK0)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK4(sK0,sK3(sK0,u1_struct_0(sK1)))),u1_pre_topc(sK4(sK0,sK3(sK0,u1_struct_0(sK1)))))
    | v2_struct_0(sK4(sK0,sK3(sK0,u1_struct_0(sK1))))
    | spl5_6
    | ~ spl5_46 ),
    inference(resolution,[],[f728,f372])).

fof(f372,plain,
    ( ! [X3] :
        ( ~ v1_tdlat_3(X3)
        | ~ m1_pre_topc(sK1,X3)
        | ~ m1_pre_topc(X3,sK0)
        | g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
        | v2_struct_0(X3) )
    | spl5_6 ),
    inference(subsumption_resolution,[],[f68,f140])).

fof(f140,plain,
    ( ~ v4_tex_2(sK1,sK0)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f139])).

fof(f68,plain,(
    ! [X3] :
      ( g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
      | ~ m1_pre_topc(sK1,X3)
      | ~ m1_pre_topc(X3,sK0)
      | ~ v1_tdlat_3(X3)
      | v2_struct_0(X3)
      | v4_tex_2(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,
    ( ( ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
        & m1_pre_topc(sK1,sK2)
        & m1_pre_topc(sK2,sK0)
        & v1_tdlat_3(sK2)
        & ~ v2_struct_0(sK2) )
      | ~ v1_tdlat_3(sK1)
      | ~ v4_tex_2(sK1,sK0) )
    & ( ( ! [X3] :
            ( g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
            | ~ m1_pre_topc(sK1,X3)
            | ~ m1_pre_topc(X3,sK0)
            | ~ v1_tdlat_3(X3)
            | v2_struct_0(X3) )
        & v1_tdlat_3(sK1) )
      | v4_tex_2(sK1,sK0) )
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f46,f49,f48,f47])).

fof(f47,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X2,X0)
                  & v1_tdlat_3(X2)
                  & ~ v2_struct_0(X2) )
              | ~ v1_tdlat_3(X1)
              | ~ v4_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                    | ~ m1_pre_topc(X1,X3)
                    | ~ m1_pre_topc(X3,X0)
                    | ~ v1_tdlat_3(X3)
                    | v2_struct_0(X3) )
                & v1_tdlat_3(X1) )
              | v4_tex_2(X1,X0) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X2,sK0)
                & v1_tdlat_3(X2)
                & ~ v2_struct_0(X2) )
            | ~ v1_tdlat_3(X1)
            | ~ v4_tex_2(X1,sK0) )
          & ( ( ! [X3] :
                  ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  | ~ m1_pre_topc(X1,X3)
                  | ~ m1_pre_topc(X3,sK0)
                  | ~ v1_tdlat_3(X3)
                  | v2_struct_0(X3) )
              & v1_tdlat_3(X1) )
            | v4_tex_2(X1,sK0) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X1] :
        ( ( ? [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,sK0)
              & v1_tdlat_3(X2)
              & ~ v2_struct_0(X2) )
          | ~ v1_tdlat_3(X1)
          | ~ v4_tex_2(X1,sK0) )
        & ( ( ! [X3] :
                ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                | ~ m1_pre_topc(X1,X3)
                | ~ m1_pre_topc(X3,sK0)
                | ~ v1_tdlat_3(X3)
                | v2_struct_0(X3) )
            & v1_tdlat_3(X1) )
          | v4_tex_2(X1,sK0) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ( ? [X2] :
            ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
            & m1_pre_topc(sK1,X2)
            & m1_pre_topc(X2,sK0)
            & v1_tdlat_3(X2)
            & ~ v2_struct_0(X2) )
        | ~ v1_tdlat_3(sK1)
        | ~ v4_tex_2(sK1,sK0) )
      & ( ( ! [X3] :
              ( g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
              | ~ m1_pre_topc(sK1,X3)
              | ~ m1_pre_topc(X3,sK0)
              | ~ v1_tdlat_3(X3)
              | v2_struct_0(X3) )
          & v1_tdlat_3(sK1) )
        | v4_tex_2(sK1,sK0) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X2] :
        ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
        & m1_pre_topc(sK1,X2)
        & m1_pre_topc(X2,sK0)
        & v1_tdlat_3(X2)
        & ~ v2_struct_0(X2) )
   => ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
      & m1_pre_topc(sK1,sK2)
      & m1_pre_topc(sK2,sK0)
      & v1_tdlat_3(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X2,X0)
                & v1_tdlat_3(X2)
                & ~ v2_struct_0(X2) )
            | ~ v1_tdlat_3(X1)
            | ~ v4_tex_2(X1,X0) )
          & ( ( ! [X3] :
                  ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  | ~ m1_pre_topc(X1,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_tdlat_3(X3)
                  | v2_struct_0(X3) )
              & v1_tdlat_3(X1) )
            | v4_tex_2(X1,X0) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X2,X0)
                & v1_tdlat_3(X2)
                & ~ v2_struct_0(X2) )
            | ~ v1_tdlat_3(X1)
            | ~ v4_tex_2(X1,X0) )
          & ( ( ! [X2] :
                  ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X2,X0)
                  | ~ v1_tdlat_3(X2)
                  | v2_struct_0(X2) )
              & v1_tdlat_3(X1) )
            | v4_tex_2(X1,X0) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X2,X0)
                & v1_tdlat_3(X2)
                & ~ v2_struct_0(X2) )
            | ~ v1_tdlat_3(X1)
            | ~ v4_tex_2(X1,X0) )
          & ( ( ! [X2] :
                  ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X2,X0)
                  | ~ v1_tdlat_3(X2)
                  | v2_struct_0(X2) )
              & v1_tdlat_3(X1) )
            | v4_tex_2(X1,X0) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_tex_2(X1,X0)
          <~> ( ! [X2] :
                  ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X2,X0)
                  | ~ v1_tdlat_3(X2)
                  | v2_struct_0(X2) )
              & v1_tdlat_3(X1) ) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_tex_2(X1,X0)
          <~> ( ! [X2] :
                  ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X2,X0)
                  | ~ v1_tdlat_3(X2)
                  | v2_struct_0(X2) )
              & v1_tdlat_3(X1) ) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ( v4_tex_2(X1,X0)
            <=> ( ! [X2] :
                    ( ( m1_pre_topc(X2,X0)
                      & v1_tdlat_3(X2)
                      & ~ v2_struct_0(X2) )
                   => ( m1_pre_topc(X1,X2)
                     => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ) )
                & v1_tdlat_3(X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( v4_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_tdlat_3(X2)
                    & ~ v2_struct_0(X2) )
                 => ( m1_pre_topc(X1,X2)
                   => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ) )
              & v1_tdlat_3(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_tex_2)).

fof(f728,plain,
    ( v1_tdlat_3(sK4(sK0,sK3(sK0,u1_struct_0(sK1))))
    | ~ spl5_46 ),
    inference(avatar_component_clause,[],[f726])).

fof(f994,plain,
    ( spl5_64
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_17
    | ~ spl5_18
    | spl5_23 ),
    inference(avatar_split_clause,[],[f425,f381,f250,f237,f124,f119,f114,f991])).

fof(f425,plain,
    ( m1_pre_topc(sK4(sK0,u1_struct_0(sK1)),sK0)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_17
    | ~ spl5_18
    | spl5_23 ),
    inference(unit_resulting_resolution,[],[f116,f121,f126,f239,f252,f383,f91])).

fof(f862,plain,
    ( spl5_52
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_17
    | ~ spl5_18
    | ~ spl5_22
    | spl5_23 ),
    inference(avatar_split_clause,[],[f592,f381,f340,f250,f237,f124,f119,f114,f859])).

fof(f340,plain,
    ( spl5_22
  <=> v1_pre_topc(sK4(sK0,u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f592,plain,
    ( sK4(sK0,u1_struct_0(sK1)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK4(sK0,u1_struct_0(sK1))))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_17
    | ~ spl5_18
    | ~ spl5_22
    | spl5_23 ),
    inference(subsumption_resolution,[],[f408,f587])).

fof(f587,plain,
    ( l1_pre_topc(sK4(sK0,u1_struct_0(sK1)))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_17
    | ~ spl5_18
    | spl5_23 ),
    inference(unit_resulting_resolution,[],[f383,f239,f252,f248])).

fof(f248,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | l1_pre_topc(sK4(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f247,f116])).

fof(f247,plain,
    ( ! [X0] :
        ( l1_pre_topc(sK4(sK0,X0))
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | v2_struct_0(sK0) )
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f246,f121])).

fof(f246,plain,
    ( ! [X0] :
        ( l1_pre_topc(sK4(sK0,X0))
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f245,f126])).

fof(f245,plain,
    ( ! [X0] :
        ( l1_pre_topc(sK4(sK0,X0))
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_3 ),
    inference(resolution,[],[f175,f91])).

fof(f175,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | l1_pre_topc(X0) )
    | ~ spl5_3 ),
    inference(resolution,[],[f78,f126])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f408,plain,
    ( sK4(sK0,u1_struct_0(sK1)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK4(sK0,u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK4(sK0,u1_struct_0(sK1)))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_17
    | ~ spl5_18
    | ~ spl5_22
    | spl5_23 ),
    inference(forward_demodulation,[],[f407,f400])).

fof(f400,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK4(sK0,u1_struct_0(sK1)))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_17
    | ~ spl5_18
    | spl5_23 ),
    inference(subsumption_resolution,[],[f399,f383])).

fof(f399,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | u1_struct_0(sK1) = u1_struct_0(sK4(sK0,u1_struct_0(sK1)))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_17
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f396,f252])).

fof(f396,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK1))
    | u1_struct_0(sK1) = u1_struct_0(sK4(sK0,u1_struct_0(sK1)))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_17 ),
    inference(resolution,[],[f239,f223])).

fof(f407,plain,
    ( sK4(sK0,u1_struct_0(sK1)) = g1_pre_topc(u1_struct_0(sK4(sK0,u1_struct_0(sK1))),u1_pre_topc(sK4(sK0,u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK4(sK0,u1_struct_0(sK1)))
    | ~ spl5_22 ),
    inference(resolution,[],[f342,f77])).

fof(f77,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f342,plain,
    ( v1_pre_topc(sK4(sK0,u1_struct_0(sK1)))
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f340])).

fof(f830,plain,
    ( spl5_50
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_15
    | ~ spl5_17
    | ~ spl5_18
    | spl5_23
    | ~ spl5_31
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f709,f699,f458,f381,f250,f237,f227,f124,f119,f114,f827])).

fof(f729,plain,
    ( spl5_46
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_15
    | ~ spl5_17
    | ~ spl5_18
    | spl5_23
    | ~ spl5_31
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f708,f699,f458,f381,f250,f237,f227,f124,f119,f114,f726])).

fof(f708,plain,
    ( v1_tdlat_3(sK4(sK0,sK3(sK0,u1_struct_0(sK1))))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_15
    | ~ spl5_17
    | ~ spl5_18
    | spl5_23
    | ~ spl5_31
    | ~ spl5_42 ),
    inference(subsumption_resolution,[],[f505,f703])).

fof(f505,plain,
    ( v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | v1_tdlat_3(sK4(sK0,sK3(sK0,u1_struct_0(sK1))))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_15
    | ~ spl5_17
    | ~ spl5_18
    | ~ spl5_31 ),
    inference(subsumption_resolution,[],[f502,f390])).

fof(f502,plain,
    ( ~ m1_subset_1(sK3(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | v1_tdlat_3(sK4(sK0,sK3(sK0,u1_struct_0(sK1))))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_31 ),
    inference(resolution,[],[f460,f220])).

fof(f220,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | v1_tdlat_3(sK4(sK0,X0)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f219,f116])).

fof(f219,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | v1_tdlat_3(sK4(sK0,X0))
        | v2_struct_0(sK0) )
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f218,f126])).

fof(f218,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | ~ l1_pre_topc(sK0)
        | v1_tdlat_3(sK4(sK0,X0))
        | v2_struct_0(sK0) )
    | ~ spl5_2 ),
    inference(resolution,[],[f90,f121])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v1_tdlat_3(sK4(X0,X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f714,plain,
    ( ~ spl5_43
    | spl5_23
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f703,f699,f381,f711])).

fof(f702,plain,
    ( spl5_42
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f533,f513,f699])).

fof(f533,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(sK3(sK0,u1_struct_0(sK1))))
    | ~ spl5_34 ),
    inference(unit_resulting_resolution,[],[f515,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f564,plain,
    ( spl5_39
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_17
    | ~ spl5_18
    | spl5_23 ),
    inference(avatar_split_clause,[],[f400,f381,f250,f237,f124,f119,f114,f561])).

fof(f554,plain,
    ( spl5_37
    | ~ spl5_3
    | spl5_15
    | ~ spl5_17
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f390,f250,f237,f227,f124,f551])).

fof(f521,plain,
    ( ~ spl5_35
    | ~ spl5_3
    | spl5_15
    | ~ spl5_17
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f393,f250,f237,f227,f124,f518])).

fof(f393,plain,
    ( u1_struct_0(sK1) != sK3(sK0,u1_struct_0(sK1))
    | ~ spl5_3
    | spl5_15
    | ~ spl5_17
    | ~ spl5_18 ),
    inference(unit_resulting_resolution,[],[f126,f229,f252,f239,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( sK3(X0,X1) != X1
      | v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f516,plain,
    ( spl5_34
    | ~ spl5_3
    | spl5_15
    | ~ spl5_17
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f392,f250,f237,f227,f124,f513])).

fof(f392,plain,
    ( r1_tarski(u1_struct_0(sK1),sK3(sK0,u1_struct_0(sK1)))
    | ~ spl5_3
    | spl5_15
    | ~ spl5_17
    | ~ spl5_18 ),
    inference(unit_resulting_resolution,[],[f126,f229,f252,f239,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | r1_tarski(X1,sK3(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f511,plain,
    ( spl5_33
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f210,f191,f508])).

fof(f191,plain,
    ( spl5_14
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f210,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f193,f76])).

fof(f76,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f193,plain,
    ( l1_pre_topc(sK1)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f191])).

fof(f461,plain,
    ( spl5_31
    | ~ spl5_3
    | spl5_15
    | ~ spl5_17
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f391,f250,f237,f227,f124,f458])).

fof(f391,plain,
    ( v2_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0)
    | ~ spl5_3
    | spl5_15
    | ~ spl5_17
    | ~ spl5_18 ),
    inference(unit_resulting_resolution,[],[f126,f229,f252,f239,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v2_tex_2(sK3(X0,X1),X0)
      | v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f384,plain,
    ( ~ spl5_23
    | spl5_4
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f271,f232,f129,f381])).

fof(f129,plain,
    ( spl5_4
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f232,plain,
    ( spl5_16
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f271,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | spl5_4
    | ~ spl5_16 ),
    inference(unit_resulting_resolution,[],[f131,f234,f87])).

fof(f87,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f234,plain,
    ( l1_struct_0(sK1)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f232])).

fof(f131,plain,
    ( ~ v2_struct_0(sK1)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f129])).

fof(f379,plain,
    ( ~ spl5_6
    | ~ spl5_13
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f367,f143,f186,f139])).

fof(f143,plain,
    ( spl5_7
  <=> v1_tdlat_3(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f367,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | ~ v4_tex_2(sK1,sK0)
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f73,f145])).

fof(f145,plain,
    ( v1_tdlat_3(sK1)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f143])).

fof(f73,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | ~ v1_tdlat_3(sK1)
    | ~ v4_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f378,plain,
    ( ~ spl5_6
    | spl5_10
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f369,f143,f164,f139])).

fof(f369,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ v4_tex_2(sK1,sK0)
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f71,f145])).

fof(f71,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ v1_tdlat_3(sK1)
    | ~ v4_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f377,plain,
    ( ~ spl5_6
    | spl5_11
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f368,f143,f169,f139])).

fof(f368,plain,
    ( m1_pre_topc(sK1,sK2)
    | ~ v4_tex_2(sK1,sK0)
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f72,f145])).

fof(f72,plain,
    ( m1_pre_topc(sK1,sK2)
    | ~ v1_tdlat_3(sK1)
    | ~ v4_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f376,plain,
    ( ~ spl5_6
    | ~ spl5_8
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f371,f143,f153,f139])).

fof(f371,plain,
    ( ~ v2_struct_0(sK2)
    | ~ v4_tex_2(sK1,sK0)
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f69,f145])).

fof(f69,plain,
    ( ~ v2_struct_0(sK2)
    | ~ v1_tdlat_3(sK1)
    | ~ v4_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f375,plain,
    ( ~ spl5_6
    | spl5_9
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f370,f143,f159,f139])).

fof(f370,plain,
    ( v1_tdlat_3(sK2)
    | ~ v4_tex_2(sK1,sK0)
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f70,f145])).

fof(f70,plain,
    ( v1_tdlat_3(sK2)
    | ~ v1_tdlat_3(sK1)
    | ~ v4_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f366,plain,
    ( spl5_1
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | spl5_7
    | ~ spl5_15
    | ~ spl5_18 ),
    inference(avatar_contradiction_clause,[],[f365])).

fof(f365,plain,
    ( $false
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | spl5_7
    | ~ spl5_15
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f348,f362])).

fof(f362,plain,
    ( v2_tex_2(u1_struct_0(sK1),sK0)
    | ~ spl5_3
    | ~ spl5_15
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f361,f126])).

fof(f361,plain,
    ( v2_tex_2(u1_struct_0(sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_15
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f354,f252])).

fof(f354,plain,
    ( v2_tex_2(u1_struct_0(sK1),sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_15 ),
    inference(resolution,[],[f228,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v3_tex_2(X1,X0)
      | v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f348,plain,
    ( ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | spl5_7 ),
    inference(unit_resulting_resolution,[],[f116,f126,f131,f136,f144,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tex_2(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | v1_tdlat_3(X1)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f108,f79])).

fof(f108,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ v2_tex_2(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ v2_tex_2(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f144,plain,
    ( ~ v1_tdlat_3(sK1)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f143])).

fof(f360,plain,
    ( ~ spl5_3
    | ~ spl5_15
    | spl5_17
    | ~ spl5_18 ),
    inference(avatar_contradiction_clause,[],[f359])).

fof(f359,plain,
    ( $false
    | ~ spl5_3
    | ~ spl5_15
    | spl5_17
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f358,f126])).

fof(f358,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl5_15
    | spl5_17
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f357,f252])).

fof(f357,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_15
    | spl5_17 ),
    inference(subsumption_resolution,[],[f354,f238])).

fof(f238,plain,
    ( ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | spl5_17 ),
    inference(avatar_component_clause,[],[f237])).

fof(f346,plain,
    ( spl5_1
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_6
    | spl5_15 ),
    inference(avatar_contradiction_clause,[],[f345])).

fof(f345,plain,
    ( $false
    | spl5_1
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_6
    | spl5_15 ),
    inference(subsumption_resolution,[],[f141,f241])).

fof(f241,plain,
    ( ~ v4_tex_2(sK1,sK0)
    | spl5_1
    | ~ spl5_3
    | ~ spl5_5
    | spl5_15 ),
    inference(unit_resulting_resolution,[],[f116,f126,f136,f229,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ v4_tex_2(X1,X0)
      | v3_tex_2(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f105,f79])).

fof(f105,plain,(
    ! [X0,X1] :
      ( v3_tex_2(u1_struct_0(X1),X0)
      | ~ v4_tex_2(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( v3_tex_2(X2,X0)
      | ~ v4_tex_2(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_tex_2(X2,X0)
                  | ~ v4_tex_2(X1,X0) )
                & ( v4_tex_2(X1,X0)
                  | ~ v3_tex_2(X2,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tex_2(X2,X0)
              <=> v4_tex_2(X1,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tex_2(X2,X0)
              <=> v4_tex_2(X1,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v3_tex_2(X2,X0)
                <=> v4_tex_2(X1,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_tex_2)).

fof(f141,plain,
    ( v4_tex_2(sK1,sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f139])).

fof(f343,plain,
    ( spl5_22
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_16
    | ~ spl5_17
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f297,f250,f237,f232,f129,f124,f119,f114,f340])).

fof(f297,plain,
    ( v1_pre_topc(sK4(sK0,u1_struct_0(sK1)))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_16
    | ~ spl5_17
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f296,f271])).

fof(f296,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | v1_pre_topc(sK4(sK0,u1_struct_0(sK1)))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_17
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f293,f252])).

fof(f293,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_pre_topc(sK4(sK0,u1_struct_0(sK1)))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_17 ),
    inference(resolution,[],[f217,f239])).

fof(f217,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | v1_pre_topc(sK4(sK0,X0)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f216,f116])).

fof(f216,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | v1_pre_topc(sK4(sK0,X0))
        | v2_struct_0(sK0) )
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f215,f126])).

fof(f215,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | ~ l1_pre_topc(sK0)
        | v1_pre_topc(sK4(sK0,X0))
        | v2_struct_0(sK0) )
    | ~ spl5_2 ),
    inference(resolution,[],[f89,f121])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v1_pre_topc(sK4(X0,X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f253,plain,
    ( spl5_18
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f195,f134,f124,f250])).

fof(f195,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f126,f136,f79])).

fof(f240,plain,
    ( spl5_17
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f202,f143,f134,f129,f124,f114,f237])).

fof(f202,plain,
    ( v2_tex_2(u1_struct_0(sK1),sK0)
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f116,f126,f131,f136,f145,f111])).

fof(f235,plain,
    ( spl5_16
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f209,f191,f232])).

fof(f209,plain,
    ( l1_struct_0(sK1)
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f193,f75])).

fof(f75,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f230,plain,
    ( ~ spl5_15
    | spl5_1
    | ~ spl5_3
    | ~ spl5_5
    | spl5_6 ),
    inference(avatar_split_clause,[],[f198,f139,f134,f124,f114,f227])).

fof(f198,plain,
    ( ~ v3_tex_2(u1_struct_0(sK1),sK0)
    | spl5_1
    | ~ spl5_3
    | ~ spl5_5
    | spl5_6 ),
    inference(unit_resulting_resolution,[],[f116,f126,f136,f140,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ v3_tex_2(u1_struct_0(X1),X0)
      | v4_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f106,f79])).

fof(f106,plain,(
    ! [X0,X1] :
      ( v4_tex_2(X1,X0)
      | ~ v3_tex_2(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( v4_tex_2(X1,X0)
      | ~ v3_tex_2(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f194,plain,
    ( spl5_14
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f174,f134,f124,f191])).

fof(f174,plain,
    ( l1_pre_topc(sK1)
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f136,f126,f78])).

fof(f146,plain,
    ( spl5_6
    | spl5_7 ),
    inference(avatar_split_clause,[],[f67,f143,f139])).

fof(f67,plain,
    ( v1_tdlat_3(sK1)
    | v4_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f137,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f66,f134])).

fof(f66,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f132,plain,(
    ~ spl5_4 ),
    inference(avatar_split_clause,[],[f65,f129])).

fof(f65,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f127,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f64,f124])).

fof(f64,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f122,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f63,f119])).

fof(f63,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f117,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f62,f114])).

fof(f62,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f50])).

%------------------------------------------------------------------------------
