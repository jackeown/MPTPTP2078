%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1129+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:08 EST 2020

% Result     : Theorem 6.45s
% Output     : Refutation 6.45s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 250 expanded)
%              Number of leaves         :   25 (  93 expanded)
%              Depth                    :   12
%              Number of atoms          :  435 ( 953 expanded)
%              Number of equality atoms :   41 (  68 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7718,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2017,f2020,f2025,f2029,f2705,f3852,f4483,f4487,f4510,f4562,f4935,f4994,f4995,f7041,f7653,f7681,f7683,f7717])).

% (7495)Time limit reached!
% (7495)------------------------------
% (7495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (7495)Termination reason: Time limit
% (7495)Termination phase: Saturation

% (7495)Memory used [KB]: 17014
% (7495)Time elapsed: 0.823 s
% (7495)------------------------------
% (7495)------------------------------
fof(f7717,plain,
    ( spl15_3
    | ~ spl15_5
    | ~ spl15_22
    | ~ spl15_157
    | ~ spl15_176
    | ~ spl15_304 ),
    inference(avatar_contradiction_clause,[],[f7716])).

fof(f7716,plain,
    ( $false
    | spl15_3
    | ~ spl15_5
    | ~ spl15_22
    | ~ spl15_157
    | ~ spl15_176
    | ~ spl15_304 ),
    inference(subsumption_resolution,[],[f7714,f7651])).

fof(f7651,plain,
    ( r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ spl15_22 ),
    inference(avatar_component_clause,[],[f2196])).

fof(f2196,plain,
    ( spl15_22
  <=> r2_hidden(sK1,u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_22])])).

fof(f7714,plain,
    ( ~ r2_hidden(sK1,u1_pre_topc(sK0))
    | spl15_3
    | ~ spl15_5
    | ~ spl15_157
    | ~ spl15_176
    | ~ spl15_304 ),
    inference(resolution,[],[f2013,f7170])).

fof(f7170,plain,
    ( ! [X10] :
        ( v3_pre_topc(X10,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ r2_hidden(X10,u1_pre_topc(sK0)) )
    | ~ spl15_5
    | ~ spl15_157
    | ~ spl15_176
    | ~ spl15_304 ),
    inference(subsumption_resolution,[],[f7169,f2176])).

fof(f2176,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,u1_pre_topc(sK0)) )
    | ~ spl15_5 ),
    inference(resolution,[],[f2049,f2028])).

fof(f2028,plain,
    ( l1_pre_topc(sK0)
    | ~ spl15_5 ),
    inference(avatar_component_clause,[],[f2027])).

fof(f2027,plain,
    ( spl15_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_5])])).

fof(f2049,plain,(
    ! [X4,X3] :
      ( ~ l1_pre_topc(X4)
      | ~ r2_hidden(X3,u1_pre_topc(X4))
      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4))) ) ),
    inference(resolution,[],[f1962,f1960])).

fof(f1960,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f1869])).

fof(f1869,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1786])).

fof(f1786,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f1962,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1871])).

fof(f1871,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f1870])).

fof(f1870,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f618])).

fof(f618,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f7169,plain,
    ( ! [X10] :
        ( ~ r2_hidden(X10,u1_pre_topc(sK0))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(X10,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl15_157
    | ~ spl15_176
    | ~ spl15_304 ),
    inference(forward_demodulation,[],[f7168,f6598])).

fof(f6598,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl15_304 ),
    inference(avatar_component_clause,[],[f6597])).

fof(f6597,plain,
    ( spl15_304
  <=> u1_pre_topc(sK0) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_304])])).

fof(f7168,plain,
    ( ! [X10] :
        ( ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(X10,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ r2_hidden(X10,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) )
    | ~ spl15_157
    | ~ spl15_176 ),
    inference(forward_demodulation,[],[f7143,f4993])).

fof(f4993,plain,
    ( u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl15_176 ),
    inference(avatar_component_clause,[],[f4992])).

fof(f4992,plain,
    ( spl15_176
  <=> u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_176])])).

fof(f7143,plain,
    ( ! [X10] :
        ( ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | v3_pre_topc(X10,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ r2_hidden(X10,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) )
    | ~ spl15_157 ),
    inference(resolution,[],[f7069,f2126])).

fof(f2126,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(X3,X4))))
      | v3_pre_topc(X2,g1_pre_topc(X3,X4))
      | ~ r2_hidden(X2,u1_pre_topc(g1_pre_topc(X3,X4))) ) ),
    inference(resolution,[],[f1995,f1942])).

fof(f1942,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f1856])).

fof(f1856,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f1777])).

fof(f1777,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f1995,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f1929])).

fof(f1929,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f1887])).

fof(f1887,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1774])).

fof(f1774,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f7069,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl15_157 ),
    inference(avatar_component_clause,[],[f4508])).

fof(f4508,plain,
    ( spl15_157
  <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_157])])).

fof(f2013,plain,
    ( ~ v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl15_3 ),
    inference(avatar_component_clause,[],[f2012])).

fof(f2012,plain,
    ( spl15_3
  <=> v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_3])])).

fof(f7683,plain,
    ( spl15_1
    | ~ spl15_5
    | ~ spl15_22 ),
    inference(avatar_split_clause,[],[f7670,f2196,f2027,f2006])).

fof(f2006,plain,
    ( spl15_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1])])).

fof(f7670,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl15_5
    | ~ spl15_22 ),
    inference(resolution,[],[f7651,f2194])).

fof(f2194,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_pre_topc(sK0))
        | v3_pre_topc(X0,sK0) )
    | ~ spl15_5 ),
    inference(duplicate_literal_removal,[],[f2185])).

fof(f2185,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_pre_topc(sK0))
        | ~ r2_hidden(X0,u1_pre_topc(sK0))
        | v3_pre_topc(X0,sK0) )
    | ~ spl15_5 ),
    inference(resolution,[],[f2176,f2124])).

fof(f2124,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,u1_pre_topc(sK0))
        | v3_pre_topc(X0,sK0) )
    | ~ spl15_5 ),
    inference(resolution,[],[f1995,f2028])).

fof(f7681,plain,
    ( u1_struct_0(sK0) != u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f7653,plain,
    ( spl15_22
    | ~ spl15_2
    | ~ spl15_3
    | ~ spl15_157
    | ~ spl15_176
    | ~ spl15_304 ),
    inference(avatar_split_clause,[],[f7638,f6597,f4992,f4508,f2012,f2009,f2196])).

fof(f2009,plain,
    ( spl15_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_2])])).

fof(f7638,plain,
    ( r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ spl15_2
    | ~ spl15_3
    | ~ spl15_157
    | ~ spl15_176
    | ~ spl15_304 ),
    inference(subsumption_resolution,[],[f7626,f2018])).

fof(f2018,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_2 ),
    inference(avatar_component_clause,[],[f2009])).

fof(f7626,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ spl15_3
    | ~ spl15_157
    | ~ spl15_176
    | ~ spl15_304 ),
    inference(resolution,[],[f7167,f2023])).

fof(f2023,plain,
    ( v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl15_3 ),
    inference(avatar_component_clause,[],[f2012])).

fof(f7167,plain,
    ( ! [X9] :
        ( ~ v3_pre_topc(X9,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X9,u1_pre_topc(sK0)) )
    | ~ spl15_157
    | ~ spl15_176
    | ~ spl15_304 ),
    inference(forward_demodulation,[],[f7166,f6598])).

fof(f7166,plain,
    ( ! [X9] :
        ( ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X9,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | ~ v3_pre_topc(X9,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl15_157
    | ~ spl15_176 ),
    inference(forward_demodulation,[],[f7142,f4993])).

fof(f7142,plain,
    ( ! [X9] :
        ( ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | r2_hidden(X9,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | ~ v3_pre_topc(X9,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl15_157 ),
    inference(resolution,[],[f7069,f2123])).

fof(f2123,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(X3,X4))))
      | r2_hidden(X2,u1_pre_topc(g1_pre_topc(X3,X4)))
      | ~ v3_pre_topc(X2,g1_pre_topc(X3,X4)) ) ),
    inference(resolution,[],[f1994,f1942])).

fof(f1994,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f1929])).

fof(f7041,plain,
    ( spl15_304
    | ~ spl15_153 ),
    inference(avatar_split_clause,[],[f7040,f4485,f6597])).

fof(f4485,plain,
    ( spl15_153
  <=> ! [X15,X14] :
        ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X14,X15)
        | u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X15 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_153])])).

fof(f7040,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl15_153 ),
    inference(equality_resolution,[],[f4486])).

fof(f4486,plain,
    ( ! [X14,X15] :
        ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X14,X15)
        | u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X15 )
    | ~ spl15_153 ),
    inference(avatar_component_clause,[],[f4485])).

fof(f4995,plain,
    ( u1_struct_0(sK0) != u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f4994,plain,
    ( spl15_176
    | ~ spl15_152 ),
    inference(avatar_split_clause,[],[f4990,f4481,f4992])).

fof(f4481,plain,
    ( spl15_152
  <=> ! [X11,X10] :
        ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X10,X11)
        | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X10 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_152])])).

fof(f4990,plain,
    ( u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl15_152 ),
    inference(equality_resolution,[],[f4482])).

fof(f4482,plain,
    ( ! [X10,X11] :
        ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X10,X11)
        | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X10 )
    | ~ spl15_152 ),
    inference(avatar_component_clause,[],[f4481])).

fof(f4935,plain,
    ( ~ spl15_13
    | spl15_151 ),
    inference(avatar_contradiction_clause,[],[f4934])).

fof(f4934,plain,
    ( $false
    | ~ spl15_13
    | spl15_151 ),
    inference(subsumption_resolution,[],[f4932,f4489])).

fof(f4489,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl15_13 ),
    inference(avatar_component_clause,[],[f2088])).

fof(f2088,plain,
    ( spl15_13
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_13])])).

fof(f4932,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl15_151 ),
    inference(resolution,[],[f4479,f1960])).

fof(f4479,plain,
    ( ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | spl15_151 ),
    inference(avatar_component_clause,[],[f4478])).

fof(f4478,plain,
    ( spl15_151
  <=> m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_151])])).

fof(f4562,plain,
    ( ~ spl15_5
    | spl15_157 ),
    inference(avatar_contradiction_clause,[],[f4561])).

fof(f4561,plain,
    ( $false
    | ~ spl15_5
    | spl15_157 ),
    inference(subsumption_resolution,[],[f4559,f2028])).

fof(f4559,plain,
    ( ~ l1_pre_topc(sK0)
    | spl15_157 ),
    inference(resolution,[],[f4509,f1960])).

fof(f4509,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl15_157 ),
    inference(avatar_component_clause,[],[f4508])).

fof(f4510,plain,
    ( ~ spl15_157
    | spl15_13 ),
    inference(avatar_split_clause,[],[f4503,f2088,f4508])).

fof(f4503,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl15_13 ),
    inference(resolution,[],[f2089,f1942])).

fof(f2089,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl15_13 ),
    inference(avatar_component_clause,[],[f2088])).

fof(f4487,plain,
    ( ~ spl15_151
    | spl15_153
    | ~ spl15_128 ),
    inference(avatar_split_clause,[],[f4449,f3850,f4485,f4478])).

fof(f3850,plain,
    ( spl15_128
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_128])])).

fof(f4449,plain,
    ( ! [X14,X15] :
        ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X14,X15)
        | u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X15
        | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) )
    | ~ spl15_128 ),
    inference(superposition,[],[f1940,f3851])).

fof(f3851,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl15_128 ),
    inference(avatar_component_clause,[],[f3850])).

fof(f1940,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X1 = X3
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f1855])).

fof(f1855,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f1806])).

fof(f1806,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f4483,plain,
    ( ~ spl15_151
    | spl15_152
    | ~ spl15_128 ),
    inference(avatar_split_clause,[],[f4447,f3850,f4481,f4478])).

fof(f4447,plain,
    ( ! [X10,X11] :
        ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X10,X11)
        | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X10
        | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) )
    | ~ spl15_128 ),
    inference(superposition,[],[f1939,f3851])).

fof(f1939,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f1855])).

fof(f3852,plain,
    ( spl15_128
    | ~ spl15_5 ),
    inference(avatar_split_clause,[],[f3846,f2027,f3850])).

fof(f3846,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl15_5 ),
    inference(resolution,[],[f3731,f2028])).

fof(f3731,plain,(
    ! [X2] :
      ( ~ l1_pre_topc(X2)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) ) ),
    inference(global_subsumption,[],[f2784])).

fof(f2784,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f2057,f1960])).

fof(f2057,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) = g1_pre_topc(u1_struct_0(g1_pre_topc(X0,X1)),u1_pre_topc(g1_pre_topc(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f2055,f1942])).

fof(f2055,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(X0,X1) = g1_pre_topc(u1_struct_0(g1_pre_topc(X0,X1)),u1_pre_topc(g1_pre_topc(X0,X1)))
      | ~ l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(resolution,[],[f1948,f1941])).

fof(f1941,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f1856])).

fof(f1948,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f1865])).

fof(f1865,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f1864])).

fof(f1864,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1759])).

fof(f1759,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f2705,plain,
    ( ~ spl15_1
    | ~ spl15_2
    | ~ spl15_5
    | spl15_22 ),
    inference(avatar_contradiction_clause,[],[f2704])).

fof(f2704,plain,
    ( $false
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_5
    | spl15_22 ),
    inference(subsumption_resolution,[],[f2703,f2197])).

fof(f2197,plain,
    ( ~ r2_hidden(sK1,u1_pre_topc(sK0))
    | spl15_22 ),
    inference(avatar_component_clause,[],[f2196])).

fof(f2703,plain,
    ( r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_5 ),
    inference(subsumption_resolution,[],[f2687,f2021])).

fof(f2021,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl15_1 ),
    inference(avatar_component_clause,[],[f2006])).

fof(f2687,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ spl15_2
    | ~ spl15_5 ),
    inference(resolution,[],[f2018,f2121])).

fof(f2121,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | r2_hidden(X0,u1_pre_topc(sK0)) )
    | ~ spl15_5 ),
    inference(resolution,[],[f1994,f2028])).

fof(f2029,plain,(
    spl15_5 ),
    inference(avatar_split_clause,[],[f1933,f2027])).

fof(f1933,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f1894])).

fof(f1894,plain,
    ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
      | ~ v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(sK1,sK0) )
    & ( ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        & v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
      | ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        & v3_pre_topc(sK1,sK0) ) )
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f1891,f1893,f1892])).

fof(f1892,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v3_pre_topc(X1,X0) )
            & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
                & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
              | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
                & v3_pre_topc(X1,X0) ) ) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
            | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
            | ~ v3_pre_topc(X1,sK0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
              & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
              & v3_pre_topc(X1,sK0) ) ) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f1893,plain,
    ( ? [X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
          | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          | ~ v3_pre_topc(X1,sK0) )
        & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
          | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
            & v3_pre_topc(X1,sK0) ) ) )
   => ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(sK1,sK0) )
      & ( ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
          & v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
        | ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
          & v3_pre_topc(sK1,sK0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1891,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v3_pre_topc(X1,X0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v3_pre_topc(X1,X0) ) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f1890])).

fof(f1890,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v3_pre_topc(X1,X0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v3_pre_topc(X1,X0) ) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f1854])).

fof(f1854,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f1853])).

fof(f1853,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1851])).

fof(f1851,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v3_pre_topc(X1,X0) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f1850])).

fof(f1850,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_pre_topc)).

fof(f2025,plain,
    ( spl15_1
    | spl15_3 ),
    inference(avatar_split_clause,[],[f1934,f2012,f2006])).

fof(f1934,plain,
    ( v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f1894])).

fof(f2020,plain,
    ( spl15_2
    | spl15_4 ),
    inference(avatar_split_clause,[],[f1937,f2015,f2009])).

fof(f2015,plain,
    ( spl15_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_4])])).

fof(f1937,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f1894])).

fof(f2017,plain,
    ( ~ spl15_1
    | ~ spl15_2
    | ~ spl15_3
    | ~ spl15_4 ),
    inference(avatar_split_clause,[],[f1938,f2015,f2012,f2009,f2006])).

fof(f1938,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f1894])).
%------------------------------------------------------------------------------
