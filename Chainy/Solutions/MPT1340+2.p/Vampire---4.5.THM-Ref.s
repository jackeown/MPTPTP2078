%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1340+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:18 EST 2020

% Result     : Theorem 7.06s
% Output     : Refutation 7.06s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 455 expanded)
%              Number of leaves         :   34 ( 210 expanded)
%              Depth                    :   16
%              Number of atoms          :  768 (2106 expanded)
%              Number of equality atoms :   84 ( 264 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11842,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f5608,f5613,f5618,f5623,f5628,f5638,f5653,f5658,f5668,f5709,f5744,f5775,f5785,f5836,f5945,f6235,f6240,f7106,f11209,f11276,f11836,f11841])).

fof(f11841,plain,
    ( ~ spl305_4
    | ~ spl305_7
    | ~ spl305_10
    | spl305_87 ),
    inference(avatar_contradiction_clause,[],[f11840])).

fof(f11840,plain,
    ( $false
    | ~ spl305_4
    | ~ spl305_7
    | ~ spl305_10
    | spl305_87 ),
    inference(trivial_inequality_removal,[],[f11837])).

fof(f11837,plain,
    ( k1_funct_1(sK4,sK5(u1_struct_0(sK2),sK4,sK4)) != k1_funct_1(sK4,sK5(u1_struct_0(sK2),sK4,sK4))
    | ~ spl305_4
    | ~ spl305_7
    | ~ spl305_10
    | spl305_87 ),
    inference(unit_resulting_resolution,[],[f5622,f5622,f5637,f5637,f5652,f5652,f11835,f3899])).

fof(f3899,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,sK5(X0,X2,X3)) != k1_funct_1(X3,sK5(X0,X2,X3))
      | r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f3353])).

fof(f3353,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_funct_2(X0,X1,X2,X3)
              | ( k1_funct_1(X2,sK5(X0,X2,X3)) != k1_funct_1(X3,sK5(X0,X2,X3))
                & m1_subset_1(sK5(X0,X2,X3),X0) ) )
            & ( ! [X5] :
                  ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
                  | ~ m1_subset_1(X5,X0) )
              | ~ r2_funct_2(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f3351,f3352])).

fof(f3352,plain,(
    ! [X3,X2,X0] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
          & m1_subset_1(X4,X0) )
     => ( k1_funct_1(X2,sK5(X0,X2,X3)) != k1_funct_1(X3,sK5(X0,X2,X3))
        & m1_subset_1(sK5(X0,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f3351,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_funct_2(X0,X1,X2,X3)
              | ? [X4] :
                  ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                  & m1_subset_1(X4,X0) ) )
            & ( ! [X5] :
                  ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
                  | ~ m1_subset_1(X5,X0) )
              | ~ r2_funct_2(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(rectify,[],[f3350])).

fof(f3350,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_funct_2(X0,X1,X2,X3)
              | ? [X4] :
                  ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                  & m1_subset_1(X4,X0) ) )
            & ( ! [X4] :
                  ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                  | ~ m1_subset_1(X4,X0) )
              | ~ r2_funct_2(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f2440])).

fof(f2440,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r2_funct_2(X0,X1,X2,X3)
          <=> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ m1_subset_1(X4,X0) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f2439])).

fof(f2439,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r2_funct_2(X0,X1,X2,X3)
          <=> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ m1_subset_1(X4,X0) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1494])).

fof(f1494,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r2_funct_2(X0,X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_2)).

fof(f11835,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK4)
    | spl305_87 ),
    inference(avatar_component_clause,[],[f11833])).

fof(f11833,plain,
    ( spl305_87
  <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl305_87])])).

fof(f5652,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ spl305_10 ),
    inference(avatar_component_clause,[],[f5650])).

fof(f5650,plain,
    ( spl305_10
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl305_10])])).

fof(f5637,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl305_7 ),
    inference(avatar_component_clause,[],[f5635])).

fof(f5635,plain,
    ( spl305_7
  <=> v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl305_7])])).

fof(f5622,plain,
    ( v1_funct_1(sK4)
    | ~ spl305_4 ),
    inference(avatar_component_clause,[],[f5620])).

fof(f5620,plain,
    ( spl305_4
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl305_4])])).

fof(f11836,plain,
    ( ~ spl305_87
    | ~ spl305_4
    | ~ spl305_5
    | ~ spl305_25
    | spl305_84 ),
    inference(avatar_split_clause,[],[f11830,f11273,f5741,f5625,f5620,f11833])).

fof(f5625,plain,
    ( spl305_5
  <=> v2_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl305_5])])).

fof(f5741,plain,
    ( spl305_25
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl305_25])])).

fof(f11273,plain,
    ( spl305_84
  <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_funct_1(k2_funct_1(sK4)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl305_84])])).

fof(f11830,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK4)
    | ~ spl305_4
    | ~ spl305_5
    | ~ spl305_25
    | spl305_84 ),
    inference(backward_demodulation,[],[f11275,f11820])).

fof(f11820,plain,
    ( sK4 = k2_funct_1(k2_funct_1(sK4))
    | ~ spl305_4
    | ~ spl305_5
    | ~ spl305_25 ),
    inference(unit_resulting_resolution,[],[f5743,f5622,f5627,f4285])).

fof(f4285,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2688])).

fof(f2688,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f2687])).

fof(f2687,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1036])).

fof(f1036,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

fof(f5627,plain,
    ( v2_funct_1(sK4)
    | ~ spl305_5 ),
    inference(avatar_component_clause,[],[f5625])).

fof(f5743,plain,
    ( v1_relat_1(sK4)
    | ~ spl305_25 ),
    inference(avatar_component_clause,[],[f5741])).

fof(f11275,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_funct_1(k2_funct_1(sK4)),sK4)
    | spl305_84 ),
    inference(avatar_component_clause,[],[f11273])).

fof(f11276,plain,
    ( ~ spl305_84
    | spl305_29
    | ~ spl305_36
    | ~ spl305_42
    | ~ spl305_43
    | ~ spl305_53
    | ~ spl305_83 ),
    inference(avatar_split_clause,[],[f11222,f11206,f7103,f6237,f6232,f5942,f5833,f11273])).

fof(f5833,plain,
    ( spl305_29
  <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl305_29])])).

fof(f5942,plain,
    ( spl305_36
  <=> v1_funct_1(k2_funct_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl305_36])])).

fof(f6232,plain,
    ( spl305_42
  <=> v2_funct_1(k2_funct_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl305_42])])).

fof(f6237,plain,
    ( spl305_43
  <=> v1_funct_2(k2_funct_1(sK4),u1_struct_0(sK3),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl305_43])])).

fof(f7103,plain,
    ( spl305_53
  <=> m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl305_53])])).

fof(f11206,plain,
    ( spl305_83
  <=> u1_struct_0(sK2) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl305_83])])).

fof(f11222,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_funct_1(k2_funct_1(sK4)),sK4)
    | spl305_29
    | ~ spl305_36
    | ~ spl305_42
    | ~ spl305_43
    | ~ spl305_53
    | ~ spl305_83 ),
    inference(backward_demodulation,[],[f5835,f11210])).

fof(f11210,plain,
    ( k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)) = k2_funct_1(k2_funct_1(sK4))
    | ~ spl305_36
    | ~ spl305_42
    | ~ spl305_43
    | ~ spl305_53
    | ~ spl305_83 ),
    inference(unit_resulting_resolution,[],[f5944,f6234,f6239,f7105,f11208,f3903])).

fof(f3903,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f2446])).

fof(f2446,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f2445])).

fof(f2445,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2245])).

fof(f2245,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f11208,plain,
    ( u1_struct_0(sK2) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4))
    | ~ spl305_83 ),
    inference(avatar_component_clause,[],[f11206])).

fof(f7105,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ spl305_53 ),
    inference(avatar_component_clause,[],[f7103])).

fof(f6239,plain,
    ( v1_funct_2(k2_funct_1(sK4),u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ spl305_43 ),
    inference(avatar_component_clause,[],[f6237])).

fof(f6234,plain,
    ( v2_funct_1(k2_funct_1(sK4))
    | ~ spl305_42 ),
    inference(avatar_component_clause,[],[f6232])).

fof(f5944,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | ~ spl305_36 ),
    inference(avatar_component_clause,[],[f5942])).

fof(f5835,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK4)
    | spl305_29 ),
    inference(avatar_component_clause,[],[f5833])).

fof(f11209,plain,
    ( spl305_83
    | ~ spl305_1
    | spl305_2
    | ~ spl305_3
    | ~ spl305_4
    | ~ spl305_5
    | ~ spl305_7
    | ~ spl305_10
    | ~ spl305_20
    | ~ spl305_21
    | ~ spl305_28 ),
    inference(avatar_split_clause,[],[f5886,f5772,f5711,f5706,f5650,f5635,f5625,f5620,f5615,f5610,f5605,f11206])).

fof(f5605,plain,
    ( spl305_1
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl305_1])])).

fof(f5610,plain,
    ( spl305_2
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl305_2])])).

fof(f5615,plain,
    ( spl305_3
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl305_3])])).

fof(f5706,plain,
    ( spl305_20
  <=> u1_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl305_20])])).

fof(f5711,plain,
    ( spl305_21
  <=> u1_struct_0(sK3) = k2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl305_21])])).

fof(f5772,plain,
    ( spl305_28
  <=> u1_struct_0(sK2) = k2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl305_28])])).

fof(f5886,plain,
    ( u1_struct_0(sK2) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4))
    | ~ spl305_1
    | spl305_2
    | ~ spl305_3
    | ~ spl305_4
    | ~ spl305_5
    | ~ spl305_7
    | ~ spl305_10
    | ~ spl305_20
    | ~ spl305_21
    | ~ spl305_28 ),
    inference(forward_demodulation,[],[f5885,f5774])).

fof(f5774,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2)
    | ~ spl305_28 ),
    inference(avatar_component_clause,[],[f5772])).

fof(f5885,plain,
    ( k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4))
    | ~ spl305_1
    | spl305_2
    | ~ spl305_3
    | ~ spl305_4
    | ~ spl305_5
    | ~ spl305_7
    | ~ spl305_10
    | ~ spl305_20
    | ~ spl305_21 ),
    inference(forward_demodulation,[],[f5884,f5827])).

fof(f5827,plain,
    ( k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_funct_1(sK4)
    | ~ spl305_4
    | ~ spl305_5
    | ~ spl305_7
    | ~ spl305_10
    | ~ spl305_20 ),
    inference(unit_resulting_resolution,[],[f5622,f5627,f5637,f5652,f5708,f3903])).

fof(f5708,plain,
    ( u1_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | ~ spl305_20 ),
    inference(avatar_component_clause,[],[f5706])).

fof(f5884,plain,
    ( k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | ~ spl305_1
    | spl305_2
    | ~ spl305_3
    | ~ spl305_4
    | ~ spl305_5
    | ~ spl305_7
    | ~ spl305_10
    | ~ spl305_20
    | ~ spl305_21 ),
    inference(subsumption_resolution,[],[f5883,f5607])).

fof(f5607,plain,
    ( l1_struct_0(sK2)
    | ~ spl305_1 ),
    inference(avatar_component_clause,[],[f5605])).

fof(f5883,plain,
    ( k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | ~ l1_struct_0(sK2)
    | spl305_2
    | ~ spl305_3
    | ~ spl305_4
    | ~ spl305_5
    | ~ spl305_7
    | ~ spl305_10
    | ~ spl305_20
    | ~ spl305_21 ),
    inference(subsumption_resolution,[],[f5882,f5612])).

fof(f5612,plain,
    ( ~ v2_struct_0(sK3)
    | spl305_2 ),
    inference(avatar_component_clause,[],[f5610])).

fof(f5882,plain,
    ( k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | v2_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | ~ spl305_3
    | ~ spl305_4
    | ~ spl305_5
    | ~ spl305_7
    | ~ spl305_10
    | ~ spl305_20
    | ~ spl305_21 ),
    inference(subsumption_resolution,[],[f5881,f5617])).

fof(f5617,plain,
    ( l1_struct_0(sK3)
    | ~ spl305_3 ),
    inference(avatar_component_clause,[],[f5615])).

fof(f5881,plain,
    ( k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | ~ spl305_4
    | ~ spl305_5
    | ~ spl305_7
    | ~ spl305_10
    | ~ spl305_20
    | ~ spl305_21 ),
    inference(subsumption_resolution,[],[f5880,f5622])).

fof(f5880,plain,
    ( k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | ~ spl305_5
    | ~ spl305_7
    | ~ spl305_10
    | ~ spl305_20
    | ~ spl305_21 ),
    inference(subsumption_resolution,[],[f5879,f5637])).

fof(f5879,plain,
    ( k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | ~ spl305_5
    | ~ spl305_10
    | ~ spl305_20
    | ~ spl305_21 ),
    inference(subsumption_resolution,[],[f5878,f5652])).

fof(f5878,plain,
    ( k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | ~ spl305_5
    | ~ spl305_20
    | ~ spl305_21 ),
    inference(subsumption_resolution,[],[f5877,f5627])).

fof(f5877,plain,
    ( ~ v2_funct_1(sK4)
    | k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | ~ spl305_20
    | ~ spl305_21 ),
    inference(subsumption_resolution,[],[f5876,f5713])).

fof(f5713,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3)
    | ~ spl305_21 ),
    inference(avatar_component_clause,[],[f5711])).

fof(f5876,plain,
    ( u1_struct_0(sK3) != k2_struct_0(sK3)
    | ~ v2_funct_1(sK4)
    | k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | ~ spl305_20 ),
    inference(superposition,[],[f3908,f5708])).

fof(f3908,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ v2_funct_1(X2)
      | k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2450])).

fof(f2450,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              | ~ v2_funct_1(X2)
              | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f2449])).

fof(f2449,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              | ~ v2_funct_1(X2)
              | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2409])).

fof(f2409,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
               => ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                  & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).

fof(f7106,plain,
    ( spl305_53
    | ~ spl305_4
    | ~ spl305_5
    | ~ spl305_7
    | ~ spl305_10
    | ~ spl305_20 ),
    inference(avatar_split_clause,[],[f5828,f5706,f5650,f5635,f5625,f5620,f7103])).

fof(f5828,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ spl305_4
    | ~ spl305_5
    | ~ spl305_7
    | ~ spl305_10
    | ~ spl305_20 ),
    inference(backward_demodulation,[],[f5798,f5827])).

fof(f5798,plain,
    ( m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ spl305_4
    | ~ spl305_7
    | ~ spl305_10 ),
    inference(unit_resulting_resolution,[],[f5622,f5637,f5652,f3906])).

fof(f3906,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f2448])).

fof(f2448,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f2447])).

fof(f2447,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2252])).

fof(f2252,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).

fof(f6240,plain,
    ( spl305_43
    | ~ spl305_4
    | ~ spl305_5
    | ~ spl305_7
    | ~ spl305_10
    | ~ spl305_20 ),
    inference(avatar_split_clause,[],[f5829,f5706,f5650,f5635,f5625,f5620,f6237])).

fof(f5829,plain,
    ( v1_funct_2(k2_funct_1(sK4),u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ spl305_4
    | ~ spl305_5
    | ~ spl305_7
    | ~ spl305_10
    | ~ spl305_20 ),
    inference(backward_demodulation,[],[f5796,f5827])).

fof(f5796,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ spl305_4
    | ~ spl305_7
    | ~ spl305_10 ),
    inference(unit_resulting_resolution,[],[f5622,f5637,f5652,f3905])).

fof(f3905,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f2448])).

fof(f6235,plain,
    ( spl305_42
    | ~ spl305_1
    | ~ spl305_3
    | ~ spl305_4
    | ~ spl305_5
    | ~ spl305_7
    | ~ spl305_10
    | ~ spl305_20
    | ~ spl305_21 ),
    inference(avatar_split_clause,[],[f5847,f5711,f5706,f5650,f5635,f5625,f5620,f5615,f5605,f6232])).

fof(f5847,plain,
    ( v2_funct_1(k2_funct_1(sK4))
    | ~ spl305_1
    | ~ spl305_3
    | ~ spl305_4
    | ~ spl305_5
    | ~ spl305_7
    | ~ spl305_10
    | ~ spl305_20
    | ~ spl305_21 ),
    inference(forward_demodulation,[],[f5846,f5827])).

fof(f5846,plain,
    ( v2_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | ~ spl305_1
    | ~ spl305_3
    | ~ spl305_4
    | ~ spl305_5
    | ~ spl305_7
    | ~ spl305_10
    | ~ spl305_20
    | ~ spl305_21 ),
    inference(subsumption_resolution,[],[f5845,f5607])).

fof(f5845,plain,
    ( v2_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | ~ l1_struct_0(sK2)
    | ~ spl305_3
    | ~ spl305_4
    | ~ spl305_5
    | ~ spl305_7
    | ~ spl305_10
    | ~ spl305_20
    | ~ spl305_21 ),
    inference(subsumption_resolution,[],[f5844,f5617])).

fof(f5844,plain,
    ( v2_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | ~ spl305_4
    | ~ spl305_5
    | ~ spl305_7
    | ~ spl305_10
    | ~ spl305_20
    | ~ spl305_21 ),
    inference(subsumption_resolution,[],[f5843,f5622])).

fof(f5843,plain,
    ( v2_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | ~ spl305_5
    | ~ spl305_7
    | ~ spl305_10
    | ~ spl305_20
    | ~ spl305_21 ),
    inference(subsumption_resolution,[],[f5842,f5637])).

fof(f5842,plain,
    ( v2_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | ~ spl305_5
    | ~ spl305_10
    | ~ spl305_20
    | ~ spl305_21 ),
    inference(subsumption_resolution,[],[f5841,f5652])).

fof(f5841,plain,
    ( v2_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | ~ spl305_5
    | ~ spl305_20
    | ~ spl305_21 ),
    inference(subsumption_resolution,[],[f5840,f5627])).

fof(f5840,plain,
    ( ~ v2_funct_1(sK4)
    | v2_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | ~ spl305_20
    | ~ spl305_21 ),
    inference(subsumption_resolution,[],[f5839,f5713])).

fof(f5839,plain,
    ( u1_struct_0(sK3) != k2_struct_0(sK3)
    | ~ v2_funct_1(sK4)
    | v2_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | ~ spl305_20 ),
    inference(superposition,[],[f3909,f5708])).

fof(f3909,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ v2_funct_1(X2)
      | v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2452])).

fof(f2452,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
              | ~ v2_funct_1(X2)
              | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f2451])).

fof(f2451,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
              | ~ v2_funct_1(X2)
              | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2410])).

fof(f2410,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
               => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_tops_2)).

fof(f5945,plain,
    ( spl305_36
    | ~ spl305_4
    | ~ spl305_5
    | ~ spl305_7
    | ~ spl305_10
    | ~ spl305_20 ),
    inference(avatar_split_clause,[],[f5830,f5706,f5650,f5635,f5625,f5620,f5942])).

fof(f5830,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | ~ spl305_4
    | ~ spl305_5
    | ~ spl305_7
    | ~ spl305_10
    | ~ spl305_20 ),
    inference(backward_demodulation,[],[f5784,f5827])).

fof(f5784,plain,
    ( v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | ~ spl305_4
    | ~ spl305_7
    | ~ spl305_10 ),
    inference(unit_resulting_resolution,[],[f5622,f5637,f5652,f3904])).

fof(f3904,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k2_tops_2(X0,X1,X2))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f2448])).

fof(f5836,plain,
    ( ~ spl305_29
    | ~ spl305_4
    | ~ spl305_5
    | ~ spl305_7
    | ~ spl305_10
    | spl305_13
    | ~ spl305_20 ),
    inference(avatar_split_clause,[],[f5831,f5706,f5665,f5650,f5635,f5625,f5620,f5833])).

fof(f5665,plain,
    ( spl305_13
  <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl305_13])])).

fof(f5831,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK4)
    | ~ spl305_4
    | ~ spl305_5
    | ~ spl305_7
    | ~ spl305_10
    | spl305_13
    | ~ spl305_20 ),
    inference(backward_demodulation,[],[f5667,f5827])).

fof(f5667,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK4)
    | spl305_13 ),
    inference(avatar_component_clause,[],[f5665])).

fof(f5785,plain,
    ( spl305_21
    | ~ spl305_3 ),
    inference(avatar_split_clause,[],[f5701,f5615,f5711])).

fof(f5701,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3)
    | ~ spl305_3 ),
    inference(unit_resulting_resolution,[],[f5617,f3982])).

fof(f3982,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2502])).

fof(f2502,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1773])).

fof(f1773,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f5775,plain,
    ( spl305_28
    | ~ spl305_1 ),
    inference(avatar_split_clause,[],[f5700,f5605,f5772])).

fof(f5700,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2)
    | ~ spl305_1 ),
    inference(unit_resulting_resolution,[],[f5607,f3982])).

fof(f5744,plain,
    ( spl305_25
    | ~ spl305_10 ),
    inference(avatar_split_clause,[],[f5738,f5650,f5741])).

fof(f5738,plain,
    ( v1_relat_1(sK4)
    | ~ spl305_10 ),
    inference(unit_resulting_resolution,[],[f5652,f3988])).

fof(f3988,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f2510])).

fof(f2510,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1210])).

fof(f1210,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f5709,plain,
    ( spl305_20
    | ~ spl305_3
    | ~ spl305_11 ),
    inference(avatar_split_clause,[],[f5704,f5655,f5615,f5706])).

fof(f5655,plain,
    ( spl305_11
  <=> k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl305_11])])).

fof(f5704,plain,
    ( u1_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | ~ spl305_3
    | ~ spl305_11 ),
    inference(backward_demodulation,[],[f5657,f5701])).

fof(f5657,plain,
    ( k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | ~ spl305_11 ),
    inference(avatar_component_clause,[],[f5655])).

fof(f5668,plain,(
    ~ spl305_13 ),
    inference(avatar_split_clause,[],[f3892,f5665])).

fof(f3892,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK4) ),
    inference(cnf_transformation,[],[f3348])).

fof(f3348,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK4)
    & v2_funct_1(sK4)
    & k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    & v1_funct_1(sK4)
    & l1_struct_0(sK3)
    & ~ v2_struct_0(sK3)
    & l1_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f2432,f3347,f3346,f3345])).

fof(f3345,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
                & v2_funct_1(X2)
                & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f3346,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X2)),X2)
            & v2_funct_1(X2)
            & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X2)),X2)
          & v2_funct_1(X2)
          & k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
          & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3))
          & v1_funct_1(X2) )
      & l1_struct_0(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f3347,plain,
    ( ? [X2] :
        ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X2)),X2)
        & v2_funct_1(X2)
        & k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
        & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3))
        & v1_funct_1(X2) )
   => ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK4)
      & v2_funct_1(sK4)
      & k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f2432,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f2431])).

fof(f2431,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2412])).

fof(f2412,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( ( l1_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( v2_funct_1(X2)
                    & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                 => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f2411])).

fof(f2411,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
               => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).

fof(f5658,plain,(
    spl305_11 ),
    inference(avatar_split_clause,[],[f3890,f5655])).

fof(f3890,plain,(
    k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
    inference(cnf_transformation,[],[f3348])).

fof(f5653,plain,(
    spl305_10 ),
    inference(avatar_split_clause,[],[f3889,f5650])).

fof(f3889,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f3348])).

fof(f5638,plain,(
    spl305_7 ),
    inference(avatar_split_clause,[],[f3888,f5635])).

fof(f3888,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f3348])).

fof(f5628,plain,(
    spl305_5 ),
    inference(avatar_split_clause,[],[f3891,f5625])).

fof(f3891,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f3348])).

fof(f5623,plain,(
    spl305_4 ),
    inference(avatar_split_clause,[],[f3887,f5620])).

fof(f3887,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f3348])).

fof(f5618,plain,(
    spl305_3 ),
    inference(avatar_split_clause,[],[f3886,f5615])).

fof(f3886,plain,(
    l1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f3348])).

fof(f5613,plain,(
    ~ spl305_2 ),
    inference(avatar_split_clause,[],[f3885,f5610])).

fof(f3885,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f3348])).

fof(f5608,plain,(
    spl305_1 ),
    inference(avatar_split_clause,[],[f3884,f5605])).

fof(f3884,plain,(
    l1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f3348])).
%------------------------------------------------------------------------------
