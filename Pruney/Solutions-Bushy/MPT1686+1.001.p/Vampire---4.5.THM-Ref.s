%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1686+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:20 EST 2020

% Result     : Theorem 5.14s
% Output     : Refutation 5.14s
% Verified   : 
% Statistics : Number of formulae       :  538 (1662 expanded)
%              Number of leaves         :  128 ( 856 expanded)
%              Depth                    :   12
%              Number of atoms          : 2813 (13009 expanded)
%              Number of equality atoms :  277 (1589 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8717,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f184,f187,f191,f195,f200,f204,f206,f208,f212,f216,f220,f224,f228,f232,f236,f240,f254,f258,f261,f283,f298,f327,f346,f359,f368,f381,f389,f396,f404,f419,f441,f592,f597,f606,f621,f714,f1399,f1409,f1413,f1417,f1552,f2256,f2327,f2581,f2624,f2703,f2716,f2717,f2858,f2878,f2885,f2893,f2903,f3402,f3408,f3414,f3474,f3478,f3492,f3686,f3786,f3790,f4103,f4109,f4115,f4539,f4557,f4562,f4576,f4581,f4608,f4617,f4621,f4625,f4629,f4641,f4645,f4793,f4932,f4970,f8293,f8339,f8343,f8360,f8402,f8410,f8414,f8418,f8420,f8422,f8426,f8430,f8440,f8447,f8480,f8488,f8559,f8571,f8681,f8689,f8703])).

fof(f8703,plain,
    ( spl14_303
    | ~ spl14_11
    | ~ spl14_10
    | ~ spl14_18
    | ~ spl14_19
    | ~ spl14_135 ),
    inference(avatar_split_clause,[],[f8702,f1415,f256,f252,f210,f214,f2579])).

fof(f2579,plain,
    ( spl14_303
  <=> v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_303])])).

fof(f214,plain,
    ( spl14_11
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_11])])).

fof(f210,plain,
    ( spl14_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_10])])).

fof(f252,plain,
    ( spl14_18
  <=> u1_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_18])])).

fof(f256,plain,
    ( spl14_19
  <=> k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_19])])).

fof(f1415,plain,
    ( spl14_135
  <=> ! [X5,X6] :
        ( k2_relset_1(X5,X6,sK2) != X6
        | ~ v1_funct_2(sK2,X5,X6)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | v1_funct_2(k2_funct_1(sK2),X6,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_135])])).

fof(f8702,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl14_10
    | ~ spl14_18
    | ~ spl14_19
    | ~ spl14_135 ),
    inference(trivial_inequality_removal,[],[f8701])).

fof(f8701,plain,
    ( u1_struct_0(sK1) != u1_struct_0(sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl14_10
    | ~ spl14_18
    | ~ spl14_19
    | ~ spl14_135 ),
    inference(forward_demodulation,[],[f8700,f253])).

fof(f253,plain,
    ( u1_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl14_18 ),
    inference(avatar_component_clause,[],[f252])).

fof(f8700,plain,
    ( u1_struct_0(sK1) != k2_relat_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl14_10
    | ~ spl14_19
    | ~ spl14_135 ),
    inference(forward_demodulation,[],[f3614,f257])).

fof(f257,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl14_19 ),
    inference(avatar_component_clause,[],[f256])).

fof(f3614,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl14_10
    | ~ spl14_135 ),
    inference(resolution,[],[f1416,f211])).

fof(f211,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl14_10 ),
    inference(avatar_component_clause,[],[f210])).

fof(f1416,plain,
    ( ! [X6,X5] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | ~ v1_funct_2(sK2,X5,X6)
        | k2_relset_1(X5,X6,sK2) != X6
        | v1_funct_2(k2_funct_1(sK2),X6,X5) )
    | ~ spl14_135 ),
    inference(avatar_component_clause,[],[f1415])).

fof(f8689,plain,
    ( spl14_305
    | ~ spl14_11
    | ~ spl14_10
    | ~ spl14_18
    | ~ spl14_19
    | ~ spl14_134 ),
    inference(avatar_split_clause,[],[f8688,f1411,f256,f252,f210,f214,f2593])).

fof(f2593,plain,
    ( spl14_305
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_305])])).

fof(f1411,plain,
    ( spl14_134
  <=> ! [X3,X4] :
        ( k2_relset_1(X3,X4,sK2) != X4
        | ~ v1_funct_2(sK2,X3,X4)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X4,X3))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_134])])).

fof(f8688,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl14_10
    | ~ spl14_18
    | ~ spl14_19
    | ~ spl14_134 ),
    inference(trivial_inequality_removal,[],[f8687])).

fof(f8687,plain,
    ( u1_struct_0(sK1) != u1_struct_0(sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl14_10
    | ~ spl14_18
    | ~ spl14_19
    | ~ spl14_134 ),
    inference(forward_demodulation,[],[f8686,f253])).

fof(f8686,plain,
    ( u1_struct_0(sK1) != k2_relat_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl14_10
    | ~ spl14_19
    | ~ spl14_134 ),
    inference(forward_demodulation,[],[f3643,f257])).

fof(f3643,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl14_10
    | ~ spl14_134 ),
    inference(resolution,[],[f1412,f211])).

fof(f1412,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | ~ v1_funct_2(sK2,X3,X4)
        | k2_relset_1(X3,X4,sK2) != X4
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X4,X3))) )
    | ~ spl14_134 ),
    inference(avatar_component_clause,[],[f1411])).

fof(f8681,plain,
    ( ~ spl14_845
    | ~ spl14_849
    | ~ spl14_78
    | spl14_844
    | ~ spl14_869
    | ~ spl14_870 ),
    inference(avatar_split_clause,[],[f8679,f8568,f8556,f8396,f712,f8416,f8399])).

fof(f8399,plain,
    ( spl14_845
  <=> m1_subset_1(sK8(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_845])])).

fof(f8416,plain,
    ( spl14_849
  <=> r1_orders_2(sK1,sK6(sK1,sK0,k2_funct_1(sK2)),sK7(sK1,sK0,k2_funct_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_849])])).

fof(f712,plain,
    ( spl14_78
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k1_funct_1(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_78])])).

fof(f8396,plain,
    ( spl14_844
  <=> r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK8(sK1,sK0,k2_funct_1(sK2))),k1_funct_1(sK2,sK9(sK1,sK0,k2_funct_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_844])])).

fof(f8556,plain,
    ( spl14_869
  <=> k1_funct_1(sK2,sK8(sK1,sK0,k2_funct_1(sK2))) = sK6(sK1,sK0,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_869])])).

fof(f8568,plain,
    ( spl14_870
  <=> k1_funct_1(sK2,sK9(sK1,sK0,k2_funct_1(sK2))) = sK7(sK1,sK0,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_870])])).

fof(f8679,plain,
    ( ~ r1_orders_2(sK1,sK6(sK1,sK0,k2_funct_1(sK2)),sK7(sK1,sK0,k2_funct_1(sK2)))
    | ~ m1_subset_1(sK8(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK0))
    | ~ spl14_78
    | spl14_844
    | ~ spl14_869
    | ~ spl14_870 ),
    inference(forward_demodulation,[],[f8678,f8557])).

fof(f8557,plain,
    ( k1_funct_1(sK2,sK8(sK1,sK0,k2_funct_1(sK2))) = sK6(sK1,sK0,k2_funct_1(sK2))
    | ~ spl14_869 ),
    inference(avatar_component_clause,[],[f8556])).

fof(f8678,plain,
    ( ~ r1_orders_2(sK1,k1_funct_1(sK2,sK8(sK1,sK0,k2_funct_1(sK2))),sK7(sK1,sK0,k2_funct_1(sK2)))
    | ~ m1_subset_1(sK8(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK0))
    | ~ spl14_78
    | spl14_844
    | ~ spl14_870 ),
    inference(forward_demodulation,[],[f8676,f8569])).

fof(f8569,plain,
    ( k1_funct_1(sK2,sK9(sK1,sK0,k2_funct_1(sK2))) = sK7(sK1,sK0,k2_funct_1(sK2))
    | ~ spl14_870 ),
    inference(avatar_component_clause,[],[f8568])).

fof(f8676,plain,
    ( ~ r1_orders_2(sK1,k1_funct_1(sK2,sK8(sK1,sK0,k2_funct_1(sK2))),k1_funct_1(sK2,sK9(sK1,sK0,k2_funct_1(sK2))))
    | ~ m1_subset_1(sK8(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK0))
    | ~ spl14_78
    | spl14_844 ),
    inference(superposition,[],[f8397,f713])).

fof(f713,plain,
    ( ! [X0] :
        ( k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k1_funct_1(sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl14_78 ),
    inference(avatar_component_clause,[],[f712])).

fof(f8397,plain,
    ( ~ r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK8(sK1,sK0,k2_funct_1(sK2))),k1_funct_1(sK2,sK9(sK1,sK0,k2_funct_1(sK2))))
    | spl14_844 ),
    inference(avatar_component_clause,[],[f8396])).

fof(f8571,plain,
    ( ~ spl14_20
    | ~ spl14_12
    | spl14_870
    | ~ spl14_853
    | ~ spl14_18
    | ~ spl14_859 ),
    inference(avatar_split_clause,[],[f8566,f8486,f252,f8445,f8568,f218,f271])).

fof(f271,plain,
    ( spl14_20
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_20])])).

fof(f218,plain,
    ( spl14_12
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_12])])).

fof(f8445,plain,
    ( spl14_853
  <=> r2_hidden(sK7(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_853])])).

fof(f8486,plain,
    ( spl14_859
  <=> sK9(sK1,sK0,k2_funct_1(sK2)) = sK12(sK2,sK7(sK1,sK0,k2_funct_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_859])])).

fof(f8566,plain,
    ( ~ r2_hidden(sK7(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK1))
    | k1_funct_1(sK2,sK9(sK1,sK0,k2_funct_1(sK2))) = sK7(sK1,sK0,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl14_18
    | ~ spl14_859 ),
    inference(forward_demodulation,[],[f8565,f253])).

fof(f8565,plain,
    ( k1_funct_1(sK2,sK9(sK1,sK0,k2_funct_1(sK2))) = sK7(sK1,sK0,k2_funct_1(sK2))
    | ~ r2_hidden(sK7(sK1,sK0,k2_funct_1(sK2)),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl14_859 ),
    inference(superposition,[],[f160,f8487])).

fof(f8487,plain,
    ( sK9(sK1,sK0,k2_funct_1(sK2)) = sK12(sK2,sK7(sK1,sK0,k2_funct_1(sK2)))
    | ~ spl14_859 ),
    inference(avatar_component_clause,[],[f8486])).

fof(f160,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK12(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f131])).

fof(f131,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK12(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK10(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK10(X0,X1),X1) )
              & ( ( sK10(X0,X1) = k1_funct_1(X0,sK11(X0,X1))
                  & r2_hidden(sK11(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK10(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK12(X0,X5)) = X5
                    & r2_hidden(sK12(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12])],[f77,f80,f79,f78])).

fof(f78,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK10(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK10(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK10(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK10(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK10(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK10(X0,X1) = k1_funct_1(X0,sK11(X0,X1))
        & r2_hidden(sK11(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK12(X0,X5)) = X5
        & r2_hidden(sK12(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f76])).

fof(f76,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(f8559,plain,
    ( ~ spl14_20
    | ~ spl14_12
    | spl14_869
    | ~ spl14_852
    | ~ spl14_18
    | ~ spl14_858 ),
    inference(avatar_split_clause,[],[f8554,f8478,f252,f8438,f8556,f218,f271])).

fof(f8438,plain,
    ( spl14_852
  <=> r2_hidden(sK6(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_852])])).

fof(f8478,plain,
    ( spl14_858
  <=> sK8(sK1,sK0,k2_funct_1(sK2)) = sK12(sK2,sK6(sK1,sK0,k2_funct_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_858])])).

fof(f8554,plain,
    ( ~ r2_hidden(sK6(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK1))
    | k1_funct_1(sK2,sK8(sK1,sK0,k2_funct_1(sK2))) = sK6(sK1,sK0,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl14_18
    | ~ spl14_858 ),
    inference(forward_demodulation,[],[f8553,f253])).

fof(f8553,plain,
    ( k1_funct_1(sK2,sK8(sK1,sK0,k2_funct_1(sK2))) = sK6(sK1,sK0,k2_funct_1(sK2))
    | ~ r2_hidden(sK6(sK1,sK0,k2_funct_1(sK2)),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl14_858 ),
    inference(superposition,[],[f160,f8479])).

fof(f8479,plain,
    ( sK8(sK1,sK0,k2_funct_1(sK2)) = sK12(sK2,sK6(sK1,sK0,k2_funct_1(sK2)))
    | ~ spl14_858 ),
    inference(avatar_component_clause,[],[f8478])).

fof(f8488,plain,
    ( spl14_859
    | ~ spl14_598
    | ~ spl14_851
    | ~ spl14_853 ),
    inference(avatar_split_clause,[],[f8484,f8445,f8428,f4968,f8486])).

fof(f4968,plain,
    ( spl14_598
  <=> ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK1))
        | k1_funct_1(k2_funct_1(sK2),X0) = sK12(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_598])])).

fof(f8428,plain,
    ( spl14_851
  <=> sK9(sK1,sK0,k2_funct_1(sK2)) = k1_funct_1(k2_funct_1(sK2),sK7(sK1,sK0,k2_funct_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_851])])).

fof(f8484,plain,
    ( sK9(sK1,sK0,k2_funct_1(sK2)) = sK12(sK2,sK7(sK1,sK0,k2_funct_1(sK2)))
    | ~ spl14_598
    | ~ spl14_851
    | ~ spl14_853 ),
    inference(forward_demodulation,[],[f8481,f8429])).

fof(f8429,plain,
    ( sK9(sK1,sK0,k2_funct_1(sK2)) = k1_funct_1(k2_funct_1(sK2),sK7(sK1,sK0,k2_funct_1(sK2)))
    | ~ spl14_851 ),
    inference(avatar_component_clause,[],[f8428])).

fof(f8481,plain,
    ( k1_funct_1(k2_funct_1(sK2),sK7(sK1,sK0,k2_funct_1(sK2))) = sK12(sK2,sK7(sK1,sK0,k2_funct_1(sK2)))
    | ~ spl14_598
    | ~ spl14_853 ),
    inference(resolution,[],[f8446,f4969])).

fof(f4969,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK1))
        | k1_funct_1(k2_funct_1(sK2),X0) = sK12(sK2,X0) )
    | ~ spl14_598 ),
    inference(avatar_component_clause,[],[f4968])).

fof(f8446,plain,
    ( r2_hidden(sK7(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK1))
    | ~ spl14_853 ),
    inference(avatar_component_clause,[],[f8445])).

fof(f8480,plain,
    ( spl14_858
    | ~ spl14_598
    | ~ spl14_850
    | ~ spl14_852 ),
    inference(avatar_split_clause,[],[f8476,f8438,f8424,f4968,f8478])).

fof(f8424,plain,
    ( spl14_850
  <=> sK8(sK1,sK0,k2_funct_1(sK2)) = k1_funct_1(k2_funct_1(sK2),sK6(sK1,sK0,k2_funct_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_850])])).

fof(f8476,plain,
    ( sK8(sK1,sK0,k2_funct_1(sK2)) = sK12(sK2,sK6(sK1,sK0,k2_funct_1(sK2)))
    | ~ spl14_598
    | ~ spl14_850
    | ~ spl14_852 ),
    inference(forward_demodulation,[],[f8473,f8425])).

fof(f8425,plain,
    ( sK8(sK1,sK0,k2_funct_1(sK2)) = k1_funct_1(k2_funct_1(sK2),sK6(sK1,sK0,k2_funct_1(sK2)))
    | ~ spl14_850 ),
    inference(avatar_component_clause,[],[f8424])).

fof(f8473,plain,
    ( k1_funct_1(k2_funct_1(sK2),sK6(sK1,sK0,k2_funct_1(sK2))) = sK12(sK2,sK6(sK1,sK0,k2_funct_1(sK2)))
    | ~ spl14_598
    | ~ spl14_852 ),
    inference(resolution,[],[f8439,f4969])).

fof(f8439,plain,
    ( r2_hidden(sK6(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK1))
    | ~ spl14_852 ),
    inference(avatar_component_clause,[],[f8438])).

fof(f8447,plain,
    ( spl14_853
    | spl14_69
    | ~ spl14_848 ),
    inference(avatar_split_clause,[],[f8442,f8412,f601,f8445])).

fof(f601,plain,
    ( spl14_69
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_69])])).

fof(f8412,plain,
    ( spl14_848
  <=> m1_subset_1(sK7(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_848])])).

fof(f8442,plain,
    ( r2_hidden(sK7(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK1))
    | spl14_69
    | ~ spl14_848 ),
    inference(resolution,[],[f8413,f626])).

fof(f626,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r2_hidden(X0,u1_struct_0(sK1)) )
    | spl14_69 ),
    inference(resolution,[],[f602,f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f602,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | spl14_69 ),
    inference(avatar_component_clause,[],[f601])).

fof(f8413,plain,
    ( m1_subset_1(sK7(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK1))
    | ~ spl14_848 ),
    inference(avatar_component_clause,[],[f8412])).

fof(f8440,plain,
    ( spl14_852
    | spl14_69
    | ~ spl14_847 ),
    inference(avatar_split_clause,[],[f8435,f8408,f601,f8438])).

fof(f8408,plain,
    ( spl14_847
  <=> m1_subset_1(sK6(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_847])])).

fof(f8435,plain,
    ( r2_hidden(sK6(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK1))
    | spl14_69
    | ~ spl14_847 ),
    inference(resolution,[],[f8409,f626])).

fof(f8409,plain,
    ( m1_subset_1(sK6(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK1))
    | ~ spl14_847 ),
    inference(avatar_component_clause,[],[f8408])).

fof(f8430,plain,
    ( ~ spl14_13
    | ~ spl14_15
    | ~ spl14_156
    | ~ spl14_303
    | ~ spl14_305
    | spl14_851
    | spl14_269 ),
    inference(avatar_split_clause,[],[f8391,f2325,f8428,f2593,f2579,f1523,f230,f222])).

fof(f222,plain,
    ( spl14_13
  <=> l1_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_13])])).

fof(f230,plain,
    ( spl14_15
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_15])])).

fof(f1523,plain,
    ( spl14_156
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_156])])).

fof(f2325,plain,
    ( spl14_269
  <=> v5_orders_3(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_269])])).

fof(f8391,plain,
    ( sK9(sK1,sK0,k2_funct_1(sK2)) = k1_funct_1(k2_funct_1(sK2),sK7(sK1,sK0,k2_funct_1(sK2)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ l1_orders_2(sK0)
    | ~ l1_orders_2(sK1)
    | spl14_269 ),
    inference(resolution,[],[f4099,f123])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( v5_orders_3(X2,X0,X1)
      | k1_funct_1(X2,sK7(X0,X1,X2)) = sK9(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_orders_3(X2,X0,X1)
                  | ( ~ r1_orders_2(X1,sK8(X0,X1,X2),sK9(X0,X1,X2))
                    & k1_funct_1(X2,sK7(X0,X1,X2)) = sK9(X0,X1,X2)
                    & k1_funct_1(X2,sK6(X0,X1,X2)) = sK8(X0,X1,X2)
                    & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1))
                    & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1))
                    & r1_orders_2(X0,sK6(X0,X1,X2),sK7(X0,X1,X2))
                    & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))
                    & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) )
                & ( ! [X7] :
                      ( ! [X8] :
                          ( ! [X9] :
                              ( ! [X10] :
                                  ( r1_orders_2(X1,X9,X10)
                                  | k1_funct_1(X2,X8) != X10
                                  | k1_funct_1(X2,X7) != X9
                                  | ~ m1_subset_1(X10,u1_struct_0(X1)) )
                              | ~ m1_subset_1(X9,u1_struct_0(X1)) )
                          | ~ r1_orders_2(X0,X7,X8)
                          | ~ m1_subset_1(X8,u1_struct_0(X0)) )
                      | ~ m1_subset_1(X7,u1_struct_0(X0)) )
                  | ~ v5_orders_3(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f70,f74,f73,f72,f71])).

fof(f71,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ~ r1_orders_2(X1,X5,X6)
                      & k1_funct_1(X2,X4) = X6
                      & k1_funct_1(X2,X3) = X5
                      & m1_subset_1(X6,u1_struct_0(X1)) )
                  & m1_subset_1(X5,u1_struct_0(X1)) )
              & r1_orders_2(X0,X3,X4)
              & m1_subset_1(X4,u1_struct_0(X0)) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ~ r1_orders_2(X1,X5,X6)
                    & k1_funct_1(X2,X4) = X6
                    & k1_funct_1(X2,sK6(X0,X1,X2)) = X5
                    & m1_subset_1(X6,u1_struct_0(X1)) )
                & m1_subset_1(X5,u1_struct_0(X1)) )
            & r1_orders_2(X0,sK6(X0,X1,X2),X4)
            & m1_subset_1(X4,u1_struct_0(X0)) )
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ~ r1_orders_2(X1,X5,X6)
                  & k1_funct_1(X2,X4) = X6
                  & k1_funct_1(X2,sK6(X0,X1,X2)) = X5
                  & m1_subset_1(X6,u1_struct_0(X1)) )
              & m1_subset_1(X5,u1_struct_0(X1)) )
          & r1_orders_2(X0,sK6(X0,X1,X2),X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ~ r1_orders_2(X1,X5,X6)
                & k1_funct_1(X2,sK7(X0,X1,X2)) = X6
                & k1_funct_1(X2,sK6(X0,X1,X2)) = X5
                & m1_subset_1(X6,u1_struct_0(X1)) )
            & m1_subset_1(X5,u1_struct_0(X1)) )
        & r1_orders_2(X0,sK6(X0,X1,X2),sK7(X0,X1,X2))
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( ~ r1_orders_2(X1,X5,X6)
              & k1_funct_1(X2,sK7(X0,X1,X2)) = X6
              & k1_funct_1(X2,sK6(X0,X1,X2)) = X5
              & m1_subset_1(X6,u1_struct_0(X1)) )
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ? [X6] :
            ( ~ r1_orders_2(X1,sK8(X0,X1,X2),X6)
            & k1_funct_1(X2,sK7(X0,X1,X2)) = X6
            & k1_funct_1(X2,sK6(X0,X1,X2)) = sK8(X0,X1,X2)
            & m1_subset_1(X6,u1_struct_0(X1)) )
        & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( ~ r1_orders_2(X1,sK8(X0,X1,X2),X6)
          & k1_funct_1(X2,sK7(X0,X1,X2)) = X6
          & k1_funct_1(X2,sK6(X0,X1,X2)) = sK8(X0,X1,X2)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,sK8(X0,X1,X2),sK9(X0,X1,X2))
        & k1_funct_1(X2,sK7(X0,X1,X2)) = sK9(X0,X1,X2)
        & k1_funct_1(X2,sK6(X0,X1,X2)) = sK8(X0,X1,X2)
        & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_orders_3(X2,X0,X1)
                  | ? [X3] :
                      ( ? [X4] :
                          ( ? [X5] :
                              ( ? [X6] :
                                  ( ~ r1_orders_2(X1,X5,X6)
                                  & k1_funct_1(X2,X4) = X6
                                  & k1_funct_1(X2,X3) = X5
                                  & m1_subset_1(X6,u1_struct_0(X1)) )
                              & m1_subset_1(X5,u1_struct_0(X1)) )
                          & r1_orders_2(X0,X3,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X7] :
                      ( ! [X8] :
                          ( ! [X9] :
                              ( ! [X10] :
                                  ( r1_orders_2(X1,X9,X10)
                                  | k1_funct_1(X2,X8) != X10
                                  | k1_funct_1(X2,X7) != X9
                                  | ~ m1_subset_1(X10,u1_struct_0(X1)) )
                              | ~ m1_subset_1(X9,u1_struct_0(X1)) )
                          | ~ r1_orders_2(X0,X7,X8)
                          | ~ m1_subset_1(X8,u1_struct_0(X0)) )
                      | ~ m1_subset_1(X7,u1_struct_0(X0)) )
                  | ~ v5_orders_3(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_orders_3(X2,X0,X1)
                  | ? [X3] :
                      ( ? [X4] :
                          ( ? [X5] :
                              ( ? [X6] :
                                  ( ~ r1_orders_2(X1,X5,X6)
                                  & k1_funct_1(X2,X4) = X6
                                  & k1_funct_1(X2,X3) = X5
                                  & m1_subset_1(X6,u1_struct_0(X1)) )
                              & m1_subset_1(X5,u1_struct_0(X1)) )
                          & r1_orders_2(X0,X3,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( ! [X4] :
                          ( ! [X5] :
                              ( ! [X6] :
                                  ( r1_orders_2(X1,X5,X6)
                                  | k1_funct_1(X2,X4) != X6
                                  | k1_funct_1(X2,X3) != X5
                                  | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                              | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                          | ~ r1_orders_2(X0,X3,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ v5_orders_3(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_orders_3(X2,X0,X1)
              <=> ! [X3] :
                    ( ! [X4] :
                        ( ! [X5] :
                            ( ! [X6] :
                                ( r1_orders_2(X1,X5,X6)
                                | k1_funct_1(X2,X4) != X6
                                | k1_funct_1(X2,X3) != X5
                                | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                        | ~ r1_orders_2(X0,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_orders_3(X2,X0,X1)
              <=> ! [X3] :
                    ( ! [X4] :
                        ( ! [X5] :
                            ( ! [X6] :
                                ( r1_orders_2(X1,X5,X6)
                                | k1_funct_1(X2,X4) != X6
                                | k1_funct_1(X2,X3) != X5
                                | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                        | ~ r1_orders_2(X0,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v5_orders_3(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ( r1_orders_2(X0,X3,X4)
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X1))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X1))
                                 => ( ( k1_funct_1(X2,X4) = X6
                                      & k1_funct_1(X2,X3) = X5 )
                                   => r1_orders_2(X1,X5,X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_orders_3)).

fof(f4099,plain,
    ( ~ v5_orders_3(k2_funct_1(sK2),sK1,sK0)
    | spl14_269 ),
    inference(avatar_component_clause,[],[f2325])).

fof(f8426,plain,
    ( ~ spl14_13
    | ~ spl14_15
    | ~ spl14_156
    | ~ spl14_303
    | ~ spl14_305
    | spl14_850
    | spl14_269 ),
    inference(avatar_split_clause,[],[f8390,f2325,f8424,f2593,f2579,f1523,f230,f222])).

fof(f8390,plain,
    ( sK8(sK1,sK0,k2_funct_1(sK2)) = k1_funct_1(k2_funct_1(sK2),sK6(sK1,sK0,k2_funct_1(sK2)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ l1_orders_2(sK0)
    | ~ l1_orders_2(sK1)
    | spl14_269 ),
    inference(resolution,[],[f4099,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( v5_orders_3(X2,X0,X1)
      | k1_funct_1(X2,sK6(X0,X1,X2)) = sK8(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f8422,plain,
    ( ~ spl14_13
    | ~ spl14_15
    | ~ spl14_156
    | ~ spl14_303
    | ~ spl14_305
    | spl14_843
    | spl14_269 ),
    inference(avatar_split_clause,[],[f8389,f2325,f8393,f2593,f2579,f1523,f230,f222])).

fof(f8393,plain,
    ( spl14_843
  <=> m1_subset_1(sK9(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_843])])).

fof(f8389,plain,
    ( m1_subset_1(sK9(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ l1_orders_2(sK0)
    | ~ l1_orders_2(sK1)
    | spl14_269 ),
    inference(resolution,[],[f4099,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( v5_orders_3(X2,X0,X1)
      | m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f8420,plain,
    ( ~ spl14_13
    | ~ spl14_15
    | ~ spl14_156
    | ~ spl14_303
    | ~ spl14_305
    | spl14_845
    | spl14_269 ),
    inference(avatar_split_clause,[],[f8388,f2325,f8399,f2593,f2579,f1523,f230,f222])).

fof(f8388,plain,
    ( m1_subset_1(sK8(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ l1_orders_2(sK0)
    | ~ l1_orders_2(sK1)
    | spl14_269 ),
    inference(resolution,[],[f4099,f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( v5_orders_3(X2,X0,X1)
      | m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f8418,plain,
    ( ~ spl14_13
    | ~ spl14_15
    | ~ spl14_156
    | ~ spl14_303
    | ~ spl14_305
    | spl14_849
    | spl14_269 ),
    inference(avatar_split_clause,[],[f8387,f2325,f8416,f2593,f2579,f1523,f230,f222])).

fof(f8387,plain,
    ( r1_orders_2(sK1,sK6(sK1,sK0,k2_funct_1(sK2)),sK7(sK1,sK0,k2_funct_1(sK2)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ l1_orders_2(sK0)
    | ~ l1_orders_2(sK1)
    | spl14_269 ),
    inference(resolution,[],[f4099,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( v5_orders_3(X2,X0,X1)
      | r1_orders_2(X0,sK6(X0,X1,X2),sK7(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f8414,plain,
    ( ~ spl14_13
    | ~ spl14_15
    | ~ spl14_156
    | ~ spl14_303
    | ~ spl14_305
    | spl14_848
    | spl14_269 ),
    inference(avatar_split_clause,[],[f8386,f2325,f8412,f2593,f2579,f1523,f230,f222])).

fof(f8386,plain,
    ( m1_subset_1(sK7(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ l1_orders_2(sK0)
    | ~ l1_orders_2(sK1)
    | spl14_269 ),
    inference(resolution,[],[f4099,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( v5_orders_3(X2,X0,X1)
      | m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f8410,plain,
    ( ~ spl14_13
    | ~ spl14_15
    | ~ spl14_156
    | ~ spl14_303
    | ~ spl14_305
    | spl14_847
    | spl14_269 ),
    inference(avatar_split_clause,[],[f8385,f2325,f8408,f2593,f2579,f1523,f230,f222])).

fof(f8385,plain,
    ( m1_subset_1(sK6(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ l1_orders_2(sK0)
    | ~ l1_orders_2(sK1)
    | spl14_269 ),
    inference(resolution,[],[f4099,f117])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( v5_orders_3(X2,X0,X1)
      | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f8402,plain,
    ( ~ spl14_843
    | ~ spl14_844
    | ~ spl14_845
    | ~ spl14_305
    | ~ spl14_303
    | ~ spl14_156
    | ~ spl14_13
    | spl14_269
    | ~ spl14_596 ),
    inference(avatar_split_clause,[],[f8382,f4930,f2325,f222,f1523,f2579,f2593,f8399,f8396,f8393])).

fof(f4930,plain,
    ( spl14_596
  <=> ! [X3,X2] :
        ( ~ m1_subset_1(sK8(X2,sK0,X3),u1_struct_0(sK0))
        | ~ l1_orders_2(X2)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
        | v5_orders_3(X3,X2,sK0)
        | ~ r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK8(X2,sK0,X3)),k1_funct_1(sK2,sK9(X2,sK0,X3)))
        | ~ m1_subset_1(sK9(X2,sK0,X3),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_596])])).

fof(f8382,plain,
    ( ~ l1_orders_2(sK1)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK8(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK0))
    | ~ r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK8(sK1,sK0,k2_funct_1(sK2))),k1_funct_1(sK2,sK9(sK1,sK0,k2_funct_1(sK2))))
    | ~ m1_subset_1(sK9(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK0))
    | spl14_269
    | ~ spl14_596 ),
    inference(resolution,[],[f4099,f4931])).

fof(f4931,plain,
    ( ! [X2,X3] :
        ( v5_orders_3(X3,X2,sK0)
        | ~ l1_orders_2(X2)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
        | ~ m1_subset_1(sK8(X2,sK0,X3),u1_struct_0(sK0))
        | ~ r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK8(X2,sK0,X3)),k1_funct_1(sK2,sK9(X2,sK0,X3)))
        | ~ m1_subset_1(sK9(X2,sK0,X3),u1_struct_0(sK0)) )
    | ~ spl14_596 ),
    inference(avatar_component_clause,[],[f4930])).

fof(f8360,plain,
    ( ~ spl14_15
    | ~ spl14_13
    | ~ spl14_12
    | ~ spl14_11
    | ~ spl14_10
    | spl14_16
    | spl14_14
    | ~ spl14_2
    | ~ spl14_568
    | ~ spl14_156
    | spl14_1
    | ~ spl14_305
    | ~ spl14_269
    | ~ spl14_303 ),
    inference(avatar_split_clause,[],[f3528,f2579,f2325,f2593,f170,f1523,f4606,f173,f226,f234,f210,f214,f218,f222,f230])).

fof(f234,plain,
    ( spl14_16
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_16])])).

fof(f226,plain,
    ( spl14_14
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_14])])).

fof(f173,plain,
    ( spl14_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).

fof(f4606,plain,
    ( spl14_568
  <=> v5_orders_3(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_568])])).

fof(f170,plain,
    ( spl14_1
  <=> v23_waybel_0(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).

fof(f3528,plain,
    ( ~ v5_orders_3(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v23_waybel_0(sK2,sK0,sK1)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v5_orders_3(sK2,sK0,sK1)
    | ~ v2_funct_1(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_orders_2(sK1)
    | ~ l1_orders_2(sK0)
    | ~ spl14_303 ),
    inference(resolution,[],[f155,f2580])).

fof(f2580,plain,
    ( v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl14_303 ),
    inference(avatar_component_clause,[],[f2579])).

fof(f155,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
      | ~ v5_orders_3(k2_funct_1(X2),X1,X0)
      | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v23_waybel_0(X2,X0,X1)
      | ~ v1_funct_1(k2_funct_1(X2))
      | ~ v5_orders_3(X2,X0,X1)
      | ~ v2_funct_1(X2)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f109])).

fof(f109,plain,(
    ! [X2,X0,X3,X1] :
      ( v23_waybel_0(X2,X0,X1)
      | ~ v5_orders_3(X3,X1,X0)
      | k2_funct_1(X2) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X3)
      | ~ v5_orders_3(X2,X0,X1)
      | ~ v2_funct_1(X2)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( ( v23_waybel_0(X2,X0,X1)
                      | ~ v2_struct_0(X1)
                      | ~ v2_struct_0(X0) )
                    & ( ( v2_struct_0(X1)
                        & v2_struct_0(X0) )
                      | ~ v23_waybel_0(X2,X0,X1) ) )
                  | ( ~ v2_struct_0(X1)
                    & ~ v2_struct_0(X0) ) )
                & ( ( ( v23_waybel_0(X2,X0,X1)
                      | ! [X3] :
                          ( ~ v5_orders_3(X3,X1,X0)
                          | k2_funct_1(X2) != X3
                          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                          | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                          | ~ v1_funct_1(X3) )
                      | ~ v5_orders_3(X2,X0,X1)
                      | ~ v2_funct_1(X2) )
                    & ( ( v5_orders_3(sK5(X0,X1,X2),X1,X0)
                        & k2_funct_1(X2) = sK5(X0,X1,X2)
                        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                        & v1_funct_2(sK5(X0,X1,X2),u1_struct_0(X1),u1_struct_0(X0))
                        & v1_funct_1(sK5(X0,X1,X2))
                        & v5_orders_3(X2,X0,X1)
                        & v2_funct_1(X2) )
                      | ~ v23_waybel_0(X2,X0,X1) ) )
                  | v2_struct_0(X1)
                  | v2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f66,f67])).

fof(f67,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( v5_orders_3(X4,X1,X0)
          & k2_funct_1(X2) = X4
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(X4) )
     => ( v5_orders_3(sK5(X0,X1,X2),X1,X0)
        & k2_funct_1(X2) = sK5(X0,X1,X2)
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(sK5(X0,X1,X2),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK5(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( ( v23_waybel_0(X2,X0,X1)
                      | ~ v2_struct_0(X1)
                      | ~ v2_struct_0(X0) )
                    & ( ( v2_struct_0(X1)
                        & v2_struct_0(X0) )
                      | ~ v23_waybel_0(X2,X0,X1) ) )
                  | ( ~ v2_struct_0(X1)
                    & ~ v2_struct_0(X0) ) )
                & ( ( ( v23_waybel_0(X2,X0,X1)
                      | ! [X3] :
                          ( ~ v5_orders_3(X3,X1,X0)
                          | k2_funct_1(X2) != X3
                          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                          | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                          | ~ v1_funct_1(X3) )
                      | ~ v5_orders_3(X2,X0,X1)
                      | ~ v2_funct_1(X2) )
                    & ( ( ? [X4] :
                            ( v5_orders_3(X4,X1,X0)
                            & k2_funct_1(X2) = X4
                            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                            & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0))
                            & v1_funct_1(X4) )
                        & v5_orders_3(X2,X0,X1)
                        & v2_funct_1(X2) )
                      | ~ v23_waybel_0(X2,X0,X1) ) )
                  | v2_struct_0(X1)
                  | v2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( ( v23_waybel_0(X2,X0,X1)
                      | ~ v2_struct_0(X1)
                      | ~ v2_struct_0(X0) )
                    & ( ( v2_struct_0(X1)
                        & v2_struct_0(X0) )
                      | ~ v23_waybel_0(X2,X0,X1) ) )
                  | ( ~ v2_struct_0(X1)
                    & ~ v2_struct_0(X0) ) )
                & ( ( ( v23_waybel_0(X2,X0,X1)
                      | ! [X3] :
                          ( ~ v5_orders_3(X3,X1,X0)
                          | k2_funct_1(X2) != X3
                          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                          | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                          | ~ v1_funct_1(X3) )
                      | ~ v5_orders_3(X2,X0,X1)
                      | ~ v2_funct_1(X2) )
                    & ( ( ? [X3] :
                            ( v5_orders_3(X3,X1,X0)
                            & k2_funct_1(X2) = X3
                            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                            & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                            & v1_funct_1(X3) )
                        & v5_orders_3(X2,X0,X1)
                        & v2_funct_1(X2) )
                      | ~ v23_waybel_0(X2,X0,X1) ) )
                  | v2_struct_0(X1)
                  | v2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( ( v23_waybel_0(X2,X0,X1)
                      | ~ v2_struct_0(X1)
                      | ~ v2_struct_0(X0) )
                    & ( ( v2_struct_0(X1)
                        & v2_struct_0(X0) )
                      | ~ v23_waybel_0(X2,X0,X1) ) )
                  | ( ~ v2_struct_0(X1)
                    & ~ v2_struct_0(X0) ) )
                & ( ( ( v23_waybel_0(X2,X0,X1)
                      | ! [X3] :
                          ( ~ v5_orders_3(X3,X1,X0)
                          | k2_funct_1(X2) != X3
                          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                          | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                          | ~ v1_funct_1(X3) )
                      | ~ v5_orders_3(X2,X0,X1)
                      | ~ v2_funct_1(X2) )
                    & ( ( ? [X3] :
                            ( v5_orders_3(X3,X1,X0)
                            & k2_funct_1(X2) = X3
                            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                            & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                            & v1_funct_1(X3) )
                        & v5_orders_3(X2,X0,X1)
                        & v2_funct_1(X2) )
                      | ~ v23_waybel_0(X2,X0,X1) ) )
                  | v2_struct_0(X1)
                  | v2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( v23_waybel_0(X2,X0,X1)
                  <=> ( v2_struct_0(X1)
                      & v2_struct_0(X0) ) )
                  | ( ~ v2_struct_0(X1)
                    & ~ v2_struct_0(X0) ) )
                & ( ( v23_waybel_0(X2,X0,X1)
                  <=> ( ? [X3] :
                          ( v5_orders_3(X3,X1,X0)
                          & k2_funct_1(X2) = X3
                          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                          & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                          & v1_funct_1(X3) )
                      & v5_orders_3(X2,X0,X1)
                      & v2_funct_1(X2) ) )
                  | v2_struct_0(X1)
                  | v2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( v23_waybel_0(X2,X0,X1)
                  <=> ( v2_struct_0(X1)
                      & v2_struct_0(X0) ) )
                  | ( ~ v2_struct_0(X1)
                    & ~ v2_struct_0(X0) ) )
                & ( ( v23_waybel_0(X2,X0,X1)
                  <=> ( ? [X3] :
                          ( v5_orders_3(X3,X1,X0)
                          & k2_funct_1(X2) = X3
                          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                          & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                          & v1_funct_1(X3) )
                      & v5_orders_3(X2,X0,X1)
                      & v2_funct_1(X2) ) )
                  | v2_struct_0(X1)
                  | v2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( ~ ( ~ v2_struct_0(X1)
                      & ~ v2_struct_0(X0) )
                 => ( v23_waybel_0(X2,X0,X1)
                  <=> ( v2_struct_0(X1)
                      & v2_struct_0(X0) ) ) )
                & ~ ( ~ ( v23_waybel_0(X2,X0,X1)
                      <=> ( ? [X3] :
                              ( v5_orders_3(X3,X1,X0)
                              & k2_funct_1(X2) = X3
                              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                              & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                              & v1_funct_1(X3) )
                          & v5_orders_3(X2,X0,X1)
                          & v2_funct_1(X2) ) )
                    & ~ v2_struct_0(X1)
                    & ~ v2_struct_0(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d38_waybel_0)).

fof(f8343,plain,
    ( ~ spl14_15
    | ~ spl14_13
    | ~ spl14_12
    | ~ spl14_11
    | ~ spl14_10
    | spl14_568
    | ~ spl14_835 ),
    inference(avatar_split_clause,[],[f8340,f8337,f4606,f210,f214,f218,f222,f230])).

fof(f8337,plain,
    ( spl14_835
  <=> r1_orders_2(sK1,sK8(sK0,sK1,sK2),sK9(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_835])])).

fof(f8340,plain,
    ( v5_orders_3(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_orders_2(sK1)
    | ~ l1_orders_2(sK0)
    | ~ spl14_835 ),
    inference(resolution,[],[f8338,f124])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X1,sK8(X0,X1,X2),sK9(X0,X1,X2))
      | v5_orders_3(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f8338,plain,
    ( r1_orders_2(sK1,sK8(sK0,sK1,sK2),sK9(sK0,sK1,sK2))
    | ~ spl14_835 ),
    inference(avatar_component_clause,[],[f8337])).

fof(f8339,plain,
    ( ~ spl14_570
    | spl14_835
    | ~ spl14_78
    | ~ spl14_575
    | ~ spl14_828 ),
    inference(avatar_split_clause,[],[f8335,f8291,f4643,f712,f8337,f4623])).

fof(f4623,plain,
    ( spl14_570
  <=> m1_subset_1(sK7(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_570])])).

fof(f4643,plain,
    ( spl14_575
  <=> sK9(sK0,sK1,sK2) = k1_funct_1(sK2,sK7(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_575])])).

fof(f8291,plain,
    ( spl14_828
  <=> r1_orders_2(sK1,sK8(sK0,sK1,sK2),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK7(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_828])])).

fof(f8335,plain,
    ( r1_orders_2(sK1,sK8(sK0,sK1,sK2),sK9(sK0,sK1,sK2))
    | ~ m1_subset_1(sK7(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl14_78
    | ~ spl14_575
    | ~ spl14_828 ),
    inference(forward_demodulation,[],[f8330,f4644])).

fof(f4644,plain,
    ( sK9(sK0,sK1,sK2) = k1_funct_1(sK2,sK7(sK0,sK1,sK2))
    | ~ spl14_575 ),
    inference(avatar_component_clause,[],[f4643])).

fof(f8330,plain,
    ( r1_orders_2(sK1,sK8(sK0,sK1,sK2),k1_funct_1(sK2,sK7(sK0,sK1,sK2)))
    | ~ m1_subset_1(sK7(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl14_78
    | ~ spl14_828 ),
    inference(superposition,[],[f8292,f713])).

fof(f8292,plain,
    ( r1_orders_2(sK1,sK8(sK0,sK1,sK2),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK7(sK0,sK1,sK2)))
    | ~ spl14_828 ),
    inference(avatar_component_clause,[],[f8291])).

fof(f8293,plain,
    ( ~ spl14_569
    | spl14_828
    | ~ spl14_78
    | ~ spl14_574
    | ~ spl14_587 ),
    inference(avatar_split_clause,[],[f8289,f4791,f4639,f712,f8291,f4619])).

fof(f4619,plain,
    ( spl14_569
  <=> m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_569])])).

fof(f4639,plain,
    ( spl14_574
  <=> sK8(sK0,sK1,sK2) = k1_funct_1(sK2,sK6(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_574])])).

fof(f4791,plain,
    ( spl14_587
  <=> r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK6(sK0,sK1,sK2)),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK7(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_587])])).

fof(f8289,plain,
    ( r1_orders_2(sK1,sK8(sK0,sK1,sK2),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK7(sK0,sK1,sK2)))
    | ~ m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl14_78
    | ~ spl14_574
    | ~ spl14_587 ),
    inference(forward_demodulation,[],[f8277,f4640])).

fof(f4640,plain,
    ( sK8(sK0,sK1,sK2) = k1_funct_1(sK2,sK6(sK0,sK1,sK2))
    | ~ spl14_574 ),
    inference(avatar_component_clause,[],[f4639])).

fof(f8277,plain,
    ( r1_orders_2(sK1,k1_funct_1(sK2,sK6(sK0,sK1,sK2)),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK7(sK0,sK1,sK2)))
    | ~ m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl14_78
    | ~ spl14_587 ),
    inference(superposition,[],[f4792,f713])).

fof(f4792,plain,
    ( r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK6(sK0,sK1,sK2)),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK7(sK0,sK1,sK2)))
    | ~ spl14_587 ),
    inference(avatar_component_clause,[],[f4791])).

fof(f4970,plain,
    ( ~ spl14_20
    | ~ spl14_12
    | spl14_598
    | ~ spl14_18
    | ~ spl14_447
    | ~ spl14_473 ),
    inference(avatar_split_clause,[],[f4966,f3684,f3400,f252,f4968,f218,f271])).

fof(f3400,plain,
    ( spl14_447
  <=> ! [X11] :
        ( r2_hidden(sK12(sK2,X11),u1_struct_0(sK0))
        | ~ r2_hidden(X11,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_447])])).

fof(f3684,plain,
    ( spl14_473
  <=> ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK0))
        | k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_473])])).

fof(f4966,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK1))
        | k1_funct_1(k2_funct_1(sK2),X0) = sK12(sK2,X0)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl14_18
    | ~ spl14_447
    | ~ spl14_473 ),
    inference(duplicate_literal_removal,[],[f4965])).

fof(f4965,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK1))
        | k1_funct_1(k2_funct_1(sK2),X0) = sK12(sK2,X0)
        | ~ r2_hidden(X0,u1_struct_0(sK1))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl14_18
    | ~ spl14_447
    | ~ spl14_473 ),
    inference(forward_demodulation,[],[f4937,f253])).

fof(f4937,plain,
    ( ! [X0] :
        ( k1_funct_1(k2_funct_1(sK2),X0) = sK12(sK2,X0)
        | ~ r2_hidden(X0,u1_struct_0(sK1))
        | ~ r2_hidden(X0,k2_relat_1(sK2))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl14_447
    | ~ spl14_473 ),
    inference(superposition,[],[f3703,f160])).

fof(f3703,plain,
    ( ! [X2] :
        ( sK12(sK2,X2) = k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK12(sK2,X2)))
        | ~ r2_hidden(X2,u1_struct_0(sK1)) )
    | ~ spl14_447
    | ~ spl14_473 ),
    inference(resolution,[],[f3685,f3401])).

fof(f3401,plain,
    ( ! [X11] :
        ( r2_hidden(sK12(sK2,X11),u1_struct_0(sK0))
        | ~ r2_hidden(X11,u1_struct_0(sK1)) )
    | ~ spl14_447 ),
    inference(avatar_component_clause,[],[f3400])).

fof(f3685,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK0))
        | k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,X0)) = X0 )
    | ~ spl14_473 ),
    inference(avatar_component_clause,[],[f3684])).

fof(f4932,plain,
    ( ~ spl14_15
    | spl14_596
    | ~ spl14_8
    | ~ spl14_78 ),
    inference(avatar_split_clause,[],[f4925,f712,f198,f4930,f230])).

fof(f198,plain,
    ( spl14_8
  <=> ! [X5,X6] :
        ( r1_orders_2(sK0,X5,X6)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X5),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X6)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_8])])).

fof(f4925,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK8(X2,sK0,X3),u1_struct_0(sK0))
        | ~ m1_subset_1(sK9(X2,sK0,X3),u1_struct_0(sK0))
        | ~ r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK8(X2,sK0,X3)),k1_funct_1(sK2,sK9(X2,sK0,X3)))
        | v5_orders_3(X3,X2,sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
        | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0))
        | ~ v1_funct_1(X3)
        | ~ l1_orders_2(sK0)
        | ~ l1_orders_2(X2) )
    | ~ spl14_8
    | ~ spl14_78 ),
    inference(resolution,[],[f720,f124])).

fof(f720,plain,
    ( ! [X2,X3] :
        ( r1_orders_2(sK0,X3,X2)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3),k1_funct_1(sK2,X2)) )
    | ~ spl14_8
    | ~ spl14_78 ),
    inference(duplicate_literal_removal,[],[f717])).

fof(f717,plain,
    ( ! [X2,X3] :
        ( ~ r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3),k1_funct_1(sK2,X2))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_orders_2(sK0,X3,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl14_8
    | ~ spl14_78 ),
    inference(superposition,[],[f199,f713])).

fof(f199,plain,
    ( ! [X6,X5] :
        ( ~ r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X5),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X6))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | r1_orders_2(sK0,X5,X6) )
    | ~ spl14_8 ),
    inference(avatar_component_clause,[],[f198])).

fof(f4793,plain,
    ( spl14_587
    | ~ spl14_570
    | ~ spl14_569
    | ~ spl14_9
    | ~ spl14_571 ),
    inference(avatar_split_clause,[],[f4789,f4627,f202,f4619,f4623,f4791])).

fof(f202,plain,
    ( spl14_9
  <=> ! [X5,X6] :
        ( r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X5),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X6))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X5,X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_9])])).

fof(f4627,plain,
    ( spl14_571
  <=> r1_orders_2(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_571])])).

fof(f4789,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK7(sK0,sK1,sK2),u1_struct_0(sK0))
    | r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK6(sK0,sK1,sK2)),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK7(sK0,sK1,sK2)))
    | ~ spl14_9
    | ~ spl14_571 ),
    inference(resolution,[],[f203,f4628])).

fof(f4628,plain,
    ( r1_orders_2(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2))
    | ~ spl14_571 ),
    inference(avatar_component_clause,[],[f4627])).

fof(f203,plain,
    ( ! [X6,X5] :
        ( ~ r1_orders_2(sK0,X5,X6)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X5),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X6)) )
    | ~ spl14_9 ),
    inference(avatar_component_clause,[],[f202])).

fof(f4645,plain,
    ( ~ spl14_15
    | ~ spl14_13
    | ~ spl14_12
    | ~ spl14_11
    | ~ spl14_10
    | spl14_575
    | spl14_568 ),
    inference(avatar_split_clause,[],[f4616,f4606,f4643,f210,f214,f218,f222,f230])).

fof(f4616,plain,
    ( sK9(sK0,sK1,sK2) = k1_funct_1(sK2,sK7(sK0,sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_orders_2(sK1)
    | ~ l1_orders_2(sK0)
    | spl14_568 ),
    inference(resolution,[],[f4607,f123])).

fof(f4607,plain,
    ( ~ v5_orders_3(sK2,sK0,sK1)
    | spl14_568 ),
    inference(avatar_component_clause,[],[f4606])).

fof(f4641,plain,
    ( ~ spl14_15
    | ~ spl14_13
    | ~ spl14_12
    | ~ spl14_11
    | ~ spl14_10
    | spl14_574
    | spl14_568 ),
    inference(avatar_split_clause,[],[f4615,f4606,f4639,f210,f214,f218,f222,f230])).

fof(f4615,plain,
    ( sK8(sK0,sK1,sK2) = k1_funct_1(sK2,sK6(sK0,sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_orders_2(sK1)
    | ~ l1_orders_2(sK0)
    | spl14_568 ),
    inference(resolution,[],[f4607,f122])).

fof(f4629,plain,
    ( ~ spl14_15
    | ~ spl14_13
    | ~ spl14_12
    | ~ spl14_11
    | ~ spl14_10
    | spl14_571
    | spl14_568 ),
    inference(avatar_split_clause,[],[f4612,f4606,f4627,f210,f214,f218,f222,f230])).

fof(f4612,plain,
    ( r1_orders_2(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_orders_2(sK1)
    | ~ l1_orders_2(sK0)
    | spl14_568 ),
    inference(resolution,[],[f4607,f119])).

fof(f4625,plain,
    ( ~ spl14_15
    | ~ spl14_13
    | ~ spl14_12
    | ~ spl14_11
    | ~ spl14_10
    | spl14_570
    | spl14_568 ),
    inference(avatar_split_clause,[],[f4611,f4606,f4623,f210,f214,f218,f222,f230])).

fof(f4611,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_orders_2(sK1)
    | ~ l1_orders_2(sK0)
    | spl14_568 ),
    inference(resolution,[],[f4607,f118])).

fof(f4621,plain,
    ( ~ spl14_15
    | ~ spl14_13
    | ~ spl14_12
    | ~ spl14_11
    | ~ spl14_10
    | spl14_569
    | spl14_568 ),
    inference(avatar_split_clause,[],[f4610,f4606,f4619,f210,f214,f218,f222,f230])).

fof(f4610,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_orders_2(sK1)
    | ~ l1_orders_2(sK0)
    | spl14_568 ),
    inference(resolution,[],[f4607,f117])).

fof(f4617,plain,
    ( ~ spl14_15
    | ~ spl14_13
    | ~ spl14_12
    | ~ spl14_11
    | ~ spl14_10
    | spl14_16
    | spl14_14
    | ~ spl14_1
    | spl14_568 ),
    inference(avatar_split_clause,[],[f4609,f4606,f170,f226,f234,f210,f214,f218,f222,f230])).

fof(f4609,plain,
    ( ~ v23_waybel_0(sK2,sK0,sK1)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_orders_2(sK1)
    | ~ l1_orders_2(sK0)
    | spl14_568 ),
    inference(resolution,[],[f4607,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( v5_orders_3(X2,X0,X1)
      | ~ v23_waybel_0(X2,X0,X1)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f4608,plain,
    ( ~ spl14_449
    | spl14_460
    | ~ spl14_568
    | ~ spl14_10
    | ~ spl14_448
    | ~ spl14_12
    | ~ spl14_13
    | ~ spl14_11
    | ~ spl14_564 ),
    inference(avatar_split_clause,[],[f4604,f4560,f214,f222,f218,f3406,f210,f4606,f3536,f3412])).

fof(f3412,plain,
    ( spl14_449
  <=> m1_subset_1(k1_funct_1(sK2,sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_449])])).

fof(f3536,plain,
    ( spl14_460
  <=> r1_orders_2(sK1,k1_funct_1(sK2,sK3),k1_funct_1(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_460])])).

fof(f3406,plain,
    ( spl14_448
  <=> m1_subset_1(k1_funct_1(sK2,sK4),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_448])])).

fof(f4560,plain,
    ( spl14_564
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(k1_funct_1(X0,sK4),u1_struct_0(X1))
        | ~ l1_orders_2(X1)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | ~ v5_orders_3(X0,sK0,X1)
        | r1_orders_2(X1,k1_funct_1(X0,sK3),k1_funct_1(X0,sK4))
        | ~ m1_subset_1(k1_funct_1(X0,sK3),u1_struct_0(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_564])])).

fof(f4604,plain,
    ( ~ l1_orders_2(sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(k1_funct_1(sK2,sK4),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v5_orders_3(sK2,sK0,sK1)
    | r1_orders_2(sK1,k1_funct_1(sK2,sK3),k1_funct_1(sK2,sK4))
    | ~ m1_subset_1(k1_funct_1(sK2,sK3),u1_struct_0(sK1))
    | ~ spl14_11
    | ~ spl14_564 ),
    inference(resolution,[],[f4561,f215])).

fof(f215,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl14_11 ),
    inference(avatar_component_clause,[],[f214])).

fof(f4561,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ l1_orders_2(X1)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(k1_funct_1(X0,sK4),u1_struct_0(X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | ~ v5_orders_3(X0,sK0,X1)
        | r1_orders_2(X1,k1_funct_1(X0,sK3),k1_funct_1(X0,sK4))
        | ~ m1_subset_1(k1_funct_1(X0,sK3),u1_struct_0(X1)) )
    | ~ spl14_564 ),
    inference(avatar_component_clause,[],[f4560])).

fof(f4581,plain,
    ( ~ spl14_6
    | ~ spl14_460
    | ~ spl14_78
    | spl14_450 ),
    inference(avatar_split_clause,[],[f4579,f3432,f712,f3536,f189])).

fof(f189,plain,
    ( spl14_6
  <=> m1_subset_1(sK4,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_6])])).

fof(f3432,plain,
    ( spl14_450
  <=> r1_orders_2(sK1,k1_funct_1(sK2,sK3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_450])])).

fof(f4579,plain,
    ( ~ r1_orders_2(sK1,k1_funct_1(sK2,sK3),k1_funct_1(sK2,sK4))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ spl14_78
    | spl14_450 ),
    inference(superposition,[],[f4575,f713])).

fof(f4575,plain,
    ( ~ r1_orders_2(sK1,k1_funct_1(sK2,sK3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4))
    | spl14_450 ),
    inference(avatar_component_clause,[],[f3432])).

fof(f4576,plain,
    ( ~ spl14_7
    | ~ spl14_450
    | spl14_5
    | ~ spl14_78 ),
    inference(avatar_split_clause,[],[f4573,f712,f182,f3432,f193])).

fof(f193,plain,
    ( spl14_7
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_7])])).

fof(f182,plain,
    ( spl14_5
  <=> r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_5])])).

fof(f4573,plain,
    ( ~ r1_orders_2(sK1,k1_funct_1(sK2,sK3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | spl14_5
    | ~ spl14_78 ),
    inference(superposition,[],[f183,f713])).

fof(f183,plain,
    ( ~ r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4))
    | spl14_5 ),
    inference(avatar_component_clause,[],[f182])).

fof(f4562,plain,
    ( ~ spl14_15
    | ~ spl14_7
    | ~ spl14_6
    | spl14_564
    | ~ spl14_4 ),
    inference(avatar_split_clause,[],[f4558,f179,f4560,f189,f193,f230])).

fof(f179,plain,
    ( spl14_4
  <=> r1_orders_2(sK0,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_4])])).

fof(f4558,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k1_funct_1(X0,sK4),u1_struct_0(X1))
        | ~ m1_subset_1(k1_funct_1(X0,sK3),u1_struct_0(X1))
        | r1_orders_2(X1,k1_funct_1(X0,sK3),k1_funct_1(X0,sK4))
        | ~ m1_subset_1(sK4,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ v5_orders_3(X0,sK0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ l1_orders_2(X1)
        | ~ l1_orders_2(sK0) )
    | ~ spl14_4 ),
    inference(resolution,[],[f185,f157])).

fof(f157,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( ~ r1_orders_2(X0,X7,X8)
      | ~ m1_subset_1(k1_funct_1(X2,X8),u1_struct_0(X1))
      | ~ m1_subset_1(k1_funct_1(X2,X7),u1_struct_0(X1))
      | r1_orders_2(X1,k1_funct_1(X2,X7),k1_funct_1(X2,X8))
      | ~ m1_subset_1(X8,u1_struct_0(X0))
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | ~ v5_orders_3(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f156])).

fof(f156,plain,(
    ! [X2,X0,X8,X7,X1,X9] :
      ( r1_orders_2(X1,X9,k1_funct_1(X2,X8))
      | k1_funct_1(X2,X7) != X9
      | ~ m1_subset_1(k1_funct_1(X2,X8),u1_struct_0(X1))
      | ~ m1_subset_1(X9,u1_struct_0(X1))
      | ~ r1_orders_2(X0,X7,X8)
      | ~ m1_subset_1(X8,u1_struct_0(X0))
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | ~ v5_orders_3(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f116])).

fof(f116,plain,(
    ! [X2,X0,X10,X8,X7,X1,X9] :
      ( r1_orders_2(X1,X9,X10)
      | k1_funct_1(X2,X8) != X10
      | k1_funct_1(X2,X7) != X9
      | ~ m1_subset_1(X10,u1_struct_0(X1))
      | ~ m1_subset_1(X9,u1_struct_0(X1))
      | ~ r1_orders_2(X0,X7,X8)
      | ~ m1_subset_1(X8,u1_struct_0(X0))
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | ~ v5_orders_3(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f185,plain,
    ( r1_orders_2(sK0,sK3,sK4)
    | ~ spl14_4 ),
    inference(avatar_component_clause,[],[f179])).

fof(f4557,plain,
    ( ~ spl14_6
    | spl14_4
    | ~ spl14_78
    | ~ spl14_483
    | ~ spl14_560 ),
    inference(avatar_split_clause,[],[f4556,f4537,f3788,f712,f179,f189])).

fof(f3788,plain,
    ( spl14_483
  <=> sK4 = k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_483])])).

fof(f4537,plain,
    ( spl14_560
  <=> r1_orders_2(sK0,sK3,k1_funct_1(k2_funct_1(sK2),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_560])])).

fof(f4556,plain,
    ( r1_orders_2(sK0,sK3,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ spl14_78
    | ~ spl14_483
    | ~ spl14_560 ),
    inference(forward_demodulation,[],[f4547,f3789])).

fof(f3789,plain,
    ( sK4 = k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK4))
    | ~ spl14_483 ),
    inference(avatar_component_clause,[],[f3788])).

fof(f4547,plain,
    ( r1_orders_2(sK0,sK3,k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK4)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ spl14_78
    | ~ spl14_560 ),
    inference(superposition,[],[f4538,f713])).

fof(f4538,plain,
    ( r1_orders_2(sK0,sK3,k1_funct_1(k2_funct_1(sK2),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4)))
    | ~ spl14_560 ),
    inference(avatar_component_clause,[],[f4537])).

fof(f4539,plain,
    ( ~ spl14_7
    | spl14_560
    | ~ spl14_78
    | ~ spl14_482
    | ~ spl14_527 ),
    inference(avatar_split_clause,[],[f4535,f4097,f3784,f712,f4537,f193])).

fof(f3784,plain,
    ( spl14_482
  <=> sK3 = k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_482])])).

fof(f4097,plain,
    ( spl14_527
  <=> r1_orders_2(sK0,k1_funct_1(k2_funct_1(sK2),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)),k1_funct_1(k2_funct_1(sK2),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_527])])).

fof(f4535,plain,
    ( r1_orders_2(sK0,sK3,k1_funct_1(k2_funct_1(sK2),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl14_78
    | ~ spl14_482
    | ~ spl14_527 ),
    inference(forward_demodulation,[],[f4525,f3785])).

fof(f3785,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK3))
    | ~ spl14_482 ),
    inference(avatar_component_clause,[],[f3784])).

fof(f4525,plain,
    ( r1_orders_2(sK0,k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK3)),k1_funct_1(k2_funct_1(sK2),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl14_78
    | ~ spl14_527 ),
    inference(superposition,[],[f4098,f713])).

fof(f4098,plain,
    ( r1_orders_2(sK0,k1_funct_1(k2_funct_1(sK2),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)),k1_funct_1(k2_funct_1(sK2),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4)))
    | ~ spl14_527 ),
    inference(avatar_component_clause,[],[f4097])).

fof(f4115,plain,
    ( ~ spl14_6
    | ~ spl14_78
    | ~ spl14_483
    | spl14_528 ),
    inference(avatar_split_clause,[],[f4114,f4101,f3788,f712,f189])).

fof(f4101,plain,
    ( spl14_528
  <=> m1_subset_1(k1_funct_1(k2_funct_1(sK2),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_528])])).

fof(f4114,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ spl14_78
    | ~ spl14_483
    | spl14_528 ),
    inference(duplicate_literal_removal,[],[f4113])).

fof(f4113,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ spl14_78
    | ~ spl14_483
    | spl14_528 ),
    inference(forward_demodulation,[],[f4111,f3789])).

fof(f4111,plain,
    ( ~ m1_subset_1(k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK4)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ spl14_78
    | spl14_528 ),
    inference(superposition,[],[f4102,f713])).

fof(f4102,plain,
    ( ~ m1_subset_1(k1_funct_1(k2_funct_1(sK2),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4)),u1_struct_0(sK0))
    | spl14_528 ),
    inference(avatar_component_clause,[],[f4101])).

fof(f4109,plain,
    ( ~ spl14_7
    | ~ spl14_78
    | ~ spl14_482
    | spl14_526 ),
    inference(avatar_split_clause,[],[f4108,f4094,f3784,f712,f193])).

fof(f4094,plain,
    ( spl14_526
  <=> m1_subset_1(k1_funct_1(k2_funct_1(sK2),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_526])])).

fof(f4108,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl14_78
    | ~ spl14_482
    | spl14_526 ),
    inference(duplicate_literal_removal,[],[f4107])).

fof(f4107,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl14_78
    | ~ spl14_482
    | spl14_526 ),
    inference(forward_demodulation,[],[f4105,f3785])).

fof(f4105,plain,
    ( ~ m1_subset_1(k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK3)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl14_78
    | spl14_526 ),
    inference(superposition,[],[f4095,f713])).

fof(f4095,plain,
    ( ~ m1_subset_1(k1_funct_1(k2_funct_1(sK2),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)),u1_struct_0(sK0))
    | spl14_526 ),
    inference(avatar_component_clause,[],[f4094])).

fof(f4103,plain,
    ( ~ spl14_526
    | spl14_527
    | ~ spl14_269
    | ~ spl14_305
    | ~ spl14_528
    | ~ spl14_156
    | ~ spl14_15
    | ~ spl14_303
    | ~ spl14_454 ),
    inference(avatar_split_clause,[],[f4092,f3472,f2579,f230,f1523,f4101,f2593,f2325,f4097,f4094])).

fof(f3472,plain,
    ( spl14_454
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(k1_funct_1(X0,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4)),u1_struct_0(X1))
        | ~ l1_orders_2(X1)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
        | ~ v5_orders_3(X0,sK1,X1)
        | r1_orders_2(X1,k1_funct_1(X0,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)),k1_funct_1(X0,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4)))
        | ~ m1_subset_1(k1_funct_1(X0,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)),u1_struct_0(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_454])])).

fof(f4092,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(k1_funct_1(k2_funct_1(sK2),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4)),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v5_orders_3(k2_funct_1(sK2),sK1,sK0)
    | r1_orders_2(sK0,k1_funct_1(k2_funct_1(sK2),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)),k1_funct_1(k2_funct_1(sK2),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4)))
    | ~ m1_subset_1(k1_funct_1(k2_funct_1(sK2),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)),u1_struct_0(sK0))
    | ~ spl14_303
    | ~ spl14_454 ),
    inference(resolution,[],[f3473,f2580])).

fof(f3473,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
        | ~ l1_orders_2(X1)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(k1_funct_1(X0,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4)),u1_struct_0(X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
        | ~ v5_orders_3(X0,sK1,X1)
        | r1_orders_2(X1,k1_funct_1(X0,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)),k1_funct_1(X0,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4)))
        | ~ m1_subset_1(k1_funct_1(X0,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)),u1_struct_0(X1)) )
    | ~ spl14_454 ),
    inference(avatar_component_clause,[],[f3472])).

fof(f3790,plain,
    ( spl14_483
    | ~ spl14_354
    | ~ spl14_473 ),
    inference(avatar_split_clause,[],[f3702,f3684,f2875,f3788])).

fof(f2875,plain,
    ( spl14_354
  <=> r2_hidden(sK4,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_354])])).

fof(f3702,plain,
    ( sK4 = k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK4))
    | ~ spl14_354
    | ~ spl14_473 ),
    inference(resolution,[],[f3685,f2876])).

fof(f2876,plain,
    ( r2_hidden(sK4,u1_struct_0(sK0))
    | ~ spl14_354 ),
    inference(avatar_component_clause,[],[f2875])).

fof(f3786,plain,
    ( spl14_482
    | ~ spl14_355
    | ~ spl14_473 ),
    inference(avatar_split_clause,[],[f3701,f3684,f2882,f3784])).

fof(f2882,plain,
    ( spl14_355
  <=> r2_hidden(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_355])])).

fof(f3701,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK3))
    | ~ spl14_355
    | ~ spl14_473 ),
    inference(resolution,[],[f3685,f2883])).

fof(f2883,plain,
    ( r2_hidden(sK3,u1_struct_0(sK0))
    | ~ spl14_355 ),
    inference(avatar_component_clause,[],[f2882])).

fof(f3686,plain,
    ( spl14_23
    | spl14_473
    | ~ spl14_11
    | ~ spl14_10
    | ~ spl14_133 ),
    inference(avatar_split_clause,[],[f3682,f1407,f210,f214,f3684,f293])).

fof(f293,plain,
    ( spl14_23
  <=> k1_xboole_0 = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_23])])).

fof(f1407,plain,
    ( spl14_133
  <=> ! [X1,X0,X2] :
        ( k1_xboole_0 = X0
        | ~ v1_funct_2(sK2,X2,X0)
        | ~ r2_hidden(X1,X2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        | k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,X1)) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_133])])).

fof(f3682,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ r2_hidden(X0,u1_struct_0(sK0))
        | k1_xboole_0 = u1_struct_0(sK1)
        | k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,X0)) = X0 )
    | ~ spl14_10
    | ~ spl14_133 ),
    inference(resolution,[],[f1408,f211])).

fof(f1408,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        | ~ v1_funct_2(sK2,X2,X0)
        | ~ r2_hidden(X1,X2)
        | k1_xboole_0 = X0
        | k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,X1)) = X1 )
    | ~ spl14_133 ),
    inference(avatar_component_clause,[],[f1407])).

fof(f3492,plain,
    ( ~ spl14_6
    | ~ spl14_67
    | spl14_453 ),
    inference(avatar_split_clause,[],[f3489,f3469,f590,f189])).

fof(f590,plain,
    ( spl14_67
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_subset_1(k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_67])])).

fof(f3469,plain,
    ( spl14_453
  <=> m1_subset_1(k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_453])])).

fof(f3489,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ spl14_67
    | spl14_453 ),
    inference(resolution,[],[f3470,f591])).

fof(f591,plain,
    ( ! [X0] :
        ( m1_subset_1(k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl14_67 ),
    inference(avatar_component_clause,[],[f590])).

fof(f3470,plain,
    ( ~ m1_subset_1(k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4),u1_struct_0(sK1))
    | spl14_453 ),
    inference(avatar_component_clause,[],[f3469])).

fof(f3478,plain,
    ( ~ spl14_7
    | ~ spl14_67
    | spl14_452 ),
    inference(avatar_split_clause,[],[f3475,f3466,f590,f193])).

fof(f3466,plain,
    ( spl14_452
  <=> m1_subset_1(k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_452])])).

fof(f3475,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl14_67
    | spl14_452 ),
    inference(resolution,[],[f3467,f591])).

fof(f3467,plain,
    ( ~ m1_subset_1(k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),u1_struct_0(sK1))
    | spl14_452 ),
    inference(avatar_component_clause,[],[f3466])).

fof(f3474,plain,
    ( ~ spl14_13
    | ~ spl14_452
    | ~ spl14_453
    | spl14_454
    | ~ spl14_5 ),
    inference(avatar_split_clause,[],[f3464,f182,f3472,f3469,f3466,f222])).

fof(f3464,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k1_funct_1(X0,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4)),u1_struct_0(X1))
        | ~ m1_subset_1(k1_funct_1(X0,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)),u1_struct_0(X1))
        | r1_orders_2(X1,k1_funct_1(X0,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)),k1_funct_1(X0,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4)))
        | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4),u1_struct_0(sK1))
        | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),u1_struct_0(sK1))
        | ~ v5_orders_3(X0,sK1,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ l1_orders_2(X1)
        | ~ l1_orders_2(sK1) )
    | ~ spl14_5 ),
    inference(resolution,[],[f157,f186])).

fof(f186,plain,
    ( r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4))
    | ~ spl14_5 ),
    inference(avatar_component_clause,[],[f182])).

fof(f3414,plain,
    ( spl14_449
    | ~ spl14_357 ),
    inference(avatar_split_clause,[],[f3409,f2901,f3412])).

fof(f2901,plain,
    ( spl14_357
  <=> r2_hidden(k1_funct_1(sK2,sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_357])])).

fof(f3409,plain,
    ( m1_subset_1(k1_funct_1(sK2,sK3),u1_struct_0(sK1))
    | ~ spl14_357 ),
    inference(resolution,[],[f2902,f137])).

fof(f137,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f2902,plain,
    ( r2_hidden(k1_funct_1(sK2,sK3),u1_struct_0(sK1))
    | ~ spl14_357 ),
    inference(avatar_component_clause,[],[f2901])).

fof(f3408,plain,
    ( spl14_448
    | ~ spl14_356 ),
    inference(avatar_split_clause,[],[f3403,f2891,f3406])).

fof(f2891,plain,
    ( spl14_356
  <=> r2_hidden(k1_funct_1(sK2,sK4),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_356])])).

fof(f3403,plain,
    ( m1_subset_1(k1_funct_1(sK2,sK4),u1_struct_0(sK1))
    | ~ spl14_356 ),
    inference(resolution,[],[f2892,f137])).

fof(f2892,plain,
    ( r2_hidden(k1_funct_1(sK2,sK4),u1_struct_0(sK1))
    | ~ spl14_356 ),
    inference(avatar_component_clause,[],[f2891])).

fof(f3402,plain,
    ( ~ spl14_20
    | ~ spl14_12
    | spl14_447
    | ~ spl14_18
    | ~ spl14_32 ),
    inference(avatar_split_clause,[],[f3398,f343,f252,f3400,f218,f271])).

fof(f343,plain,
    ( spl14_32
  <=> u1_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_32])])).

fof(f3398,plain,
    ( ! [X11] :
        ( r2_hidden(sK12(sK2,X11),u1_struct_0(sK0))
        | ~ r2_hidden(X11,u1_struct_0(sK1))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl14_18
    | ~ spl14_32 ),
    inference(forward_demodulation,[],[f3031,f344])).

fof(f344,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl14_32 ),
    inference(avatar_component_clause,[],[f343])).

fof(f3031,plain,
    ( ! [X11] :
        ( ~ r2_hidden(X11,u1_struct_0(sK1))
        | r2_hidden(sK12(sK2,X11),k1_relat_1(sK2))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl14_18 ),
    inference(superposition,[],[f161,f253])).

fof(f161,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k2_relat_1(X0))
      | r2_hidden(sK12(X0,X5),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f130])).

fof(f130,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK12(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f2903,plain,
    ( spl14_357
    | ~ spl14_18
    | ~ spl14_35
    | ~ spl14_355 ),
    inference(avatar_split_clause,[],[f2899,f2882,f357,f252,f2901])).

fof(f357,plain,
    ( spl14_35
  <=> ! [X1] :
        ( ~ r2_hidden(X1,u1_struct_0(sK0))
        | r2_hidden(k1_funct_1(sK2,X1),k2_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_35])])).

fof(f2899,plain,
    ( r2_hidden(k1_funct_1(sK2,sK3),u1_struct_0(sK1))
    | ~ spl14_18
    | ~ spl14_35
    | ~ spl14_355 ),
    inference(forward_demodulation,[],[f2896,f253])).

fof(f2896,plain,
    ( r2_hidden(k1_funct_1(sK2,sK3),k2_relat_1(sK2))
    | ~ spl14_35
    | ~ spl14_355 ),
    inference(resolution,[],[f2883,f358])).

fof(f358,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,u1_struct_0(sK0))
        | r2_hidden(k1_funct_1(sK2,X1),k2_relat_1(sK2)) )
    | ~ spl14_35 ),
    inference(avatar_component_clause,[],[f357])).

fof(f2893,plain,
    ( spl14_356
    | ~ spl14_18
    | ~ spl14_35
    | ~ spl14_354 ),
    inference(avatar_split_clause,[],[f2889,f2875,f357,f252,f2891])).

fof(f2889,plain,
    ( r2_hidden(k1_funct_1(sK2,sK4),u1_struct_0(sK1))
    | ~ spl14_18
    | ~ spl14_35
    | ~ spl14_354 ),
    inference(forward_demodulation,[],[f2886,f253])).

fof(f2886,plain,
    ( r2_hidden(k1_funct_1(sK2,sK4),k2_relat_1(sK2))
    | ~ spl14_35
    | ~ spl14_354 ),
    inference(resolution,[],[f2876,f358])).

fof(f2885,plain,
    ( ~ spl14_15
    | spl14_16
    | spl14_355
    | ~ spl14_7 ),
    inference(avatar_split_clause,[],[f2880,f193,f2882,f234,f230])).

fof(f2880,plain,
    ( r2_hidden(sK3,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl14_7 ),
    inference(resolution,[],[f194,f243])).

fof(f243,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | r2_hidden(X0,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ l1_orders_2(X1) ) ),
    inference(resolution,[],[f242,f101])).

fof(f101,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f242,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | r2_hidden(X0,u1_struct_0(X1))
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f138,f125])).

fof(f125,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f194,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl14_7 ),
    inference(avatar_component_clause,[],[f193])).

fof(f2878,plain,
    ( ~ spl14_15
    | spl14_16
    | spl14_354
    | ~ spl14_6 ),
    inference(avatar_split_clause,[],[f2873,f189,f2875,f234,f230])).

fof(f2873,plain,
    ( r2_hidden(sK4,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl14_6 ),
    inference(resolution,[],[f190,f243])).

fof(f190,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ spl14_6 ),
    inference(avatar_component_clause,[],[f189])).

fof(f2858,plain,
    ( ~ spl14_20
    | ~ spl14_12
    | ~ spl14_2
    | spl14_18
    | ~ spl14_325 ),
    inference(avatar_split_clause,[],[f2750,f2713,f252,f173,f218,f271])).

fof(f2713,plain,
    ( spl14_325
  <=> u1_struct_0(sK1) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_325])])).

fof(f2750,plain,
    ( u1_struct_0(sK1) = k2_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl14_325 ),
    inference(superposition,[],[f128,f2714])).

fof(f2714,plain,
    ( u1_struct_0(sK1) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl14_325 ),
    inference(avatar_component_clause,[],[f2713])).

fof(f128,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f2717,plain,
    ( k1_xboole_0 != u1_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2716,plain,
    ( ~ spl14_305
    | spl14_325
    | ~ spl14_312 ),
    inference(avatar_split_clause,[],[f2711,f2622,f2713,f2593])).

fof(f2622,plain,
    ( spl14_312
  <=> u1_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_312])])).

fof(f2711,plain,
    ( u1_struct_0(sK1) = k1_relat_1(k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl14_312 ),
    inference(superposition,[],[f141,f2623])).

fof(f2623,plain,
    ( u1_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl14_312 ),
    inference(avatar_component_clause,[],[f2622])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f2703,plain,
    ( ~ spl14_15
    | ~ spl14_13
    | ~ spl14_12
    | ~ spl14_11
    | ~ spl14_10
    | spl14_16
    | spl14_14
    | spl14_305
    | ~ spl14_1
    | ~ spl14_260 ),
    inference(avatar_split_clause,[],[f2700,f2254,f170,f2593,f226,f234,f210,f214,f218,f222,f230])).

fof(f2254,plain,
    ( spl14_260
  <=> k2_funct_1(sK2) = sK5(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_260])])).

fof(f2700,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_orders_2(sK1)
    | ~ l1_orders_2(sK0)
    | ~ spl14_1
    | ~ spl14_260 ),
    inference(forward_demodulation,[],[f2699,f2255])).

fof(f2255,plain,
    ( k2_funct_1(sK2) = sK5(sK0,sK1,sK2)
    | ~ spl14_260 ),
    inference(avatar_component_clause,[],[f2254])).

fof(f2699,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_orders_2(sK1)
    | ~ l1_orders_2(sK0)
    | ~ spl14_1 ),
    inference(resolution,[],[f106,f196])).

fof(f196,plain,
    ( v23_waybel_0(sK2,sK0,sK1)
    | ~ spl14_1 ),
    inference(avatar_component_clause,[],[f170])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ v23_waybel_0(X2,X0,X1)
      | m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f2624,plain,
    ( ~ spl14_305
    | spl14_34
    | spl14_312
    | ~ spl14_303 ),
    inference(avatar_split_clause,[],[f2588,f2579,f2622,f353,f2593])).

fof(f353,plain,
    ( spl14_34
  <=> k1_xboole_0 = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_34])])).

fof(f2588,plain,
    ( u1_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2))
    | k1_xboole_0 = u1_struct_0(sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl14_303 ),
    inference(resolution,[],[f2580,f143])).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f2581,plain,
    ( ~ spl14_15
    | ~ spl14_13
    | ~ spl14_12
    | ~ spl14_10
    | spl14_16
    | spl14_14
    | ~ spl14_1
    | spl14_303
    | ~ spl14_11
    | ~ spl14_260 ),
    inference(avatar_split_clause,[],[f2577,f2254,f214,f2579,f170,f226,f234,f210,f218,f222,f230])).

fof(f2577,plain,
    ( v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ l1_orders_2(sK1)
    | ~ l1_orders_2(sK0)
    | ~ spl14_11
    | ~ spl14_260 ),
    inference(forward_demodulation,[],[f2576,f2255])).

fof(f2576,plain,
    ( ~ v23_waybel_0(sK2,sK0,sK1)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(sK5(sK0,sK1,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ l1_orders_2(sK1)
    | ~ l1_orders_2(sK0)
    | ~ spl14_11 ),
    inference(resolution,[],[f105,f215])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v23_waybel_0(X2,X0,X1)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v1_funct_2(sK5(X0,X1,X2),u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f2327,plain,
    ( ~ spl14_15
    | ~ spl14_13
    | ~ spl14_12
    | ~ spl14_10
    | spl14_16
    | spl14_14
    | ~ spl14_1
    | spl14_269
    | ~ spl14_11
    | ~ spl14_260 ),
    inference(avatar_split_clause,[],[f2323,f2254,f214,f2325,f170,f226,f234,f210,f218,f222,f230])).

fof(f2323,plain,
    ( v5_orders_3(k2_funct_1(sK2),sK1,sK0)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ l1_orders_2(sK1)
    | ~ l1_orders_2(sK0)
    | ~ spl14_11
    | ~ spl14_260 ),
    inference(forward_demodulation,[],[f2322,f2255])).

fof(f2322,plain,
    ( ~ v23_waybel_0(sK2,sK0,sK1)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_orders_3(sK5(sK0,sK1,sK2),sK1,sK0)
    | ~ v1_funct_1(sK2)
    | ~ l1_orders_2(sK1)
    | ~ l1_orders_2(sK0)
    | ~ spl14_11 ),
    inference(resolution,[],[f108,f215])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v23_waybel_0(X2,X0,X1)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v5_orders_3(sK5(X0,X1,X2),X1,X0)
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f2256,plain,
    ( ~ spl14_15
    | ~ spl14_13
    | ~ spl14_12
    | spl14_260
    | ~ spl14_10
    | spl14_16
    | spl14_14
    | ~ spl14_1
    | ~ spl14_11 ),
    inference(avatar_split_clause,[],[f2252,f214,f170,f226,f234,f210,f2254,f218,f222,f230])).

fof(f2252,plain,
    ( ~ v23_waybel_0(sK2,sK0,sK1)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_funct_1(sK2) = sK5(sK0,sK1,sK2)
    | ~ v1_funct_1(sK2)
    | ~ l1_orders_2(sK1)
    | ~ l1_orders_2(sK0)
    | ~ spl14_11 ),
    inference(resolution,[],[f107,f215])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v23_waybel_0(X2,X0,X1)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k2_funct_1(X2) = sK5(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f1552,plain,
    ( ~ spl14_20
    | ~ spl14_12
    | spl14_156 ),
    inference(avatar_split_clause,[],[f1547,f1523,f218,f271])).

fof(f1547,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl14_156 ),
    inference(resolution,[],[f1524,f127])).

fof(f127,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f1524,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl14_156 ),
    inference(avatar_component_clause,[],[f1523])).

fof(f1417,plain,
    ( ~ spl14_12
    | spl14_135
    | ~ spl14_2 ),
    inference(avatar_split_clause,[],[f1403,f173,f1415,f218])).

fof(f1403,plain,
    ( ! [X6,X5] :
        ( k2_relset_1(X5,X6,sK2) != X6
        | v1_funct_2(k2_funct_1(sK2),X6,X5)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | ~ v1_funct_2(sK2,X5,X6)
        | ~ v1_funct_1(sK2) )
    | ~ spl14_2 ),
    inference(resolution,[],[f207,f150])).

fof(f150,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | v1_funct_2(k2_funct_1(X2),X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f207,plain,
    ( v2_funct_1(sK2)
    | ~ spl14_2 ),
    inference(avatar_component_clause,[],[f173])).

fof(f1413,plain,
    ( ~ spl14_12
    | spl14_134
    | ~ spl14_2 ),
    inference(avatar_split_clause,[],[f1402,f173,f1411,f218])).

fof(f1402,plain,
    ( ! [X4,X3] :
        ( k2_relset_1(X3,X4,sK2) != X4
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X4,X3)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | ~ v1_funct_2(sK2,X3,X4)
        | ~ v1_funct_1(sK2) )
    | ~ spl14_2 ),
    inference(resolution,[],[f207,f151])).

fof(f151,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f1409,plain,
    ( ~ spl14_12
    | spl14_133
    | ~ spl14_2 ),
    inference(avatar_split_clause,[],[f1401,f173,f1407,f218])).

fof(f1401,plain,
    ( ! [X2,X0,X1] :
        ( k1_xboole_0 = X0
        | ~ r2_hidden(X1,X2)
        | k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,X1)) = X1
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        | ~ v1_funct_2(sK2,X2,X0)
        | ~ v1_funct_1(sK2) )
    | ~ spl14_2 ),
    inference(resolution,[],[f207,f154])).

fof(f154,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_funct_1(X3)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).

fof(f1399,plain,
    ( ~ spl14_15
    | ~ spl14_13
    | ~ spl14_12
    | spl14_2
    | ~ spl14_10
    | spl14_16
    | spl14_14
    | ~ spl14_1
    | ~ spl14_11 ),
    inference(avatar_split_clause,[],[f1398,f214,f170,f226,f234,f210,f173,f218,f222,f230])).

fof(f1398,plain,
    ( ~ v23_waybel_0(sK2,sK0,sK1)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ l1_orders_2(sK1)
    | ~ l1_orders_2(sK0)
    | ~ spl14_11 ),
    inference(resolution,[],[f102,f215])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v23_waybel_0(X2,X0,X1)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f714,plain,
    ( spl14_45
    | ~ spl14_12
    | ~ spl14_10
    | spl14_78
    | ~ spl14_11 ),
    inference(avatar_split_clause,[],[f710,f214,f712,f210,f218,f417])).

fof(f417,plain,
    ( spl14_45
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_45])])).

fof(f710,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k1_funct_1(sK2,X0)
        | ~ v1_funct_1(sK2)
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl14_11 ),
    inference(resolution,[],[f153,f215])).

fof(f153,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f621,plain,
    ( ~ spl14_48
    | ~ spl14_70 ),
    inference(avatar_contradiction_clause,[],[f615])).

fof(f615,plain,
    ( $false
    | ~ spl14_48
    | ~ spl14_70 ),
    inference(subsumption_resolution,[],[f440,f605])).

fof(f605,plain,
    ( ! [X1] : ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ spl14_70 ),
    inference(avatar_component_clause,[],[f604])).

fof(f604,plain,
    ( spl14_70
  <=> ! [X1] : ~ m1_subset_1(X1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_70])])).

fof(f440,plain,
    ( m1_subset_1(sK12(sK2,k1_funct_1(sK2,sK13(u1_struct_0(sK0)))),u1_struct_0(sK0))
    | ~ spl14_48 ),
    inference(avatar_component_clause,[],[f439])).

fof(f439,plain,
    ( spl14_48
  <=> m1_subset_1(sK12(sK2,k1_funct_1(sK2,sK13(u1_struct_0(sK0)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_48])])).

fof(f606,plain,
    ( ~ spl14_69
    | spl14_70
    | ~ spl14_68 ),
    inference(avatar_split_clause,[],[f599,f595,f604,f601])).

fof(f595,plain,
    ( spl14_68
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_68])])).

fof(f599,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v1_xboole_0(u1_struct_0(sK1)) )
    | ~ spl14_68 ),
    inference(resolution,[],[f596,f139])).

fof(f139,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f596,plain,
    ( ! [X0] :
        ( r2_hidden(k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl14_68 ),
    inference(avatar_component_clause,[],[f595])).

fof(f597,plain,
    ( ~ spl14_13
    | spl14_14
    | spl14_68
    | ~ spl14_67 ),
    inference(avatar_split_clause,[],[f593,f590,f595,f226,f222])).

fof(f593,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),u1_struct_0(sK1))
        | v2_struct_0(sK1)
        | ~ l1_orders_2(sK1) )
    | ~ spl14_67 ),
    inference(resolution,[],[f591,f243])).

fof(f592,plain,
    ( spl14_45
    | ~ spl14_12
    | ~ spl14_10
    | spl14_67
    | ~ spl14_11 ),
    inference(avatar_split_clause,[],[f587,f214,f590,f210,f218,f417])).

fof(f587,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | m1_subset_1(k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),u1_struct_0(sK1))
        | ~ v1_funct_1(sK2)
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl14_11 ),
    inference(resolution,[],[f152,f215])).

fof(f152,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_funct_2)).

fof(f441,plain,
    ( spl14_48
    | ~ spl14_38 ),
    inference(avatar_split_clause,[],[f432,f379,f439])).

fof(f379,plain,
    ( spl14_38
  <=> r2_hidden(sK12(sK2,k1_funct_1(sK2,sK13(u1_struct_0(sK0)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_38])])).

fof(f432,plain,
    ( m1_subset_1(sK12(sK2,k1_funct_1(sK2,sK13(u1_struct_0(sK0)))),u1_struct_0(sK0))
    | ~ spl14_38 ),
    inference(resolution,[],[f380,f137])).

fof(f380,plain,
    ( r2_hidden(sK12(sK2,k1_funct_1(sK2,sK13(u1_struct_0(sK0)))),u1_struct_0(sK0))
    | ~ spl14_38 ),
    inference(avatar_component_clause,[],[f379])).

fof(f419,plain,
    ( ~ spl14_45
    | ~ spl14_42 ),
    inference(avatar_split_clause,[],[f407,f402,f417])).

fof(f402,plain,
    ( spl14_42
  <=> r2_hidden(sK12(sK2,sK13(k2_relat_1(sK2))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_42])])).

fof(f407,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl14_42 ),
    inference(resolution,[],[f403,f139])).

fof(f403,plain,
    ( r2_hidden(sK12(sK2,sK13(k2_relat_1(sK2))),u1_struct_0(sK0))
    | ~ spl14_42 ),
    inference(avatar_component_clause,[],[f402])).

fof(f404,plain,
    ( ~ spl14_20
    | ~ spl14_12
    | spl14_42
    | ~ spl14_32
    | ~ spl14_41 ),
    inference(avatar_split_clause,[],[f400,f394,f343,f402,f218,f271])).

fof(f394,plain,
    ( spl14_41
  <=> r2_hidden(sK13(k2_relat_1(sK2)),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_41])])).

fof(f400,plain,
    ( r2_hidden(sK12(sK2,sK13(k2_relat_1(sK2))),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl14_32
    | ~ spl14_41 ),
    inference(forward_demodulation,[],[f397,f344])).

fof(f397,plain,
    ( r2_hidden(sK12(sK2,sK13(k2_relat_1(sK2))),k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl14_41 ),
    inference(resolution,[],[f395,f161])).

fof(f395,plain,
    ( r2_hidden(sK13(k2_relat_1(sK2)),k2_relat_1(sK2))
    | ~ spl14_41 ),
    inference(avatar_component_clause,[],[f394])).

fof(f396,plain,
    ( spl14_41
    | spl14_40 ),
    inference(avatar_split_clause,[],[f391,f387,f394])).

fof(f387,plain,
    ( spl14_40
  <=> v1_xboole_0(k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_40])])).

fof(f391,plain,
    ( r2_hidden(sK13(k2_relat_1(sK2)),k2_relat_1(sK2))
    | spl14_40 ),
    inference(resolution,[],[f390,f136])).

fof(f136,plain,(
    ! [X0] : m1_subset_1(sK13(X0),X0) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0] : m1_subset_1(sK13(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f9,f82])).

fof(f82,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK13(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f9,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f390,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k2_relat_1(sK2))
        | r2_hidden(X0,k2_relat_1(sK2)) )
    | spl14_40 ),
    inference(resolution,[],[f388,f138])).

fof(f388,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | spl14_40 ),
    inference(avatar_component_clause,[],[f387])).

fof(f389,plain,
    ( ~ spl14_40
    | ~ spl14_36 ),
    inference(avatar_split_clause,[],[f372,f366,f387])).

fof(f366,plain,
    ( spl14_36
  <=> r2_hidden(k1_funct_1(sK2,sK13(u1_struct_0(sK0))),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_36])])).

fof(f372,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | ~ spl14_36 ),
    inference(resolution,[],[f367,f139])).

fof(f367,plain,
    ( r2_hidden(k1_funct_1(sK2,sK13(u1_struct_0(sK0))),k2_relat_1(sK2))
    | ~ spl14_36 ),
    inference(avatar_component_clause,[],[f366])).

fof(f381,plain,
    ( ~ spl14_20
    | ~ spl14_12
    | spl14_38
    | ~ spl14_32
    | ~ spl14_36 ),
    inference(avatar_split_clause,[],[f377,f366,f343,f379,f218,f271])).

fof(f377,plain,
    ( r2_hidden(sK12(sK2,k1_funct_1(sK2,sK13(u1_struct_0(sK0)))),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl14_32
    | ~ spl14_36 ),
    inference(forward_demodulation,[],[f370,f344])).

fof(f370,plain,
    ( r2_hidden(sK12(sK2,k1_funct_1(sK2,sK13(u1_struct_0(sK0)))),k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl14_36 ),
    inference(resolution,[],[f367,f161])).

fof(f368,plain,
    ( ~ spl14_15
    | spl14_16
    | spl14_36
    | ~ spl14_35 ),
    inference(avatar_split_clause,[],[f362,f357,f366,f234,f230])).

fof(f362,plain,
    ( r2_hidden(k1_funct_1(sK2,sK13(u1_struct_0(sK0))),k2_relat_1(sK2))
    | v2_struct_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl14_35 ),
    inference(resolution,[],[f358,f244])).

fof(f244,plain,(
    ! [X0] :
      ( r2_hidden(sK13(u1_struct_0(X0)),u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f243,f136])).

fof(f359,plain,
    ( ~ spl14_20
    | ~ spl14_12
    | spl14_35
    | ~ spl14_32 ),
    inference(avatar_split_clause,[],[f348,f343,f357,f218,f271])).

fof(f348,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,u1_struct_0(sK0))
        | r2_hidden(k1_funct_1(sK2,X1),k2_relat_1(sK2))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl14_32 ),
    inference(superposition,[],[f159,f344])).

fof(f159,plain,(
    ! [X6,X0] :
      ( ~ r2_hidden(X6,k1_relat_1(X0))
      | r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f158])).

fof(f158,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f132])).

fof(f132,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f346,plain,
    ( ~ spl14_10
    | spl14_32
    | ~ spl14_24 ),
    inference(avatar_split_clause,[],[f341,f296,f343,f210])).

fof(f296,plain,
    ( spl14_24
  <=> u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_24])])).

fof(f341,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl14_24 ),
    inference(superposition,[],[f141,f297])).

fof(f297,plain,
    ( u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl14_24 ),
    inference(avatar_component_clause,[],[f296])).

fof(f327,plain,
    ( spl14_14
    | ~ spl14_13
    | ~ spl14_17
    | ~ spl14_23 ),
    inference(avatar_split_clause,[],[f307,f293,f238,f222,f226])).

fof(f238,plain,
    ( spl14_17
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_17])])).

fof(f307,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ spl14_23 ),
    inference(superposition,[],[f246,f294])).

fof(f294,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl14_23 ),
    inference(avatar_component_clause,[],[f293])).

fof(f246,plain,(
    ! [X1] :
      ( ~ v1_xboole_0(u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f244,f139])).

fof(f298,plain,
    ( ~ spl14_10
    | spl14_23
    | spl14_24
    | ~ spl14_11 ),
    inference(avatar_split_clause,[],[f290,f214,f296,f293,f210])).

fof(f290,plain,
    ( u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k1_xboole_0 = u1_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl14_11 ),
    inference(resolution,[],[f143,f215])).

fof(f283,plain,
    ( ~ spl14_10
    | spl14_20 ),
    inference(avatar_contradiction_clause,[],[f282])).

fof(f282,plain,
    ( $false
    | ~ spl14_10
    | spl14_20 ),
    inference(subsumption_resolution,[],[f211,f281])).

fof(f281,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl14_20 ),
    inference(resolution,[],[f272,f140])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f272,plain,
    ( ~ v1_relat_1(sK2)
    | spl14_20 ),
    inference(avatar_component_clause,[],[f271])).

fof(f261,plain,
    ( ~ spl14_18
    | spl14_3
    | ~ spl14_19 ),
    inference(avatar_split_clause,[],[f259,f256,f176,f252])).

fof(f176,plain,
    ( spl14_3
  <=> u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_3])])).

fof(f259,plain,
    ( u1_struct_0(sK1) != k2_relat_1(sK2)
    | spl14_3
    | ~ spl14_19 ),
    inference(superposition,[],[f177,f257])).

fof(f177,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | spl14_3 ),
    inference(avatar_component_clause,[],[f176])).

fof(f258,plain,
    ( spl14_19
    | ~ spl14_10 ),
    inference(avatar_split_clause,[],[f248,f210,f256])).

fof(f248,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl14_10 ),
    inference(resolution,[],[f142,f211])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f254,plain,
    ( spl14_18
    | ~ spl14_3
    | ~ spl14_10 ),
    inference(avatar_split_clause,[],[f250,f210,f176,f252])).

fof(f250,plain,
    ( u1_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl14_3
    | ~ spl14_10 ),
    inference(forward_demodulation,[],[f248,f205])).

fof(f205,plain,
    ( u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl14_3 ),
    inference(avatar_component_clause,[],[f176])).

fof(f240,plain,(
    spl14_17 ),
    inference(avatar_split_clause,[],[f100,f238])).

fof(f100,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f236,plain,(
    ~ spl14_16 ),
    inference(avatar_split_clause,[],[f85,f234])).

fof(f85,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,
    ( ( ( ( ~ r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4))
          | ~ r1_orders_2(sK0,sK3,sK4) )
        & ( r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4))
          | r1_orders_2(sK0,sK3,sK4) )
        & m1_subset_1(sK4,u1_struct_0(sK0))
        & m1_subset_1(sK3,u1_struct_0(sK0)) )
      | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
      | ~ v2_funct_1(sK2)
      | ~ v23_waybel_0(sK2,sK0,sK1) )
    & ( ( ! [X5] :
            ( ! [X6] :
                ( ( ( r1_orders_2(sK0,X5,X6)
                    | ~ r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X5),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X6)) )
                  & ( r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X5),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X6))
                    | ~ r1_orders_2(sK0,X5,X6) ) )
                | ~ m1_subset_1(X6,u1_struct_0(sK0)) )
            | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
        & u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
        & v2_funct_1(sK2) )
      | v23_waybel_0(sK2,sK0,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_orders_2(sK1)
    & ~ v2_struct_0(sK1)
    & l1_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f57,f62,f61,f60,f59,f58])).

fof(f58,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( ? [X4] :
                          ( ( ~ r1_orders_2(X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X4))
                            | ~ r1_orders_2(X0,X3,X4) )
                          & ( r1_orders_2(X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X4))
                            | r1_orders_2(X0,X3,X4) )
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | u1_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  | ~ v2_funct_1(X2)
                  | ~ v23_waybel_0(X2,X0,X1) )
                & ( ( ! [X5] :
                        ( ! [X6] :
                            ( ( ( r1_orders_2(X0,X5,X6)
                                | ~ r1_orders_2(X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X5),k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X6)) )
                              & ( r1_orders_2(X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X5),k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X6))
                                | ~ r1_orders_2(X0,X5,X6) ) )
                            | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                        | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                    & u1_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                    & v2_funct_1(X2) )
                  | v23_waybel_0(X2,X0,X1) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_orders_2(X1)
            & ~ v2_struct_0(X1) )
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ? [X4] :
                        ( ( ~ r1_orders_2(X1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(X1),X2,X3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(X1),X2,X4))
                          | ~ r1_orders_2(sK0,X3,X4) )
                        & ( r1_orders_2(X1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(X1),X2,X3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(X1),X2,X4))
                          | r1_orders_2(sK0,X3,X4) )
                        & m1_subset_1(X4,u1_struct_0(sK0)) )
                    & m1_subset_1(X3,u1_struct_0(sK0)) )
                | u1_struct_0(X1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
                | ~ v2_funct_1(X2)
                | ~ v23_waybel_0(X2,sK0,X1) )
              & ( ( ! [X5] :
                      ( ! [X6] :
                          ( ( ( r1_orders_2(sK0,X5,X6)
                              | ~ r1_orders_2(X1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(X1),X2,X5),k3_funct_2(u1_struct_0(sK0),u1_struct_0(X1),X2,X6)) )
                            & ( r1_orders_2(X1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(X1),X2,X5),k3_funct_2(u1_struct_0(sK0),u1_struct_0(X1),X2,X6))
                              | ~ r1_orders_2(sK0,X5,X6) ) )
                          | ~ m1_subset_1(X6,u1_struct_0(sK0)) )
                      | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
                  & u1_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
                  & v2_funct_1(X2) )
                | v23_waybel_0(X2,sK0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ r1_orders_2(X1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(X1),X2,X3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(X1),X2,X4))
                        | ~ r1_orders_2(sK0,X3,X4) )
                      & ( r1_orders_2(X1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(X1),X2,X3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(X1),X2,X4))
                        | r1_orders_2(sK0,X3,X4) )
                      & m1_subset_1(X4,u1_struct_0(sK0)) )
                  & m1_subset_1(X3,u1_struct_0(sK0)) )
              | u1_struct_0(X1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
              | ~ v2_funct_1(X2)
              | ~ v23_waybel_0(X2,sK0,X1) )
            & ( ( ! [X5] :
                    ( ! [X6] :
                        ( ( ( r1_orders_2(sK0,X5,X6)
                            | ~ r1_orders_2(X1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(X1),X2,X5),k3_funct_2(u1_struct_0(sK0),u1_struct_0(X1),X2,X6)) )
                          & ( r1_orders_2(X1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(X1),X2,X5),k3_funct_2(u1_struct_0(sK0),u1_struct_0(X1),X2,X6))
                            | ~ r1_orders_2(sK0,X5,X6) ) )
                        | ~ m1_subset_1(X6,u1_struct_0(sK0)) )
                    | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
                & u1_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
                & v2_funct_1(X2) )
              | v23_waybel_0(X2,sK0,X1) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_orders_2(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( ? [X3] :
                ( ? [X4] :
                    ( ( ~ r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X2,X4))
                      | ~ r1_orders_2(sK0,X3,X4) )
                    & ( r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X2,X4))
                      | r1_orders_2(sK0,X3,X4) )
                    & m1_subset_1(X4,u1_struct_0(sK0)) )
                & m1_subset_1(X3,u1_struct_0(sK0)) )
            | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2)
            | ~ v2_funct_1(X2)
            | ~ v23_waybel_0(X2,sK0,sK1) )
          & ( ( ! [X5] :
                  ( ! [X6] :
                      ( ( ( r1_orders_2(sK0,X5,X6)
                          | ~ r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X2,X5),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X2,X6)) )
                        & ( r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X2,X5),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X2,X6))
                          | ~ r1_orders_2(sK0,X5,X6) ) )
                      | ~ m1_subset_1(X6,u1_struct_0(sK0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
              & u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2)
              & v2_funct_1(X2) )
            | v23_waybel_0(X2,sK0,sK1) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,
    ( ? [X2] :
        ( ( ? [X3] :
              ( ? [X4] :
                  ( ( ~ r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X2,X4))
                    | ~ r1_orders_2(sK0,X3,X4) )
                  & ( r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X2,X4))
                    | r1_orders_2(sK0,X3,X4) )
                  & m1_subset_1(X4,u1_struct_0(sK0)) )
              & m1_subset_1(X3,u1_struct_0(sK0)) )
          | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2)
          | ~ v2_funct_1(X2)
          | ~ v23_waybel_0(X2,sK0,sK1) )
        & ( ( ! [X5] :
                ( ! [X6] :
                    ( ( ( r1_orders_2(sK0,X5,X6)
                        | ~ r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X2,X5),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X2,X6)) )
                      & ( r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X2,X5),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X2,X6))
                        | ~ r1_orders_2(sK0,X5,X6) ) )
                    | ~ m1_subset_1(X6,u1_struct_0(sK0)) )
                | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
            & u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2)
            & v2_funct_1(X2) )
          | v23_waybel_0(X2,sK0,sK1) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ( ? [X3] :
            ( ? [X4] :
                ( ( ~ r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4))
                  | ~ r1_orders_2(sK0,X3,X4) )
                & ( r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4))
                  | r1_orders_2(sK0,X3,X4) )
                & m1_subset_1(X4,u1_struct_0(sK0)) )
            & m1_subset_1(X3,u1_struct_0(sK0)) )
        | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
        | ~ v2_funct_1(sK2)
        | ~ v23_waybel_0(sK2,sK0,sK1) )
      & ( ( ! [X5] :
              ( ! [X6] :
                  ( ( ( r1_orders_2(sK0,X5,X6)
                      | ~ r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X5),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X6)) )
                    & ( r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X5),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X6))
                      | ~ r1_orders_2(sK0,X5,X6) ) )
                  | ~ m1_subset_1(X6,u1_struct_0(sK0)) )
              | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
          & u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
          & v2_funct_1(sK2) )
        | v23_waybel_0(sK2,sK0,sK1) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ( ~ r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4))
              | ~ r1_orders_2(sK0,X3,X4) )
            & ( r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4))
              | r1_orders_2(sK0,X3,X4) )
            & m1_subset_1(X4,u1_struct_0(sK0)) )
        & m1_subset_1(X3,u1_struct_0(sK0)) )
   => ( ? [X4] :
          ( ( ~ r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4))
            | ~ r1_orders_2(sK0,sK3,X4) )
          & ( r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4))
            | r1_orders_2(sK0,sK3,X4) )
          & m1_subset_1(X4,u1_struct_0(sK0)) )
      & m1_subset_1(sK3,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,
    ( ? [X4] :
        ( ( ~ r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4))
          | ~ r1_orders_2(sK0,sK3,X4) )
        & ( r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4))
          | r1_orders_2(sK0,sK3,X4) )
        & m1_subset_1(X4,u1_struct_0(sK0)) )
   => ( ( ~ r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4))
        | ~ r1_orders_2(sK0,sK3,sK4) )
      & ( r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4))
        | r1_orders_2(sK0,sK3,sK4) )
      & m1_subset_1(sK4,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ? [X4] :
                        ( ( ~ r1_orders_2(X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X4))
                          | ~ r1_orders_2(X0,X3,X4) )
                        & ( r1_orders_2(X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X4))
                          | r1_orders_2(X0,X3,X4) )
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | u1_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                | ~ v2_funct_1(X2)
                | ~ v23_waybel_0(X2,X0,X1) )
              & ( ( ! [X5] :
                      ( ! [X6] :
                          ( ( ( r1_orders_2(X0,X5,X6)
                              | ~ r1_orders_2(X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X5),k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X6)) )
                            & ( r1_orders_2(X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X5),k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X6))
                              | ~ r1_orders_2(X0,X5,X6) ) )
                          | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  & u1_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & v2_funct_1(X2) )
                | v23_waybel_0(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f56])).

fof(f56,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ? [X4] :
                        ( ( ~ r1_orders_2(X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X4))
                          | ~ r1_orders_2(X0,X3,X4) )
                        & ( r1_orders_2(X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X4))
                          | r1_orders_2(X0,X3,X4) )
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | u1_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                | ~ v2_funct_1(X2)
                | ~ v23_waybel_0(X2,X0,X1) )
              & ( ( ! [X3] :
                      ( ! [X4] :
                          ( ( ( r1_orders_2(X0,X3,X4)
                              | ~ r1_orders_2(X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) )
                            & ( r1_orders_2(X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X4))
                              | ~ r1_orders_2(X0,X3,X4) ) )
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & u1_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & v2_funct_1(X2) )
                | v23_waybel_0(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ? [X4] :
                        ( ( ~ r1_orders_2(X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X4))
                          | ~ r1_orders_2(X0,X3,X4) )
                        & ( r1_orders_2(X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X4))
                          | r1_orders_2(X0,X3,X4) )
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | u1_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                | ~ v2_funct_1(X2)
                | ~ v23_waybel_0(X2,X0,X1) )
              & ( ( ! [X3] :
                      ( ! [X4] :
                          ( ( ( r1_orders_2(X0,X3,X4)
                              | ~ r1_orders_2(X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) )
                            & ( r1_orders_2(X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X4))
                              | ~ r1_orders_2(X0,X3,X4) ) )
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & u1_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & v2_funct_1(X2) )
                | v23_waybel_0(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v23_waybel_0(X2,X0,X1)
              <~> ( ! [X3] :
                      ( ! [X4] :
                          ( ( r1_orders_2(X0,X3,X4)
                          <=> r1_orders_2(X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) )
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & u1_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & v2_funct_1(X2) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v23_waybel_0(X2,X0,X1)
              <~> ( ! [X3] :
                      ( ! [X4] :
                          ( ( r1_orders_2(X0,X3,X4)
                          <=> r1_orders_2(X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) )
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & u1_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & v2_funct_1(X2) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( v23_waybel_0(X2,X0,X1)
                <=> ( ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ( r1_orders_2(X0,X3,X4)
                            <=> r1_orders_2(X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) ) ) )
                    & u1_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                    & v2_funct_1(X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v23_waybel_0(X2,X0,X1)
              <=> ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( r1_orders_2(X0,X3,X4)
                          <=> r1_orders_2(X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) ) ) )
                  & u1_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & v2_funct_1(X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_waybel_0)).

fof(f232,plain,(
    spl14_15 ),
    inference(avatar_split_clause,[],[f86,f230])).

fof(f86,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f63])).

fof(f228,plain,(
    ~ spl14_14 ),
    inference(avatar_split_clause,[],[f87,f226])).

fof(f87,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f63])).

fof(f224,plain,(
    spl14_13 ),
    inference(avatar_split_clause,[],[f88,f222])).

fof(f88,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f63])).

fof(f220,plain,(
    spl14_12 ),
    inference(avatar_split_clause,[],[f89,f218])).

fof(f89,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f63])).

fof(f216,plain,(
    spl14_11 ),
    inference(avatar_split_clause,[],[f90,f214])).

fof(f90,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f63])).

fof(f212,plain,(
    spl14_10 ),
    inference(avatar_split_clause,[],[f91,f210])).

fof(f91,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f63])).

fof(f208,plain,
    ( spl14_1
    | spl14_2 ),
    inference(avatar_split_clause,[],[f92,f173,f170])).

fof(f92,plain,
    ( v2_funct_1(sK2)
    | v23_waybel_0(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f63])).

fof(f206,plain,
    ( spl14_1
    | spl14_3 ),
    inference(avatar_split_clause,[],[f93,f176,f170])).

fof(f93,plain,
    ( u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v23_waybel_0(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f63])).

fof(f204,plain,
    ( spl14_1
    | spl14_9 ),
    inference(avatar_split_clause,[],[f94,f202,f170])).

fof(f94,plain,(
    ! [X6,X5] :
      ( r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X5),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X6))
      | ~ r1_orders_2(sK0,X5,X6)
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | v23_waybel_0(sK2,sK0,sK1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f200,plain,
    ( spl14_1
    | spl14_8 ),
    inference(avatar_split_clause,[],[f95,f198,f170])).

fof(f95,plain,(
    ! [X6,X5] :
      ( r1_orders_2(sK0,X5,X6)
      | ~ r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X5),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X6))
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | v23_waybel_0(sK2,sK0,sK1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f195,plain,
    ( ~ spl14_1
    | ~ spl14_2
    | ~ spl14_3
    | spl14_7 ),
    inference(avatar_split_clause,[],[f96,f193,f176,f173,f170])).

fof(f96,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f63])).

fof(f191,plain,
    ( ~ spl14_1
    | ~ spl14_2
    | ~ spl14_3
    | spl14_6 ),
    inference(avatar_split_clause,[],[f97,f189,f176,f173,f170])).

fof(f97,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK0))
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f63])).

fof(f187,plain,
    ( ~ spl14_1
    | ~ spl14_2
    | ~ spl14_3
    | spl14_4
    | spl14_5 ),
    inference(avatar_split_clause,[],[f98,f182,f179,f176,f173,f170])).

fof(f98,plain,
    ( r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4))
    | r1_orders_2(sK0,sK3,sK4)
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f63])).

fof(f184,plain,
    ( ~ spl14_1
    | ~ spl14_2
    | ~ spl14_3
    | ~ spl14_4
    | ~ spl14_5 ),
    inference(avatar_split_clause,[],[f99,f182,f179,f176,f173,f170])).

fof(f99,plain,
    ( ~ r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4))
    | ~ r1_orders_2(sK0,sK3,sK4)
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f63])).

%------------------------------------------------------------------------------
