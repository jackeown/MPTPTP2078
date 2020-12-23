%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow19__t8_yellow19.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:53 EDT 2019

% Result     : Theorem 251.74s
% Output     : Refutation 251.74s
% Verified   : 
% Statistics : Number of formulae       :  291 (8081 expanded)
%              Number of leaves         :   64 (3551 expanded)
%              Depth                    :   19
%              Number of atoms          : 1629 (106330 expanded)
%              Number of equality atoms :  220 (16122 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f46055,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f299,f306,f313,f320,f379,f418,f523,f524,f525,f526,f529,f532,f929,f1186,f1253,f1567,f2803,f2813,f2852,f2898,f3635,f4601,f20606,f24561,f46044])).

fof(f46044,plain,
    ( spl16_12
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_10
    | spl16_15
    | ~ spl16_16
    | spl16_19
    | ~ spl16_20
    | ~ spl16_22
    | ~ spl16_24
    | ~ spl16_54
    | ~ spl16_224
    | ~ spl16_410
    | ~ spl16_972 ),
    inference(avatar_split_clause,[],[f46043,f20595,f4599,f2801,f910,f503,f497,f491,f485,f479,f473,f368,f318,f311,f304,f374])).

fof(f374,plain,
    ( spl16_12
  <=> r2_hidden(sK3,k2_relat_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_12])])).

fof(f304,plain,
    ( spl16_4
  <=> k2_waybel_0(sK0,sK1,sK4) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_4])])).

fof(f311,plain,
    ( spl16_6
  <=> r1_orders_2(sK1,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_6])])).

fof(f318,plain,
    ( spl16_8
  <=> m1_subset_1(sK4,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_8])])).

fof(f368,plain,
    ( spl16_10
  <=> m1_subset_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_10])])).

fof(f473,plain,
    ( spl16_15
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_15])])).

fof(f479,plain,
    ( spl16_16
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_16])])).

fof(f485,plain,
    ( spl16_19
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_19])])).

fof(f491,plain,
    ( spl16_20
  <=> v4_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_20])])).

fof(f497,plain,
    ( spl16_22
  <=> v7_waybel_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_22])])).

fof(f503,plain,
    ( spl16_24
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_24])])).

fof(f910,plain,
    ( spl16_54
  <=> v1_funct_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_54])])).

fof(f2801,plain,
    ( spl16_224
  <=> m1_subset_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_224])])).

fof(f4599,plain,
    ( spl16_410
  <=> ! [X5] :
        ( ~ r2_hidden(X5,u1_struct_0(k5_waybel_9(sK0,sK1,sK2)))
        | r2_hidden(k1_funct_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),X5),k2_relat_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_410])])).

fof(f20595,plain,
    ( spl16_972
  <=> m1_subset_1(sK2,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_972])])).

fof(f46043,plain,
    ( r2_hidden(sK3,k2_relat_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_10
    | ~ spl16_15
    | ~ spl16_16
    | ~ spl16_19
    | ~ spl16_20
    | ~ spl16_22
    | ~ spl16_24
    | ~ spl16_54
    | ~ spl16_224
    | ~ spl16_410
    | ~ spl16_972 ),
    inference(forward_demodulation,[],[f46042,f25074])).

fof(f25074,plain,
    ( k2_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2),sK4) = sK3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_15
    | ~ spl16_16
    | ~ spl16_19
    | ~ spl16_24
    | ~ spl16_224
    | ~ spl16_972 ),
    inference(forward_demodulation,[],[f25062,f305])).

fof(f305,plain,
    ( k2_waybel_0(sK0,sK1,sK4) = sK3
    | ~ spl16_4 ),
    inference(avatar_component_clause,[],[f304])).

fof(f25062,plain,
    ( k2_waybel_0(sK0,sK1,sK4) = k2_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2),sK4)
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_15
    | ~ spl16_16
    | ~ spl16_19
    | ~ spl16_24
    | ~ spl16_224
    | ~ spl16_972 ),
    inference(unit_resulting_resolution,[],[f319,f24771,f732])).

fof(f732,plain,(
    ! [X3] :
      ( k2_waybel_0(sK0,sK1,X3) = k2_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(k5_waybel_9(sK0,sK1,sK2)))
      | ~ m1_subset_1(X3,u1_struct_0(sK1)) ) ),
    inference(global_subsumption,[],[f174,f169,f172,f173,f168,f170,f731])).

fof(f731,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(k5_waybel_9(sK0,sK1,sK2)))
      | k2_waybel_0(sK0,sK1,X3) = k2_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | v2_struct_0(sK1)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(forward_demodulation,[],[f706,f338])).

fof(f338,plain,(
    k5_waybel_9(sK0,sK1,sK2) = k4_waybel_9(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f168,f169,f170,f171,f172,f173,f174,f238])).

fof(f238,plain,(
    ! [X2,X0,X1] :
      ( k5_waybel_9(X0,X1,X2) = k4_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f106])).

fof(f106,plain,(
    ! [X0,X1,X2] :
      ( k5_waybel_9(X0,X1,X2) = k4_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f105])).

fof(f105,plain,(
    ! [X0,X1,X2] :
      ( k5_waybel_9(X0,X1,X2) = k4_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f47])).

fof(f47,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => k5_waybel_9(X0,X1,X2) = k4_waybel_9(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t8_yellow19.p',redefinition_k5_waybel_9)).

fof(f171,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f141])).

fof(f141,plain,
    ( ( ! [X4] :
          ( k2_waybel_0(sK0,sK1,X4) != sK3
          | ~ r1_orders_2(sK1,sK2,X4)
          | ~ m1_subset_1(X4,u1_struct_0(sK1)) )
      | ~ r2_hidden(sK3,k2_relset_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0),u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)))) )
    & ( ( k2_waybel_0(sK0,sK1,sK4) = sK3
        & r1_orders_2(sK1,sK2,sK4)
        & m1_subset_1(sK4,u1_struct_0(sK1)) )
      | r2_hidden(sK3,k2_relset_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0),u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)))) )
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_waybel_0(sK1,sK0)
    & v7_waybel_0(sK1)
    & v4_orders_2(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f135,f140,f139,f138,f137,f136])).

fof(f136,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ! [X4] :
                          ( k2_waybel_0(X0,X1,X4) != X3
                          | ~ r1_orders_2(X1,X2,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                      | ~ r2_hidden(X3,k2_relset_1(u1_struct_0(k5_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k5_waybel_9(X0,X1,X2)))) )
                    & ( ? [X5] :
                          ( k2_waybel_0(X0,X1,X5) = X3
                          & r1_orders_2(X1,X2,X5)
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      | r2_hidden(X3,k2_relset_1(u1_struct_0(k5_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k5_waybel_9(X0,X1,X2)))) ) )
                & m1_subset_1(X2,u1_struct_0(X1)) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( k2_waybel_0(sK0,X1,X4) != X3
                        | ~ r1_orders_2(X1,X2,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ r2_hidden(X3,k2_relset_1(u1_struct_0(k5_waybel_9(sK0,X1,X2)),u1_struct_0(sK0),u1_waybel_0(sK0,k5_waybel_9(sK0,X1,X2)))) )
                  & ( ? [X5] :
                        ( k2_waybel_0(sK0,X1,X5) = X3
                        & r1_orders_2(X1,X2,X5)
                        & m1_subset_1(X5,u1_struct_0(X1)) )
                    | r2_hidden(X3,k2_relset_1(u1_struct_0(k5_waybel_9(sK0,X1,X2)),u1_struct_0(sK0),u1_waybel_0(sK0,k5_waybel_9(sK0,X1,X2)))) ) )
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,sK0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f137,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( k2_waybel_0(X0,X1,X4) != X3
                        | ~ r1_orders_2(X1,X2,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ r2_hidden(X3,k2_relset_1(u1_struct_0(k5_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k5_waybel_9(X0,X1,X2)))) )
                  & ( ? [X5] :
                        ( k2_waybel_0(X0,X1,X5) = X3
                        & r1_orders_2(X1,X2,X5)
                        & m1_subset_1(X5,u1_struct_0(X1)) )
                    | r2_hidden(X3,k2_relset_1(u1_struct_0(k5_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k5_waybel_9(X0,X1,X2)))) ) )
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ! [X4] :
                      ( k2_waybel_0(X0,sK1,X4) != X3
                      | ~ r1_orders_2(sK1,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(sK1)) )
                  | ~ r2_hidden(X3,k2_relset_1(u1_struct_0(k5_waybel_9(X0,sK1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k5_waybel_9(X0,sK1,X2)))) )
                & ( ? [X5] :
                      ( k2_waybel_0(X0,sK1,X5) = X3
                      & r1_orders_2(sK1,X2,X5)
                      & m1_subset_1(X5,u1_struct_0(sK1)) )
                  | r2_hidden(X3,k2_relset_1(u1_struct_0(k5_waybel_9(X0,sK1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k5_waybel_9(X0,sK1,X2)))) ) )
            & m1_subset_1(X2,u1_struct_0(sK1)) )
        & l1_waybel_0(sK1,X0)
        & v7_waybel_0(sK1)
        & v4_orders_2(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f138,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ! [X4] :
                    ( k2_waybel_0(X0,X1,X4) != X3
                    | ~ r1_orders_2(X1,X2,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                | ~ r2_hidden(X3,k2_relset_1(u1_struct_0(k5_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k5_waybel_9(X0,X1,X2)))) )
              & ( ? [X5] :
                    ( k2_waybel_0(X0,X1,X5) = X3
                    & r1_orders_2(X1,X2,X5)
                    & m1_subset_1(X5,u1_struct_0(X1)) )
                | r2_hidden(X3,k2_relset_1(u1_struct_0(k5_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k5_waybel_9(X0,X1,X2)))) ) )
          & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ? [X3] :
            ( ( ! [X4] :
                  ( k2_waybel_0(X0,X1,X4) != X3
                  | ~ r1_orders_2(X1,sK2,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | ~ r2_hidden(X3,k2_relset_1(u1_struct_0(k5_waybel_9(X0,X1,sK2)),u1_struct_0(X0),u1_waybel_0(X0,k5_waybel_9(X0,X1,sK2)))) )
            & ( ? [X5] :
                  ( k2_waybel_0(X0,X1,X5) = X3
                  & r1_orders_2(X1,sK2,X5)
                  & m1_subset_1(X5,u1_struct_0(X1)) )
              | r2_hidden(X3,k2_relset_1(u1_struct_0(k5_waybel_9(X0,X1,sK2)),u1_struct_0(X0),u1_waybel_0(X0,k5_waybel_9(X0,X1,sK2)))) ) )
        & m1_subset_1(sK2,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( k2_waybel_0(X0,X1,X4) != X3
                | ~ r1_orders_2(X1,X2,X4)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            | ~ r2_hidden(X3,k2_relset_1(u1_struct_0(k5_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k5_waybel_9(X0,X1,X2)))) )
          & ( ? [X5] :
                ( k2_waybel_0(X0,X1,X5) = X3
                & r1_orders_2(X1,X2,X5)
                & m1_subset_1(X5,u1_struct_0(X1)) )
            | r2_hidden(X3,k2_relset_1(u1_struct_0(k5_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k5_waybel_9(X0,X1,X2)))) ) )
     => ( ( ! [X4] :
              ( k2_waybel_0(X0,X1,X4) != sK3
              | ~ r1_orders_2(X1,X2,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          | ~ r2_hidden(sK3,k2_relset_1(u1_struct_0(k5_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k5_waybel_9(X0,X1,X2)))) )
        & ( ? [X5] :
              ( k2_waybel_0(X0,X1,X5) = sK3
              & r1_orders_2(X1,X2,X5)
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | r2_hidden(sK3,k2_relset_1(u1_struct_0(k5_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k5_waybel_9(X0,X1,X2)))) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f140,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X5] :
          ( k2_waybel_0(X0,X1,X5) = X3
          & r1_orders_2(X1,X2,X5)
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( k2_waybel_0(X0,X1,sK4) = X3
        & r1_orders_2(X1,X2,sK4)
        & m1_subset_1(sK4,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f135,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( k2_waybel_0(X0,X1,X4) != X3
                        | ~ r1_orders_2(X1,X2,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ r2_hidden(X3,k2_relset_1(u1_struct_0(k5_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k5_waybel_9(X0,X1,X2)))) )
                  & ( ? [X5] :
                        ( k2_waybel_0(X0,X1,X5) = X3
                        & r1_orders_2(X1,X2,X5)
                        & m1_subset_1(X5,u1_struct_0(X1)) )
                    | r2_hidden(X3,k2_relset_1(u1_struct_0(k5_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k5_waybel_9(X0,X1,X2)))) ) )
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f134])).

fof(f134,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( k2_waybel_0(X0,X1,X4) != X3
                        | ~ r1_orders_2(X1,X2,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ r2_hidden(X3,k2_relset_1(u1_struct_0(k5_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k5_waybel_9(X0,X1,X2)))) )
                  & ( ? [X4] :
                        ( k2_waybel_0(X0,X1,X4) = X3
                        & r1_orders_2(X1,X2,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | r2_hidden(X3,k2_relset_1(u1_struct_0(k5_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k5_waybel_9(X0,X1,X2)))) ) )
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f64])).

fof(f64,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( r2_hidden(X3,k2_relset_1(u1_struct_0(k5_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k5_waybel_9(X0,X1,X2))))
                <~> ? [X4] :
                      ( k2_waybel_0(X0,X1,X4) = X3
                      & r1_orders_2(X1,X2,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) ) )
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( r2_hidden(X3,k2_relset_1(u1_struct_0(k5_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k5_waybel_9(X0,X1,X2))))
                <~> ? [X4] :
                      ( k2_waybel_0(X0,X1,X4) = X3
                      & r1_orders_2(X1,X2,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) ) )
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => ! [X3] :
                    ( r2_hidden(X3,k2_relset_1(u1_struct_0(k5_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k5_waybel_9(X0,X1,X2))))
                  <=> ? [X4] :
                        ( k2_waybel_0(X0,X1,X4) = X3
                        & r1_orders_2(X1,X2,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => ! [X3] :
                  ( r2_hidden(X3,k2_relset_1(u1_struct_0(k5_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k5_waybel_9(X0,X1,X2))))
                <=> ? [X4] :
                      ( k2_waybel_0(X0,X1,X4) = X3
                      & r1_orders_2(X1,X2,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t8_yellow19.p',t8_yellow19)).

fof(f706,plain,(
    ! [X3] :
      ( k2_waybel_0(sK0,sK1,X3) = k2_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | v2_struct_0(sK1)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f270,f338])).

fof(f270,plain,(
    ! [X4,X2,X0,X1] :
      ( k2_waybel_0(X0,X1,X4) = k2_waybel_0(X0,k4_waybel_9(X0,X1,X2),X4)
      | ~ m1_subset_1(X4,u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f188])).

fof(f188,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_waybel_0(X0,X1,X3) = k2_waybel_0(X0,k4_waybel_9(X0,X1,X2),X4)
      | X3 != X4
      | ~ m1_subset_1(X4,u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_waybel_0(X0,X1,X3) = k2_waybel_0(X0,k4_waybel_9(X0,X1,X2),X4)
                      | X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(k4_waybel_9(X0,X1,X2))) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_waybel_0(X0,X1,X3) = k2_waybel_0(X0,k4_waybel_9(X0,X1,X2),X4)
                      | X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(k4_waybel_9(X0,X1,X2))) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f51])).

fof(f51,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(k4_waybel_9(X0,X1,X2)))
                     => ( X3 = X4
                       => k2_waybel_0(X0,X1,X3) = k2_waybel_0(X0,k4_waybel_9(X0,X1,X2),X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t8_yellow19.p',t16_waybel_9)).

fof(f170,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f141])).

fof(f168,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f141])).

fof(f173,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f141])).

fof(f172,plain,(
    v7_waybel_0(sK1) ),
    inference(cnf_transformation,[],[f141])).

fof(f169,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f141])).

fof(f174,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f141])).

fof(f24771,plain,
    ( m1_subset_1(sK4,u1_struct_0(k5_waybel_9(sK0,sK1,sK2)))
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_15
    | ~ spl16_16
    | ~ spl16_19
    | ~ spl16_24
    | ~ spl16_224
    | ~ spl16_972 ),
    inference(unit_resulting_resolution,[],[f2802,f24624,f244])).

fof(f244,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f114])).

fof(f114,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f113])).

fof(f113,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f55])).

fof(f55,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t8_yellow19.p',t4_subset)).

fof(f24624,plain,
    ( r2_hidden(sK4,u1_struct_0(k5_waybel_9(sK0,sK1,sK2)))
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_15
    | ~ spl16_16
    | ~ spl16_19
    | ~ spl16_24
    | ~ spl16_972 ),
    inference(forward_demodulation,[],[f24620,f338])).

fof(f24620,plain,
    ( r2_hidden(sK4,u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_15
    | ~ spl16_16
    | ~ spl16_19
    | ~ spl16_24
    | ~ spl16_972 ),
    inference(unit_resulting_resolution,[],[f474,f480,f486,f504,f20596,f312,f342,f343,f319,f275])).

fof(f275,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(X8,u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ r1_orders_2(X1,X2,X8)
      | ~ m1_subset_1(X8,u1_struct_0(X1))
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f274])).

fof(f274,plain,(
    ! [X2,X0,X8,X3,X1] :
      ( r2_hidden(X8,u1_struct_0(X3))
      | ~ r1_orders_2(X1,X2,X8)
      | ~ m1_subset_1(X8,u1_struct_0(X1))
      | k4_waybel_9(X0,X1,X2) != X3
      | ~ l1_waybel_0(X3,X0)
      | ~ v6_waybel_0(X3,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f193])).

fof(f193,plain,(
    ! [X2,X0,X8,X7,X3,X1] :
      ( r2_hidden(X7,u1_struct_0(X3))
      | ~ r1_orders_2(X1,X2,X8)
      | X7 != X8
      | ~ m1_subset_1(X8,u1_struct_0(X1))
      | k4_waybel_9(X0,X1,X2) != X3
      | ~ l1_waybel_0(X3,X0)
      | ~ v6_waybel_0(X3,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f150])).

fof(f150,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k4_waybel_9(X0,X1,X2) = X3
                      | u1_waybel_0(X0,X3) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      | ~ r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      | ( ( ! [X5] :
                              ( ~ r1_orders_2(X1,X2,X5)
                              | sK6(X1,X2,X3) != X5
                              | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                          | ~ r2_hidden(sK6(X1,X2,X3),u1_struct_0(X3)) )
                        & ( ( r1_orders_2(X1,X2,sK7(X1,X2,X3))
                            & sK6(X1,X2,X3) = sK7(X1,X2,X3)
                            & m1_subset_1(sK7(X1,X2,X3),u1_struct_0(X1)) )
                          | r2_hidden(sK6(X1,X2,X3),u1_struct_0(X3)) ) ) )
                    & ( ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                        & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                        & ! [X7] :
                            ( ( r2_hidden(X7,u1_struct_0(X3))
                              | ! [X8] :
                                  ( ~ r1_orders_2(X1,X2,X8)
                                  | X7 != X8
                                  | ~ m1_subset_1(X8,u1_struct_0(X1)) ) )
                            & ( ( r1_orders_2(X1,X2,sK8(X1,X2,X7))
                                & sK8(X1,X2,X7) = X7
                                & m1_subset_1(sK8(X1,X2,X7),u1_struct_0(X1)) )
                              | ~ r2_hidden(X7,u1_struct_0(X3)) ) ) )
                      | k4_waybel_9(X0,X1,X2) != X3 ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f146,f149,f148,f147])).

fof(f147,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r1_orders_2(X1,X2,X5)
                | X4 != X5
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            | ~ r2_hidden(X4,u1_struct_0(X3)) )
          & ( ? [X6] :
                ( r1_orders_2(X1,X2,X6)
                & X4 = X6
                & m1_subset_1(X6,u1_struct_0(X1)) )
            | r2_hidden(X4,u1_struct_0(X3)) ) )
     => ( ( ! [X5] :
              ( ~ r1_orders_2(X1,X2,X5)
              | sK6(X1,X2,X3) != X5
              | ~ m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(sK6(X1,X2,X3),u1_struct_0(X3)) )
        & ( ? [X6] :
              ( r1_orders_2(X1,X2,X6)
              & sK6(X1,X2,X3) = X6
              & m1_subset_1(X6,u1_struct_0(X1)) )
          | r2_hidden(sK6(X1,X2,X3),u1_struct_0(X3)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f148,plain,(
    ! [X4,X3,X2,X1] :
      ( ? [X6] :
          ( r1_orders_2(X1,X2,X6)
          & X4 = X6
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r1_orders_2(X1,X2,sK7(X1,X2,X3))
        & sK7(X1,X2,X3) = X4
        & m1_subset_1(sK7(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f149,plain,(
    ! [X7,X2,X1] :
      ( ? [X9] :
          ( r1_orders_2(X1,X2,X9)
          & X7 = X9
          & m1_subset_1(X9,u1_struct_0(X1)) )
     => ( r1_orders_2(X1,X2,sK8(X1,X2,X7))
        & sK8(X1,X2,X7) = X7
        & m1_subset_1(sK8(X1,X2,X7),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f146,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k4_waybel_9(X0,X1,X2) = X3
                      | u1_waybel_0(X0,X3) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      | ~ r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      | ? [X4] :
                          ( ( ! [X5] :
                                ( ~ r1_orders_2(X1,X2,X5)
                                | X4 != X5
                                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                            | ~ r2_hidden(X4,u1_struct_0(X3)) )
                          & ( ? [X6] :
                                ( r1_orders_2(X1,X2,X6)
                                & X4 = X6
                                & m1_subset_1(X6,u1_struct_0(X1)) )
                            | r2_hidden(X4,u1_struct_0(X3)) ) ) )
                    & ( ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                        & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                        & ! [X7] :
                            ( ( r2_hidden(X7,u1_struct_0(X3))
                              | ! [X8] :
                                  ( ~ r1_orders_2(X1,X2,X8)
                                  | X7 != X8
                                  | ~ m1_subset_1(X8,u1_struct_0(X1)) ) )
                            & ( ? [X9] :
                                  ( r1_orders_2(X1,X2,X9)
                                  & X7 = X9
                                  & m1_subset_1(X9,u1_struct_0(X1)) )
                              | ~ r2_hidden(X7,u1_struct_0(X3)) ) ) )
                      | k4_waybel_9(X0,X1,X2) != X3 ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f145])).

fof(f145,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k4_waybel_9(X0,X1,X2) = X3
                      | u1_waybel_0(X0,X3) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      | ~ r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      | ? [X4] :
                          ( ( ! [X5] :
                                ( ~ r1_orders_2(X1,X2,X5)
                                | X4 != X5
                                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                            | ~ r2_hidden(X4,u1_struct_0(X3)) )
                          & ( ? [X5] :
                                ( r1_orders_2(X1,X2,X5)
                                & X4 = X5
                                & m1_subset_1(X5,u1_struct_0(X1)) )
                            | r2_hidden(X4,u1_struct_0(X3)) ) ) )
                    & ( ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                        & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                        & ! [X4] :
                            ( ( r2_hidden(X4,u1_struct_0(X3))
                              | ! [X5] :
                                  ( ~ r1_orders_2(X1,X2,X5)
                                  | X4 != X5
                                  | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                            & ( ? [X5] :
                                  ( r1_orders_2(X1,X2,X5)
                                  & X4 = X5
                                  & m1_subset_1(X5,u1_struct_0(X1)) )
                              | ~ r2_hidden(X4,u1_struct_0(X3)) ) ) )
                      | k4_waybel_9(X0,X1,X2) != X3 ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f144])).

fof(f144,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k4_waybel_9(X0,X1,X2) = X3
                      | u1_waybel_0(X0,X3) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      | ~ r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      | ? [X4] :
                          ( ( ! [X5] :
                                ( ~ r1_orders_2(X1,X2,X5)
                                | X4 != X5
                                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                            | ~ r2_hidden(X4,u1_struct_0(X3)) )
                          & ( ? [X5] :
                                ( r1_orders_2(X1,X2,X5)
                                & X4 = X5
                                & m1_subset_1(X5,u1_struct_0(X1)) )
                            | r2_hidden(X4,u1_struct_0(X3)) ) ) )
                    & ( ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                        & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                        & ! [X4] :
                            ( ( r2_hidden(X4,u1_struct_0(X3))
                              | ! [X5] :
                                  ( ~ r1_orders_2(X1,X2,X5)
                                  | X4 != X5
                                  | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                            & ( ? [X5] :
                                  ( r1_orders_2(X1,X2,X5)
                                  & X4 = X5
                                  & m1_subset_1(X5,u1_struct_0(X1)) )
                              | ~ r2_hidden(X4,u1_struct_0(X3)) ) ) )
                      | k4_waybel_9(X0,X1,X2) != X3 ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k4_waybel_9(X0,X1,X2) = X3
                  <=> ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      & ! [X4] :
                          ( r2_hidden(X4,u1_struct_0(X3))
                        <=> ? [X5] :
                              ( r1_orders_2(X1,X2,X5)
                              & X4 = X5
                              & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k4_waybel_9(X0,X1,X2) = X3
                  <=> ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      & ! [X4] :
                          ( r2_hidden(X4,u1_struct_0(X3))
                        <=> ? [X5] :
                              ( r1_orders_2(X1,X2,X5)
                              & X4 = X5
                              & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => ! [X3] :
                  ( ( l1_waybel_0(X3,X0)
                    & v6_waybel_0(X3,X0) )
                 => ( k4_waybel_9(X0,X1,X2) = X3
                  <=> ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      & ! [X4] :
                          ( r2_hidden(X4,u1_struct_0(X3))
                        <=> ? [X5] :
                              ( r1_orders_2(X1,X2,X5)
                              & X4 = X5
                              & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t8_yellow19.p',d7_waybel_9)).

fof(f343,plain,(
    l1_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0) ),
    inference(unit_resulting_resolution,[],[f168,f169,f170,f173,f174,f243])).

fof(f243,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f112])).

fof(f112,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f111])).

fof(f111,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t8_yellow19.p',dt_k4_waybel_9)).

fof(f342,plain,(
    v6_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0) ),
    inference(unit_resulting_resolution,[],[f168,f169,f170,f173,f174,f242])).

fof(f242,plain,(
    ! [X2,X0,X1] :
      ( v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f112])).

fof(f312,plain,
    ( r1_orders_2(sK1,sK2,sK4)
    | ~ spl16_6 ),
    inference(avatar_component_clause,[],[f311])).

fof(f20596,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl16_972 ),
    inference(avatar_component_clause,[],[f20595])).

fof(f504,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ spl16_24 ),
    inference(avatar_component_clause,[],[f503])).

fof(f486,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl16_19 ),
    inference(avatar_component_clause,[],[f485])).

fof(f480,plain,
    ( l1_struct_0(sK0)
    | ~ spl16_16 ),
    inference(avatar_component_clause,[],[f479])).

fof(f474,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl16_15 ),
    inference(avatar_component_clause,[],[f473])).

fof(f2802,plain,
    ( m1_subset_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2))))
    | ~ spl16_224 ),
    inference(avatar_component_clause,[],[f2801])).

fof(f319,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ spl16_8 ),
    inference(avatar_component_clause,[],[f318])).

fof(f46042,plain,
    ( r2_hidden(k2_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2),sK4),k2_relat_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2))))
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_10
    | ~ spl16_15
    | ~ spl16_16
    | ~ spl16_19
    | ~ spl16_20
    | ~ spl16_22
    | ~ spl16_24
    | ~ spl16_54
    | ~ spl16_410
    | ~ spl16_972 ),
    inference(forward_demodulation,[],[f46028,f2031])).

fof(f2031,plain,
    ( k2_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2),sK4) = k1_funct_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),sK4)
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_10
    | ~ spl16_15
    | ~ spl16_16
    | ~ spl16_19
    | ~ spl16_20
    | ~ spl16_22
    | ~ spl16_24
    | ~ spl16_54 ),
    inference(forward_demodulation,[],[f2023,f1349])).

fof(f1349,plain,
    ( k2_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2),sK4) = k3_funct_2(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0),u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),sK4)
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_15
    | ~ spl16_16
    | ~ spl16_19
    | ~ spl16_20
    | ~ spl16_22
    | ~ spl16_24 ),
    inference(unit_resulting_resolution,[],[f474,f480,f578,f425,f1281,f189])).

fof(f189,plain,(
    ! [X2,X0,X1] :
      ( k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2)
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f75])).

fof(f75,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2)
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t8_yellow19.p',d8_waybel_0)).

fof(f1281,plain,
    ( m1_subset_1(sK4,u1_struct_0(k5_waybel_9(sK0,sK1,sK2)))
    | ~ spl16_6
    | ~ spl16_8 ),
    inference(unit_resulting_resolution,[],[f424,f213])).

fof(f213,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f52])).

fof(f52,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t8_yellow19.p',t1_subset)).

fof(f424,plain,
    ( r2_hidden(sK4,u1_struct_0(k5_waybel_9(sK0,sK1,sK2)))
    | ~ spl16_6
    | ~ spl16_8 ),
    inference(forward_demodulation,[],[f403,f338])).

fof(f403,plain,
    ( r2_hidden(sK4,u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | ~ spl16_6
    | ~ spl16_8 ),
    inference(unit_resulting_resolution,[],[f168,f169,f170,f173,f312,f319,f174,f342,f343,f275])).

fof(f425,plain,(
    l1_waybel_0(k5_waybel_9(sK0,sK1,sK2),sK0) ),
    inference(global_subsumption,[],[f174,f173,f172,f171,f170,f169,f168,f411])).

fof(f411,plain,
    ( l1_waybel_0(k5_waybel_9(sK0,sK1,sK2),sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f343,f238])).

fof(f578,plain,
    ( ~ v2_struct_0(k5_waybel_9(sK0,sK1,sK2))
    | ~ spl16_15
    | ~ spl16_16
    | ~ spl16_19
    | ~ spl16_20
    | ~ spl16_22
    | ~ spl16_24 ),
    inference(unit_resulting_resolution,[],[f474,f480,f486,f492,f498,f340,f504,f215])).

fof(f215,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
          | ~ m2_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
          | ~ m2_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_yellow_6(X2,X0,X1)
         => ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t8_yellow19.p',dt_m2_yellow_6)).

fof(f340,plain,(
    m2_yellow_6(k5_waybel_9(sK0,sK1,sK2),sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f168,f169,f170,f171,f172,f173,f174,f240])).

fof(f240,plain,(
    ! [X2,X0,X1] :
      ( m2_yellow_6(k5_waybel_9(X0,X1,X2),X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f108])).

fof(f108,plain,(
    ! [X0,X1,X2] :
      ( ( m2_yellow_6(k5_waybel_9(X0,X1,X2),X0,X1)
        & v6_waybel_0(k5_waybel_9(X0,X1,X2),X0) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f107])).

fof(f107,plain,(
    ! [X0,X1,X2] :
      ( ( m2_yellow_6(k5_waybel_9(X0,X1,X2),X0,X1)
        & v6_waybel_0(k5_waybel_9(X0,X1,X2),X0) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( m2_yellow_6(k5_waybel_9(X0,X1,X2),X0,X1)
        & v6_waybel_0(k5_waybel_9(X0,X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t8_yellow19.p',dt_k5_waybel_9)).

fof(f498,plain,
    ( v7_waybel_0(sK1)
    | ~ spl16_22 ),
    inference(avatar_component_clause,[],[f497])).

fof(f492,plain,
    ( v4_orders_2(sK1)
    | ~ spl16_20 ),
    inference(avatar_component_clause,[],[f491])).

fof(f2023,plain,
    ( k1_funct_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),sK4) = k3_funct_2(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0),u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),sK4)
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_10
    | ~ spl16_15
    | ~ spl16_16
    | ~ spl16_19
    | ~ spl16_20
    | ~ spl16_22
    | ~ spl16_24
    | ~ spl16_54 ),
    inference(unit_resulting_resolution,[],[f692,f1281,f911,f369,f419,f247])).

fof(f247,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f119])).

fof(f119,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f118])).

fof(f118,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f46])).

fof(f46,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t8_yellow19.p',redefinition_k3_funct_2)).

fof(f419,plain,(
    v1_funct_2(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f408,f338])).

fof(f408,plain,(
    v1_funct_2(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f169,f343,f221])).

fof(f221,plain,(
    ! [X0,X1] :
      ( v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t8_yellow19.p',dt_u1_waybel_0)).

fof(f369,plain,
    ( m1_subset_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0))))
    | ~ spl16_10 ),
    inference(avatar_component_clause,[],[f368])).

fof(f911,plain,
    ( v1_funct_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)))
    | ~ spl16_54 ),
    inference(avatar_component_clause,[],[f910])).

fof(f692,plain,
    ( ~ v1_xboole_0(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)))
    | ~ spl16_15
    | ~ spl16_16
    | ~ spl16_19
    | ~ spl16_20
    | ~ spl16_22
    | ~ spl16_24 ),
    inference(unit_resulting_resolution,[],[f578,f628,f187])).

fof(f187,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f61])).

fof(f61,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t8_yellow19.p',fc2_struct_0)).

fof(f628,plain,(
    l1_struct_0(k5_waybel_9(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f421,f181])).

fof(f181,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t8_yellow19.p',dt_l1_orders_2)).

fof(f421,plain,(
    l1_orders_2(k5_waybel_9(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f406,f338])).

fof(f406,plain,(
    l1_orders_2(k4_waybel_9(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f169,f343,f183])).

fof(f183,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t8_yellow19.p',dt_l1_waybel_0)).

fof(f46028,plain,
    ( r2_hidden(k1_funct_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),sK4),k2_relat_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2))))
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_15
    | ~ spl16_16
    | ~ spl16_19
    | ~ spl16_24
    | ~ spl16_410
    | ~ spl16_972 ),
    inference(unit_resulting_resolution,[],[f24624,f4600])).

fof(f4600,plain,
    ( ! [X5] :
        ( r2_hidden(k1_funct_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),X5),k2_relat_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2))))
        | ~ r2_hidden(X5,u1_struct_0(k5_waybel_9(sK0,sK1,sK2))) )
    | ~ spl16_410 ),
    inference(avatar_component_clause,[],[f4599])).

fof(f24561,plain,
    ( ~ spl16_2
    | ~ spl16_10
    | ~ spl16_12
    | spl16_15
    | ~ spl16_16
    | spl16_19
    | ~ spl16_20
    | ~ spl16_22
    | ~ spl16_24
    | ~ spl16_52
    | ~ spl16_54
    | ~ spl16_222
    | ~ spl16_224
    | ~ spl16_228
    | spl16_231
    | ~ spl16_278 ),
    inference(avatar_contradiction_clause,[],[f24560])).

fof(f24560,plain,
    ( $false
    | ~ spl16_2
    | ~ spl16_10
    | ~ spl16_12
    | ~ spl16_15
    | ~ spl16_16
    | ~ spl16_19
    | ~ spl16_20
    | ~ spl16_22
    | ~ spl16_24
    | ~ spl16_52
    | ~ spl16_54
    | ~ spl16_222
    | ~ spl16_224
    | ~ spl16_228
    | ~ spl16_231
    | ~ spl16_278 ),
    inference(subsumption_resolution,[],[f17273,f24559])).

fof(f24559,plain,
    ( k2_waybel_0(sK0,sK1,sK11(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),sK3)) = sK3
    | ~ spl16_10
    | ~ spl16_12
    | ~ spl16_15
    | ~ spl16_16
    | ~ spl16_19
    | ~ spl16_20
    | ~ spl16_22
    | ~ spl16_24
    | ~ spl16_52
    | ~ spl16_54
    | ~ spl16_222
    | ~ spl16_224
    | ~ spl16_228
    | ~ spl16_231
    | ~ spl16_278 ),
    inference(forward_demodulation,[],[f24546,f24558])).

fof(f24558,plain,
    ( k2_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2),sK11(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),sK3)) = sK3
    | ~ spl16_10
    | ~ spl16_12
    | ~ spl16_15
    | ~ spl16_16
    | ~ spl16_19
    | ~ spl16_20
    | ~ spl16_22
    | ~ spl16_24
    | ~ spl16_52
    | ~ spl16_54
    | ~ spl16_222
    | ~ spl16_224
    | ~ spl16_228
    | ~ spl16_231
    | ~ spl16_278 ),
    inference(forward_demodulation,[],[f24547,f24557])).

fof(f24557,plain,
    ( k3_funct_2(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0),u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),sK11(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),sK3)) = sK3
    | ~ spl16_10
    | ~ spl16_12
    | ~ spl16_15
    | ~ spl16_16
    | ~ spl16_19
    | ~ spl16_20
    | ~ spl16_22
    | ~ spl16_24
    | ~ spl16_52
    | ~ spl16_54
    | ~ spl16_222
    | ~ spl16_224
    | ~ spl16_228 ),
    inference(forward_demodulation,[],[f24554,f3063])).

fof(f3063,plain,
    ( k1_funct_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),sK11(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),sK3)) = sK3
    | ~ spl16_12
    | ~ spl16_52
    | ~ spl16_54 ),
    inference(unit_resulting_resolution,[],[f905,f911,f375,f281])).

fof(f281,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK11(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f201])).

fof(f201,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK11(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f156])).

fof(f156,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK9(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK9(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK10(X0,X1)) = sK9(X0,X1)
                  & r2_hidden(sK10(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK9(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK11(X0,X5)) = X5
                    & r2_hidden(sK11(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f152,f155,f154,f153])).

fof(f153,plain,(
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
              ( k1_funct_1(X0,X3) != sK9(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK9(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK9(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK9(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f154,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK10(X0,X1)) = X2
        & r2_hidden(sK10(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f155,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK11(X0,X5)) = X5
        & r2_hidden(sK11(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f152,plain,(
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
    inference(rectify,[],[f151])).

fof(f151,plain,(
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
    inference(nnf_transformation,[],[f80])).

fof(f80,plain,(
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
    inference(flattening,[],[f79])).

fof(f79,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/yellow19__t8_yellow19.p',d5_funct_1)).

fof(f375,plain,
    ( r2_hidden(sK3,k2_relat_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2))))
    | ~ spl16_12 ),
    inference(avatar_component_clause,[],[f374])).

fof(f905,plain,
    ( v1_relat_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)))
    | ~ spl16_52 ),
    inference(avatar_component_clause,[],[f904])).

fof(f904,plain,
    ( spl16_52
  <=> v1_relat_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_52])])).

fof(f24554,plain,
    ( k1_funct_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),sK11(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),sK3)) = k3_funct_2(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0),u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),sK11(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),sK3))
    | ~ spl16_10
    | ~ spl16_12
    | ~ spl16_15
    | ~ spl16_16
    | ~ spl16_19
    | ~ spl16_20
    | ~ spl16_22
    | ~ spl16_24
    | ~ spl16_52
    | ~ spl16_54
    | ~ spl16_222
    | ~ spl16_224
    | ~ spl16_228 ),
    inference(unit_resulting_resolution,[],[f692,f911,f2793,f369,f4810,f247])).

fof(f4810,plain,
    ( m1_subset_1(sK11(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),sK3),u1_struct_0(k5_waybel_9(sK0,sK1,sK2)))
    | ~ spl16_12
    | ~ spl16_52
    | ~ spl16_54
    | ~ spl16_224
    | ~ spl16_228 ),
    inference(unit_resulting_resolution,[],[f2802,f3074,f244])).

fof(f3074,plain,
    ( r2_hidden(sK11(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),sK3),u1_struct_0(k5_waybel_9(sK0,sK1,sK2)))
    | ~ spl16_12
    | ~ spl16_52
    | ~ spl16_54
    | ~ spl16_228 ),
    inference(forward_demodulation,[],[f3062,f2850])).

fof(f2850,plain,
    ( u1_struct_0(k5_waybel_9(sK0,sK1,sK2)) = k1_relat_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)))
    | ~ spl16_228 ),
    inference(avatar_component_clause,[],[f2849])).

fof(f2849,plain,
    ( spl16_228
  <=> u1_struct_0(k5_waybel_9(sK0,sK1,sK2)) = k1_relat_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_228])])).

fof(f3062,plain,
    ( r2_hidden(sK11(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),sK3),k1_relat_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2))))
    | ~ spl16_12
    | ~ spl16_52
    | ~ spl16_54 ),
    inference(unit_resulting_resolution,[],[f905,f911,f375,f282])).

fof(f282,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK11(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f200])).

fof(f200,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK11(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f156])).

fof(f2793,plain,
    ( v1_funct_2(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0))
    | ~ spl16_222 ),
    inference(avatar_component_clause,[],[f2792])).

fof(f2792,plain,
    ( spl16_222
  <=> v1_funct_2(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_222])])).

fof(f24547,plain,
    ( k2_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2),sK11(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),sK3)) = k3_funct_2(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0),u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),sK11(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),sK3))
    | ~ spl16_12
    | ~ spl16_15
    | ~ spl16_16
    | ~ spl16_52
    | ~ spl16_54
    | ~ spl16_224
    | ~ spl16_228
    | ~ spl16_231
    | ~ spl16_278 ),
    inference(unit_resulting_resolution,[],[f474,f480,f2888,f3613,f4810,f189])).

fof(f3613,plain,
    ( l1_waybel_0(k5_waybel_9(sK0,sK1,sK2),sK0)
    | ~ spl16_278 ),
    inference(avatar_component_clause,[],[f3612])).

fof(f3612,plain,
    ( spl16_278
  <=> l1_waybel_0(k5_waybel_9(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_278])])).

fof(f2888,plain,
    ( ~ v2_struct_0(k5_waybel_9(sK0,sK1,sK2))
    | ~ spl16_231 ),
    inference(avatar_component_clause,[],[f2887])).

fof(f2887,plain,
    ( spl16_231
  <=> ~ v2_struct_0(k5_waybel_9(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_231])])).

fof(f24546,plain,
    ( k2_waybel_0(sK0,sK1,sK11(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),sK3)) = k2_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2),sK11(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),sK3))
    | ~ spl16_12
    | ~ spl16_52
    | ~ spl16_54
    | ~ spl16_224
    | ~ spl16_228 ),
    inference(unit_resulting_resolution,[],[f4816,f4810,f732])).

fof(f4816,plain,
    ( m1_subset_1(sK11(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),sK3),u1_struct_0(sK1))
    | ~ spl16_12
    | ~ spl16_52
    | ~ spl16_54
    | ~ spl16_228 ),
    inference(forward_demodulation,[],[f4803,f4805])).

fof(f4805,plain,
    ( sK8(sK1,sK2,sK11(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),sK3)) = sK11(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),sK3)
    | ~ spl16_12
    | ~ spl16_52
    | ~ spl16_54
    | ~ spl16_228 ),
    inference(unit_resulting_resolution,[],[f3074,f750])).

fof(f750,plain,(
    ! [X12] :
      ( ~ r2_hidden(X12,u1_struct_0(k5_waybel_9(sK0,sK1,sK2)))
      | sK8(sK1,sK2,X12) = X12 ) ),
    inference(global_subsumption,[],[f174,f339,f425,f169,f173,f168,f170,f749])).

fof(f749,plain,(
    ! [X12] :
      ( ~ v6_waybel_0(k5_waybel_9(sK0,sK1,sK2),sK0)
      | ~ l1_waybel_0(k5_waybel_9(sK0,sK1,sK2),sK0)
      | ~ r2_hidden(X12,u1_struct_0(k5_waybel_9(sK0,sK1,sK2)))
      | sK8(sK1,sK2,X12) = X12
      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(forward_demodulation,[],[f748,f338])).

fof(f748,plain,(
    ! [X12] :
      ( ~ l1_waybel_0(k5_waybel_9(sK0,sK1,sK2),sK0)
      | ~ r2_hidden(X12,u1_struct_0(k5_waybel_9(sK0,sK1,sK2)))
      | sK8(sK1,sK2,X12) = X12
      | ~ v6_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0)
      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(forward_demodulation,[],[f721,f338])).

fof(f721,plain,(
    ! [X12] :
      ( ~ r2_hidden(X12,u1_struct_0(k5_waybel_9(sK0,sK1,sK2)))
      | sK8(sK1,sK2,X12) = X12
      | ~ l1_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0)
      | ~ v6_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0)
      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f277,f338])).

fof(f277,plain,(
    ! [X2,X0,X7,X1] :
      ( sK8(X1,X2,X7) = X7
      | ~ r2_hidden(X7,u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f191])).

fof(f191,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( sK8(X1,X2,X7) = X7
      | ~ r2_hidden(X7,u1_struct_0(X3))
      | k4_waybel_9(X0,X1,X2) != X3
      | ~ l1_waybel_0(X3,X0)
      | ~ v6_waybel_0(X3,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f150])).

fof(f339,plain,(
    v6_waybel_0(k5_waybel_9(sK0,sK1,sK2),sK0) ),
    inference(unit_resulting_resolution,[],[f168,f169,f170,f171,f172,f173,f174,f239])).

fof(f239,plain,(
    ! [X2,X0,X1] :
      ( v6_waybel_0(k5_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f108])).

fof(f4803,plain,
    ( m1_subset_1(sK8(sK1,sK2,sK11(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),sK3)),u1_struct_0(sK1))
    | ~ spl16_12
    | ~ spl16_52
    | ~ spl16_54
    | ~ spl16_228 ),
    inference(unit_resulting_resolution,[],[f3074,f755])).

fof(f755,plain,(
    ! [X15] :
      ( ~ r2_hidden(X15,u1_struct_0(k5_waybel_9(sK0,sK1,sK2)))
      | m1_subset_1(sK8(sK1,sK2,X15),u1_struct_0(sK1)) ) ),
    inference(global_subsumption,[],[f174,f339,f425,f169,f173,f168,f170,f754])).

fof(f754,plain,(
    ! [X15] :
      ( ~ v6_waybel_0(k5_waybel_9(sK0,sK1,sK2),sK0)
      | ~ l1_waybel_0(k5_waybel_9(sK0,sK1,sK2),sK0)
      | ~ r2_hidden(X15,u1_struct_0(k5_waybel_9(sK0,sK1,sK2)))
      | m1_subset_1(sK8(sK1,sK2,X15),u1_struct_0(sK1))
      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(forward_demodulation,[],[f753,f338])).

fof(f753,plain,(
    ! [X15] :
      ( ~ l1_waybel_0(k5_waybel_9(sK0,sK1,sK2),sK0)
      | ~ r2_hidden(X15,u1_struct_0(k5_waybel_9(sK0,sK1,sK2)))
      | m1_subset_1(sK8(sK1,sK2,X15),u1_struct_0(sK1))
      | ~ v6_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0)
      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(forward_demodulation,[],[f724,f338])).

fof(f724,plain,(
    ! [X15] :
      ( ~ r2_hidden(X15,u1_struct_0(k5_waybel_9(sK0,sK1,sK2)))
      | m1_subset_1(sK8(sK1,sK2,X15),u1_struct_0(sK1))
      | ~ l1_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0)
      | ~ v6_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0)
      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f278,f338])).

fof(f278,plain,(
    ! [X2,X0,X7,X1] :
      ( m1_subset_1(sK8(X1,X2,X7),u1_struct_0(X1))
      | ~ r2_hidden(X7,u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f190])).

fof(f190,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( m1_subset_1(sK8(X1,X2,X7),u1_struct_0(X1))
      | ~ r2_hidden(X7,u1_struct_0(X3))
      | k4_waybel_9(X0,X1,X2) != X3
      | ~ l1_waybel_0(X3,X0)
      | ~ v6_waybel_0(X3,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f150])).

fof(f17273,plain,
    ( k2_waybel_0(sK0,sK1,sK11(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),sK3)) != sK3
    | ~ spl16_2
    | ~ spl16_12
    | ~ spl16_52
    | ~ spl16_54
    | ~ spl16_228 ),
    inference(unit_resulting_resolution,[],[f4815,f4816,f298])).

fof(f298,plain,
    ( ! [X4] :
        ( k2_waybel_0(sK0,sK1,X4) != sK3
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,sK2,X4) )
    | ~ spl16_2 ),
    inference(avatar_component_clause,[],[f297])).

fof(f297,plain,
    ( spl16_2
  <=> ! [X4] :
        ( k2_waybel_0(sK0,sK1,X4) != sK3
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,sK2,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_2])])).

fof(f4815,plain,
    ( r1_orders_2(sK1,sK2,sK11(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),sK3))
    | ~ spl16_12
    | ~ spl16_52
    | ~ spl16_54
    | ~ spl16_228 ),
    inference(forward_demodulation,[],[f4804,f4805])).

fof(f4804,plain,
    ( r1_orders_2(sK1,sK2,sK8(sK1,sK2,sK11(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),sK3)))
    | ~ spl16_12
    | ~ spl16_52
    | ~ spl16_54
    | ~ spl16_228 ),
    inference(unit_resulting_resolution,[],[f3074,f745])).

fof(f745,plain,(
    ! [X9] :
      ( ~ r2_hidden(X9,u1_struct_0(k5_waybel_9(sK0,sK1,sK2)))
      | r1_orders_2(sK1,sK2,sK8(sK1,sK2,X9)) ) ),
    inference(global_subsumption,[],[f174,f339,f425,f169,f173,f168,f170,f744])).

fof(f744,plain,(
    ! [X9] :
      ( ~ v6_waybel_0(k5_waybel_9(sK0,sK1,sK2),sK0)
      | ~ l1_waybel_0(k5_waybel_9(sK0,sK1,sK2),sK0)
      | ~ r2_hidden(X9,u1_struct_0(k5_waybel_9(sK0,sK1,sK2)))
      | r1_orders_2(sK1,sK2,sK8(sK1,sK2,X9))
      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(forward_demodulation,[],[f743,f338])).

fof(f743,plain,(
    ! [X9] :
      ( ~ l1_waybel_0(k5_waybel_9(sK0,sK1,sK2),sK0)
      | ~ r2_hidden(X9,u1_struct_0(k5_waybel_9(sK0,sK1,sK2)))
      | r1_orders_2(sK1,sK2,sK8(sK1,sK2,X9))
      | ~ v6_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0)
      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(forward_demodulation,[],[f718,f338])).

fof(f718,plain,(
    ! [X9] :
      ( ~ r2_hidden(X9,u1_struct_0(k5_waybel_9(sK0,sK1,sK2)))
      | r1_orders_2(sK1,sK2,sK8(sK1,sK2,X9))
      | ~ l1_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0)
      | ~ v6_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0)
      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f276,f338])).

fof(f276,plain,(
    ! [X2,X0,X7,X1] :
      ( r1_orders_2(X1,X2,sK8(X1,X2,X7))
      | ~ r2_hidden(X7,u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f192])).

fof(f192,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( r1_orders_2(X1,X2,sK8(X1,X2,X7))
      | ~ r2_hidden(X7,u1_struct_0(X3))
      | k4_waybel_9(X0,X1,X2) != X3
      | ~ l1_waybel_0(X3,X0)
      | ~ v6_waybel_0(X3,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f150])).

fof(f20606,plain,(
    spl16_972 ),
    inference(avatar_split_clause,[],[f174,f20595])).

fof(f4601,plain,
    ( ~ spl16_53
    | ~ spl16_55
    | spl16_410
    | ~ spl16_228 ),
    inference(avatar_split_clause,[],[f4583,f2849,f4599,f913,f907])).

fof(f907,plain,
    ( spl16_53
  <=> ~ v1_relat_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_53])])).

fof(f913,plain,
    ( spl16_55
  <=> ~ v1_funct_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_55])])).

fof(f4583,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,u1_struct_0(k5_waybel_9(sK0,sK1,sK2)))
        | r2_hidden(k1_funct_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),X5),k2_relat_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2))))
        | ~ v1_funct_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)))
        | ~ v1_relat_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2))) )
    | ~ spl16_228 ),
    inference(superposition,[],[f280,f2850])).

fof(f280,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f279])).

fof(f279,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f202])).

fof(f202,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f156])).

fof(f3635,plain,(
    spl16_278 ),
    inference(avatar_split_clause,[],[f425,f3612])).

fof(f2898,plain,
    ( ~ spl16_231
    | spl16_15
    | ~ spl16_16
    | spl16_19
    | ~ spl16_20
    | ~ spl16_22
    | ~ spl16_24 ),
    inference(avatar_split_clause,[],[f578,f503,f497,f491,f485,f479,f473,f2887])).

fof(f2852,plain,
    ( ~ spl16_11
    | spl16_92
    | ~ spl16_223
    | spl16_228
    | ~ spl16_10 ),
    inference(avatar_split_clause,[],[f2842,f368,f2849,f2795,f1458,f371])).

fof(f371,plain,
    ( spl16_11
  <=> ~ m1_subset_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_11])])).

fof(f1458,plain,
    ( spl16_92
  <=> u1_struct_0(sK0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_92])])).

fof(f2795,plain,
    ( spl16_223
  <=> ~ v1_funct_2(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_223])])).

fof(f2842,plain,
    ( u1_struct_0(k5_waybel_9(sK0,sK1,sK2)) = k1_relat_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)))
    | ~ v1_funct_2(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0))
    | u1_struct_0(sK0) = o_0_0_xboole_0
    | ~ m1_subset_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0))))
    | ~ spl16_10 ),
    inference(superposition,[],[f269,f1177])).

fof(f1177,plain,
    ( k1_relset_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0),u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2))) = k1_relat_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)))
    | ~ spl16_10 ),
    inference(unit_resulting_resolution,[],[f369,f229])).

fof(f229,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f100])).

fof(f100,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f42,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t8_yellow19.p',redefinition_k1_relset_1)).

fof(f269,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | o_0_0_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_unfolding,[],[f232,f180])).

fof(f180,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t8_yellow19.p',d2_xboole_0)).

fof(f232,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f162])).

fof(f162,plain,(
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
    inference(nnf_transformation,[],[f104])).

fof(f104,plain,(
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
    inference(flattening,[],[f103])).

fof(f103,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/yellow19__t8_yellow19.p',d1_funct_2)).

fof(f2813,plain,(
    spl16_222 ),
    inference(avatar_split_clause,[],[f419,f2792])).

fof(f2803,plain,
    ( ~ spl16_11
    | spl16_92
    | ~ spl16_223
    | spl16_224
    | ~ spl16_10 ),
    inference(avatar_split_clause,[],[f2788,f368,f2801,f2795,f1458,f371])).

fof(f2788,plain,
    ( m1_subset_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2))))
    | ~ v1_funct_2(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0))
    | u1_struct_0(sK0) = o_0_0_xboole_0
    | ~ m1_subset_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0))))
    | ~ spl16_10 ),
    inference(superposition,[],[f1178,f269])).

fof(f1178,plain,
    ( m1_subset_1(k1_relset_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0),u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2))),k1_zfmisc_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2))))
    | ~ spl16_10 ),
    inference(unit_resulting_resolution,[],[f369,f230])).

fof(f230,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f101])).

fof(f101,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t8_yellow19.p',dt_k1_relset_1)).

fof(f1567,plain,(
    ~ spl16_92 ),
    inference(avatar_contradiction_clause,[],[f1566])).

fof(f1566,plain,
    ( $false
    | ~ spl16_92 ),
    inference(subsumption_resolution,[],[f179,f1468])).

fof(f1468,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl16_92 ),
    inference(superposition,[],[f322,f1459])).

fof(f1459,plain,
    ( u1_struct_0(sK0) = o_0_0_xboole_0
    | ~ spl16_92 ),
    inference(avatar_component_clause,[],[f1458])).

fof(f322,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f168,f169,f187])).

fof(f179,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t8_yellow19.p',dt_o_0_0_xboole_0)).

fof(f1253,plain,
    ( spl16_12
    | ~ spl16_0
    | ~ spl16_10 ),
    inference(avatar_split_clause,[],[f1187,f368,f291,f374])).

fof(f291,plain,
    ( spl16_0
  <=> r2_hidden(sK3,k2_relset_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0),u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_0])])).

fof(f1187,plain,
    ( r2_hidden(sK3,k2_relat_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2))))
    | ~ spl16_0
    | ~ spl16_10 ),
    inference(forward_demodulation,[],[f292,f1176])).

fof(f1176,plain,
    ( k2_relset_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0),u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2))) = k2_relat_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)))
    | ~ spl16_10 ),
    inference(unit_resulting_resolution,[],[f369,f228])).

fof(f228,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f99])).

fof(f99,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f45])).

fof(f45,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t8_yellow19.p',redefinition_k2_relset_1)).

fof(f292,plain,
    ( r2_hidden(sK3,k2_relset_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0),u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2))))
    | ~ spl16_0 ),
    inference(avatar_component_clause,[],[f291])).

fof(f1186,plain,
    ( spl16_52
    | ~ spl16_10 ),
    inference(avatar_split_clause,[],[f1185,f368,f904])).

fof(f1185,plain,
    ( v1_relat_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)))
    | ~ spl16_10 ),
    inference(unit_resulting_resolution,[],[f207,f369,f186])).

fof(f186,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f60])).

fof(f60,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t8_yellow19.p',cc2_relat_1)).

fof(f207,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t8_yellow19.p',fc6_relat_1)).

fof(f929,plain,(
    spl16_54 ),
    inference(avatar_split_clause,[],[f420,f910])).

fof(f420,plain,(
    v1_funct_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2))) ),
    inference(forward_demodulation,[],[f407,f338])).

fof(f407,plain,(
    v1_funct_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))) ),
    inference(unit_resulting_resolution,[],[f169,f343,f220])).

fof(f220,plain,(
    ! [X0,X1] :
      ( v1_funct_1(u1_waybel_0(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f532,plain,(
    ~ spl16_19 ),
    inference(avatar_split_clause,[],[f170,f485])).

fof(f529,plain,(
    ~ spl16_15 ),
    inference(avatar_split_clause,[],[f168,f473])).

fof(f526,plain,(
    spl16_24 ),
    inference(avatar_split_clause,[],[f173,f503])).

fof(f525,plain,(
    spl16_22 ),
    inference(avatar_split_clause,[],[f172,f497])).

fof(f524,plain,(
    spl16_20 ),
    inference(avatar_split_clause,[],[f171,f491])).

fof(f523,plain,(
    spl16_16 ),
    inference(avatar_split_clause,[],[f169,f479])).

fof(f418,plain,(
    spl16_10 ),
    inference(avatar_split_clause,[],[f417,f368])).

fof(f417,plain,(
    m1_subset_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f409,f338])).

fof(f409,plain,(
    m1_subset_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f169,f343,f222])).

fof(f222,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f379,plain,
    ( ~ spl16_11
    | ~ spl16_13
    | spl16_1 ),
    inference(avatar_split_clause,[],[f366,f294,f377,f371])).

fof(f377,plain,
    ( spl16_13
  <=> ~ r2_hidden(sK3,k2_relat_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_13])])).

fof(f294,plain,
    ( spl16_1
  <=> ~ r2_hidden(sK3,k2_relset_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0),u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_1])])).

fof(f366,plain,
    ( ~ r2_hidden(sK3,k2_relat_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2))))
    | ~ m1_subset_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0))))
    | ~ spl16_1 ),
    inference(superposition,[],[f295,f228])).

fof(f295,plain,
    ( ~ r2_hidden(sK3,k2_relset_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0),u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2))))
    | ~ spl16_1 ),
    inference(avatar_component_clause,[],[f294])).

fof(f320,plain,
    ( spl16_0
    | spl16_8 ),
    inference(avatar_split_clause,[],[f175,f318,f291])).

fof(f175,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK1))
    | r2_hidden(sK3,k2_relset_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0),u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)))) ),
    inference(cnf_transformation,[],[f141])).

fof(f313,plain,
    ( spl16_0
    | spl16_6 ),
    inference(avatar_split_clause,[],[f176,f311,f291])).

fof(f176,plain,
    ( r1_orders_2(sK1,sK2,sK4)
    | r2_hidden(sK3,k2_relset_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0),u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)))) ),
    inference(cnf_transformation,[],[f141])).

fof(f306,plain,
    ( spl16_0
    | spl16_4 ),
    inference(avatar_split_clause,[],[f177,f304,f291])).

fof(f177,plain,
    ( k2_waybel_0(sK0,sK1,sK4) = sK3
    | r2_hidden(sK3,k2_relset_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0),u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)))) ),
    inference(cnf_transformation,[],[f141])).

fof(f299,plain,
    ( ~ spl16_1
    | spl16_2 ),
    inference(avatar_split_clause,[],[f178,f297,f294])).

fof(f178,plain,(
    ! [X4] :
      ( k2_waybel_0(sK0,sK1,X4) != sK3
      | ~ r1_orders_2(sK1,sK2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | ~ r2_hidden(sK3,k2_relset_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0),u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)))) ) ),
    inference(cnf_transformation,[],[f141])).
%------------------------------------------------------------------------------
