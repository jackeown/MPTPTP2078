%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1687+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:20 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 301 expanded)
%              Number of leaves         :   44 ( 147 expanded)
%              Depth                    :   10
%              Number of atoms          :  689 (1997 expanded)
%              Number of equality atoms :   89 ( 213 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f398,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f96,f100,f104,f108,f112,f116,f120,f124,f128,f132,f138,f141,f151,f160,f182,f195,f242,f247,f251,f261,f266,f269,f387,f394,f395,f396])).

fof(f396,plain,
    ( u1_struct_0(sK1) != k2_relat_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),u1_struct_0(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f395,plain,
    ( u1_struct_0(sK1) != k2_relat_1(sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),u1_struct_0(sK0)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f394,plain,
    ( ~ spl5_6
    | spl5_57
    | ~ spl5_56 ),
    inference(avatar_split_clause,[],[f389,f385,f391,f102])).

fof(f102,plain,
    ( spl5_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f391,plain,
    ( spl5_57
  <=> u1_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).

fof(f385,plain,
    ( spl5_56
  <=> u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).

fof(f389,plain,
    ( u1_struct_0(sK1) = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl5_56 ),
    inference(superposition,[],[f72,f386])).

fof(f386,plain,
    ( u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl5_56 ),
    inference(avatar_component_clause,[],[f385])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f387,plain,
    ( spl5_12
    | ~ spl5_11
    | spl5_10
    | ~ spl5_9
    | ~ spl5_8
    | ~ spl5_7
    | spl5_56
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f383,f102,f98,f385,f106,f110,f114,f118,f122,f126])).

fof(f126,plain,
    ( spl5_12
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f122,plain,
    ( spl5_11
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f118,plain,
    ( spl5_10
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f114,plain,
    ( spl5_9
  <=> l1_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f110,plain,
    ( spl5_8
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f106,plain,
    ( spl5_7
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f98,plain,
    ( spl5_5
  <=> v23_waybel_0(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f383,plain,
    ( ~ v23_waybel_0(sK2,sK0,sK1)
    | u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_6 ),
    inference(resolution,[],[f56,f103])).

fof(f103,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f102])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v23_waybel_0(X2,X0,X1)
      | u1_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v23_waybel_0(X2,X0,X1)
                  | ( ( ~ r1_orders_2(X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2)),k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)))
                      | ~ r1_orders_2(X0,sK3(X0,X1,X2),sK4(X0,X1,X2)) )
                    & ( r1_orders_2(X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2)),k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)))
                      | r1_orders_2(X0,sK3(X0,X1,X2),sK4(X0,X1,X2)) )
                    & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
                    & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) )
                  | u1_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  | ~ v2_funct_1(X2) )
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
                  | ~ v23_waybel_0(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f38,f40,f39])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ? [X4] :
              ( ( ~ r1_orders_2(X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X4))
                | ~ r1_orders_2(X0,X3,X4) )
              & ( r1_orders_2(X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X4))
                | r1_orders_2(X0,X3,X4) )
              & m1_subset_1(X4,u1_struct_0(X0)) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ? [X4] :
            ( ( ~ r1_orders_2(X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2)),k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X4))
              | ~ r1_orders_2(X0,sK3(X0,X1,X2),X4) )
            & ( r1_orders_2(X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2)),k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X4))
              | r1_orders_2(X0,sK3(X0,X1,X2),X4) )
            & m1_subset_1(X4,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ r1_orders_2(X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2)),k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X4))
            | ~ r1_orders_2(X0,sK3(X0,X1,X2),X4) )
          & ( r1_orders_2(X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2)),k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X4))
            | r1_orders_2(X0,sK3(X0,X1,X2),X4) )
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ( ~ r1_orders_2(X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2)),k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)))
          | ~ r1_orders_2(X0,sK3(X0,X1,X2),sK4(X0,X1,X2)) )
        & ( r1_orders_2(X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2)),k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)))
          | r1_orders_2(X0,sK3(X0,X1,X2),sK4(X0,X1,X2)) )
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v23_waybel_0(X2,X0,X1)
                  | ? [X3] :
                      ( ? [X4] :
                          ( ( ~ r1_orders_2(X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X4))
                            | ~ r1_orders_2(X0,X3,X4) )
                          & ( r1_orders_2(X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X4))
                            | r1_orders_2(X0,X3,X4) )
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | u1_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  | ~ v2_funct_1(X2) )
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
                  | ~ v23_waybel_0(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v23_waybel_0(X2,X0,X1)
                  | ? [X3] :
                      ( ? [X4] :
                          ( ( ~ r1_orders_2(X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X4))
                            | ~ r1_orders_2(X0,X3,X4) )
                          & ( r1_orders_2(X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X4))
                            | r1_orders_2(X0,X3,X4) )
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | u1_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  | ~ v2_funct_1(X2) )
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
                  | ~ v23_waybel_0(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v23_waybel_0(X2,X0,X1)
                  | ? [X3] :
                      ( ? [X4] :
                          ( ( ~ r1_orders_2(X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X4))
                            | ~ r1_orders_2(X0,X3,X4) )
                          & ( r1_orders_2(X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X4))
                            | r1_orders_2(X0,X3,X4) )
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | u1_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  | ~ v2_funct_1(X2) )
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
                  | ~ v23_waybel_0(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v23_waybel_0(X2,X0,X1)
              <=> ( ! [X3] :
                      ( ! [X4] :
                          ( ( r1_orders_2(X0,X3,X4)
                          <=> r1_orders_2(X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) )
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & u1_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & v2_funct_1(X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v23_waybel_0(X2,X0,X1)
              <=> ( ! [X3] :
                      ( ! [X4] :
                          ( ( r1_orders_2(X0,X3,X4)
                          <=> r1_orders_2(X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) )
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & u1_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & v2_funct_1(X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_waybel_0)).

fof(f269,plain,
    ( ~ spl5_14
    | ~ spl5_8
    | spl5_33 ),
    inference(avatar_split_clause,[],[f267,f256,f110,f135])).

fof(f135,plain,
    ( spl5_14
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f256,plain,
    ( spl5_33
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f267,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl5_33 ),
    inference(resolution,[],[f257,f66])).

fof(f66,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f257,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl5_33 ),
    inference(avatar_component_clause,[],[f256])).

fof(f266,plain,
    ( ~ spl5_33
    | ~ spl5_1
    | spl5_35
    | ~ spl5_4
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f262,f249,f94,f264,f85,f256])).

fof(f85,plain,
    ( spl5_1
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f264,plain,
    ( spl5_35
  <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f94,plain,
    ( spl5_4
  <=> u1_struct_0(sK0) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f249,plain,
    ( spl5_32
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f262,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl5_4
    | ~ spl5_32 ),
    inference(forward_demodulation,[],[f253,f250])).

fof(f250,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f249])).

fof(f253,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl5_4 ),
    inference(superposition,[],[f64,f246])).

fof(f246,plain,
    ( u1_struct_0(sK0) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f94])).

fof(f64,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f261,plain,
    ( ~ spl5_33
    | ~ spl5_1
    | spl5_34
    | ~ spl5_4
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f254,f249,f94,f259,f85,f256])).

fof(f259,plain,
    ( spl5_34
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f254,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),u1_struct_0(sK0))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl5_4
    | ~ spl5_32 ),
    inference(forward_demodulation,[],[f252,f250])).

fof(f252,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),u1_struct_0(sK0))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl5_4 ),
    inference(superposition,[],[f65,f246])).

fof(f65,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f251,plain,
    ( ~ spl5_14
    | ~ spl5_8
    | spl5_32
    | ~ spl5_31 ),
    inference(avatar_split_clause,[],[f244,f239,f249,f110,f135])).

fof(f239,plain,
    ( spl5_31
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f244,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl5_31 ),
    inference(resolution,[],[f240,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f240,plain,
    ( v2_funct_1(sK2)
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f239])).

fof(f247,plain,
    ( ~ spl5_14
    | ~ spl5_8
    | spl5_4
    | ~ spl5_17
    | ~ spl5_31 ),
    inference(avatar_split_clause,[],[f245,f239,f157,f94,f110,f135])).

fof(f157,plain,
    ( spl5_17
  <=> u1_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f245,plain,
    ( u1_struct_0(sK0) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl5_17
    | ~ spl5_31 ),
    inference(forward_demodulation,[],[f243,f158])).

fof(f158,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f157])).

fof(f243,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl5_31 ),
    inference(resolution,[],[f240,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f242,plain,
    ( spl5_12
    | ~ spl5_11
    | spl5_10
    | ~ spl5_9
    | ~ spl5_8
    | ~ spl5_7
    | spl5_31
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f235,f102,f98,f239,f106,f110,f114,f118,f122,f126])).

fof(f235,plain,
    ( ~ v23_waybel_0(sK2,sK0,sK1)
    | v2_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_6 ),
    inference(resolution,[],[f55,f103])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v23_waybel_0(X2,X0,X1)
      | v2_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f195,plain,
    ( ~ spl5_9
    | spl5_21 ),
    inference(avatar_split_clause,[],[f193,f179,f114])).

fof(f179,plain,
    ( spl5_21
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f193,plain,
    ( ~ l1_orders_2(sK1)
    | spl5_21 ),
    inference(resolution,[],[f180,f53])).

fof(f53,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f180,plain,
    ( ~ l1_struct_0(sK1)
    | spl5_21 ),
    inference(avatar_component_clause,[],[f179])).

fof(f182,plain,
    ( spl5_10
    | ~ spl5_21
    | ~ spl5_13
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f164,f148,f130,f179,f118])).

fof(f130,plain,
    ( spl5_13
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f148,plain,
    ( spl5_16
  <=> k1_xboole_0 = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f164,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl5_16 ),
    inference(superposition,[],[f54,f149])).

fof(f149,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f148])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f160,plain,
    ( ~ spl5_6
    | spl5_17
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f154,f145,f157,f102])).

fof(f145,plain,
    ( spl5_15
  <=> u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f154,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl5_15 ),
    inference(superposition,[],[f71,f146])).

fof(f146,plain,
    ( u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f145])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f151,plain,
    ( spl5_15
    | spl5_16
    | ~ spl5_7
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f142,f102,f106,f148,f145])).

fof(f142,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | k1_xboole_0 = u1_struct_0(sK1)
    | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl5_6 ),
    inference(resolution,[],[f73,f103])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f141,plain,
    ( ~ spl5_6
    | spl5_14 ),
    inference(avatar_contradiction_clause,[],[f140])).

fof(f140,plain,
    ( $false
    | ~ spl5_6
    | spl5_14 ),
    inference(subsumption_resolution,[],[f103,f139])).

fof(f139,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl5_14 ),
    inference(resolution,[],[f70,f136])).

fof(f136,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_14 ),
    inference(avatar_component_clause,[],[f135])).

% (9190)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% (9182)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% (9191)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% (9181)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f138,plain,
    ( ~ spl5_14
    | ~ spl5_8
    | spl5_1 ),
    inference(avatar_split_clause,[],[f133,f85,f110,f135])).

fof(f133,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl5_1 ),
    inference(resolution,[],[f67,f86])).

fof(f86,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f85])).

fof(f67,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f132,plain,(
    spl5_13 ),
    inference(avatar_split_clause,[],[f52,f130])).

fof(f52,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f128,plain,(
    ~ spl5_12 ),
    inference(avatar_split_clause,[],[f43,f126])).

fof(f43,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( u1_struct_0(sK0) != k2_relat_1(k2_funct_1(sK2))
      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & v23_waybel_0(sK2,sK0,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_orders_2(sK1)
    & ~ v2_struct_0(sK1)
    & l1_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f34,f33,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( u1_struct_0(X0) != k2_relat_1(k2_funct_1(X2))
                  | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  | ~ v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
                  | ~ v1_funct_1(k2_funct_1(X2)) )
                & v23_waybel_0(X2,X0,X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_orders_2(X1)
            & ~ v2_struct_0(X1) )
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( k2_relat_1(k2_funct_1(X2)) != u1_struct_0(sK0)
                | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
                | ~ v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(sK0))
                | ~ v1_funct_1(k2_funct_1(X2)) )
              & v23_waybel_0(X2,sK0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( k2_relat_1(k2_funct_1(X2)) != u1_struct_0(sK0)
              | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
              | ~ v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(sK0))
              | ~ v1_funct_1(k2_funct_1(X2)) )
            & v23_waybel_0(X2,sK0,X1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_orders_2(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( k2_relat_1(k2_funct_1(X2)) != u1_struct_0(sK0)
            | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
            | ~ v1_funct_2(k2_funct_1(X2),u1_struct_0(sK1),u1_struct_0(sK0))
            | ~ v1_funct_1(k2_funct_1(X2)) )
          & v23_waybel_0(X2,sK0,sK1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X2] :
        ( ( k2_relat_1(k2_funct_1(X2)) != u1_struct_0(sK0)
          | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
          | ~ v1_funct_2(k2_funct_1(X2),u1_struct_0(sK1),u1_struct_0(sK0))
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & v23_waybel_0(X2,sK0,sK1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ( u1_struct_0(sK0) != k2_relat_1(k2_funct_1(sK2))
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(k2_funct_1(sK2)) )
      & v23_waybel_0(sK2,sK0,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( u1_struct_0(X0) != k2_relat_1(k2_funct_1(X2))
                | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                | ~ v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
                | ~ v1_funct_1(k2_funct_1(X2)) )
              & v23_waybel_0(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( u1_struct_0(X0) != k2_relat_1(k2_funct_1(X2))
                | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                | ~ v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
                | ~ v1_funct_1(k2_funct_1(X2)) )
              & v23_waybel_0(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
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
                 => ( u1_struct_0(X0) = k2_relat_1(k2_funct_1(X2))
                    & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(k2_funct_1(X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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
               => ( u1_struct_0(X0) = k2_relat_1(k2_funct_1(X2))
                  & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(k2_funct_1(X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_waybel_0)).

fof(f124,plain,(
    spl5_11 ),
    inference(avatar_split_clause,[],[f44,f122])).

fof(f44,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f120,plain,(
    ~ spl5_10 ),
    inference(avatar_split_clause,[],[f45,f118])).

fof(f45,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f116,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f46,f114])).

fof(f46,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f112,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f47,f110])).

fof(f47,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f108,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f48,f106])).

fof(f48,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f104,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f49,f102])).

fof(f49,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f35])).

fof(f100,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f50,f98])).

fof(f50,plain,(
    v23_waybel_0(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f96,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f51,f94,f91,f88,f85])).

fof(f88,plain,
    ( spl5_2
  <=> v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f91,plain,
    ( spl5_3
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f51,plain,
    ( u1_struct_0(sK0) != k2_relat_1(k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f35])).

%------------------------------------------------------------------------------
