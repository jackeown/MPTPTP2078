%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : orders_2__t38_orders_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:20 EDT 2019

% Result     : Theorem 1.31s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :  263 ( 578 expanded)
%              Number of leaves         :   57 ( 255 expanded)
%              Depth                    :   12
%              Number of atoms          : 1186 (3836 expanded)
%              Number of equality atoms :   78 ( 144 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4512,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f181,f188,f216,f223,f302,f381,f390,f437,f455,f473,f501,f521,f551,f608,f670,f677,f690,f761,f784,f884,f890,f909,f1175,f1214,f1482,f2232,f2291,f2318,f2695,f2696,f2708,f2721,f2761,f2799,f4429,f4511])).

fof(f4511,plain,
    ( spl12_40
    | ~ spl12_22 ),
    inference(avatar_split_clause,[],[f4475,f294,f379])).

fof(f379,plain,
    ( spl12_40
  <=> ! [X3] :
        ( ~ r2_hidden(sK2,X3)
        | ~ v6_orders_2(X3,sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK1,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_40])])).

fof(f294,plain,
    ( spl12_22
  <=> r1_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_22])])).

fof(f4475,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK2,X3)
        | ~ r2_hidden(sK1,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v6_orders_2(X3,sK0) )
    | ~ spl12_22 ),
    inference(subsumption_resolution,[],[f117,f295])).

fof(f295,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ spl12_22 ),
    inference(avatar_component_clause,[],[f294])).

fof(f117,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK2,X3)
      | ~ r2_hidden(sK1,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v6_orders_2(X3,sK0)
      | ~ r1_orders_2(sK0,sK1,sK2) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,
    ( ( ( ! [X3] :
            ( ~ r2_hidden(sK2,X3)
            | ~ r2_hidden(sK1,X3)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
            | ~ v6_orders_2(X3,sK0) )
        & ( r1_orders_2(sK0,sK2,sK1)
          | r1_orders_2(sK0,sK1,sK2) ) )
      | ( ~ r1_orders_2(sK0,sK2,sK1)
        & ~ r1_orders_2(sK0,sK1,sK2)
        & r2_hidden(sK2,sK3)
        & r2_hidden(sK1,sK3)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
        & v6_orders_2(sK3,sK0) ) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v3_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f43,f80,f79,f78,f77])).

fof(f77,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ( ! [X3] :
                        ( ~ r2_hidden(X2,X3)
                        | ~ r2_hidden(X1,X3)
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        | ~ v6_orders_2(X3,X0) )
                    & ( r1_orders_2(X0,X2,X1)
                      | r1_orders_2(X0,X1,X2) ) )
                  | ( ~ r1_orders_2(X0,X2,X1)
                    & ~ r1_orders_2(X0,X1,X2)
                    & ? [X4] :
                        ( r2_hidden(X2,X4)
                        & r2_hidden(X1,X4)
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                        & v6_orders_2(X4,X0) ) ) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ( ! [X3] :
                      ( ~ r2_hidden(X2,X3)
                      | ~ r2_hidden(X1,X3)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
                      | ~ v6_orders_2(X3,sK0) )
                  & ( r1_orders_2(sK0,X2,X1)
                    | r1_orders_2(sK0,X1,X2) ) )
                | ( ~ r1_orders_2(sK0,X2,X1)
                  & ~ r1_orders_2(sK0,X1,X2)
                  & ? [X4] :
                      ( r2_hidden(X2,X4)
                      & r2_hidden(X1,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
                      & v6_orders_2(X4,sK0) ) ) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v3_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( ! [X3] :
                      ( ~ r2_hidden(X2,X3)
                      | ~ r2_hidden(X1,X3)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      | ~ v6_orders_2(X3,X0) )
                  & ( r1_orders_2(X0,X2,X1)
                    | r1_orders_2(X0,X1,X2) ) )
                | ( ~ r1_orders_2(X0,X2,X1)
                  & ~ r1_orders_2(X0,X1,X2)
                  & ? [X4] :
                      ( r2_hidden(X2,X4)
                      & r2_hidden(X1,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                      & v6_orders_2(X4,X0) ) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ( ( ! [X3] :
                    ( ~ r2_hidden(X2,X3)
                    | ~ r2_hidden(sK1,X3)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    | ~ v6_orders_2(X3,X0) )
                & ( r1_orders_2(X0,X2,sK1)
                  | r1_orders_2(X0,sK1,X2) ) )
              | ( ~ r1_orders_2(X0,X2,sK1)
                & ~ r1_orders_2(X0,sK1,X2)
                & ? [X4] :
                    ( r2_hidden(X2,X4)
                    & r2_hidden(sK1,X4)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                    & v6_orders_2(X4,X0) ) ) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ( ! [X3] :
                  ( ~ r2_hidden(X2,X3)
                  | ~ r2_hidden(X1,X3)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v6_orders_2(X3,X0) )
              & ( r1_orders_2(X0,X2,X1)
                | r1_orders_2(X0,X1,X2) ) )
            | ( ~ r1_orders_2(X0,X2,X1)
              & ~ r1_orders_2(X0,X1,X2)
              & ? [X4] :
                  ( r2_hidden(X2,X4)
                  & r2_hidden(X1,X4)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                  & v6_orders_2(X4,X0) ) ) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( ( ! [X3] :
                ( ~ r2_hidden(sK2,X3)
                | ~ r2_hidden(X1,X3)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                | ~ v6_orders_2(X3,X0) )
            & ( r1_orders_2(X0,sK2,X1)
              | r1_orders_2(X0,X1,sK2) ) )
          | ( ~ r1_orders_2(X0,sK2,X1)
            & ~ r1_orders_2(X0,X1,sK2)
            & ? [X4] :
                ( r2_hidden(sK2,X4)
                & r2_hidden(X1,X4)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                & v6_orders_2(X4,X0) ) ) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ? [X4] :
          ( r2_hidden(X2,X4)
          & r2_hidden(X1,X4)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
          & v6_orders_2(X4,X0) )
     => ( r2_hidden(X2,sK3)
        & r2_hidden(X1,sK3)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
        & v6_orders_2(sK3,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( ! [X3] :
                      ( ~ r2_hidden(X2,X3)
                      | ~ r2_hidden(X1,X3)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      | ~ v6_orders_2(X3,X0) )
                  & ( r1_orders_2(X0,X2,X1)
                    | r1_orders_2(X0,X1,X2) ) )
                | ( ~ r1_orders_2(X0,X2,X1)
                  & ~ r1_orders_2(X0,X1,X2)
                  & ? [X4] :
                      ( r2_hidden(X2,X4)
                      & r2_hidden(X1,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                      & v6_orders_2(X4,X0) ) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( ! [X3] :
                      ( ~ r2_hidden(X2,X3)
                      | ~ r2_hidden(X1,X3)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      | ~ v6_orders_2(X3,X0) )
                  & ( r1_orders_2(X0,X2,X1)
                    | r1_orders_2(X0,X1,X2) ) )
                | ( ~ r1_orders_2(X0,X2,X1)
                  & ~ r1_orders_2(X0,X1,X2)
                  & ? [X4] :
                      ( r2_hidden(X2,X4)
                      & r2_hidden(X1,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                      & v6_orders_2(X4,X0) ) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f41,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( ~ ( ! [X3] :
                          ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                            & v6_orders_2(X3,X0) )
                         => ~ ( r2_hidden(X2,X3)
                              & r2_hidden(X1,X3) ) )
                      & ( r1_orders_2(X0,X2,X1)
                        | r1_orders_2(X0,X1,X2) ) )
                  & ~ ( ~ r1_orders_2(X0,X2,X1)
                      & ~ r1_orders_2(X0,X1,X2)
                      & ? [X4] :
                          ( r2_hidden(X2,X4)
                          & r2_hidden(X1,X4)
                          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                          & v6_orders_2(X4,X0) ) ) ) ) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( ~ ( ! [X3] :
                          ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                            & v6_orders_2(X3,X0) )
                         => ~ ( r2_hidden(X2,X3)
                              & r2_hidden(X1,X3) ) )
                      & ( r1_orders_2(X0,X2,X1)
                        | r1_orders_2(X0,X1,X2) ) )
                  & ~ ( ~ r1_orders_2(X0,X2,X1)
                      & ~ r1_orders_2(X0,X1,X2)
                      & ? [X3] :
                          ( r2_hidden(X2,X3)
                          & r2_hidden(X1,X3)
                          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                          & v6_orders_2(X3,X0) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ~ ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                          & v6_orders_2(X3,X0) )
                       => ~ ( r2_hidden(X2,X3)
                            & r2_hidden(X1,X3) ) )
                    & ( r1_orders_2(X0,X2,X1)
                      | r1_orders_2(X0,X1,X2) ) )
                & ~ ( ~ r1_orders_2(X0,X2,X1)
                    & ~ r1_orders_2(X0,X1,X2)
                    & ? [X3] :
                        ( r2_hidden(X2,X3)
                        & r2_hidden(X1,X3)
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & v6_orders_2(X3,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t38_orders_2.p',t38_orders_2)).

fof(f4429,plain,
    ( ~ spl12_2
    | ~ spl12_10
    | ~ spl12_12
    | spl12_23
    | ~ spl12_48 ),
    inference(avatar_contradiction_clause,[],[f4428])).

fof(f4428,plain,
    ( $false
    | ~ spl12_2
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_23
    | ~ spl12_48 ),
    inference(subsumption_resolution,[],[f4427,f187])).

fof(f187,plain,
    ( l1_orders_2(sK0)
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl12_2
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f4427,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_23
    | ~ spl12_48 ),
    inference(subsumption_resolution,[],[f4426,f215])).

fof(f215,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl12_10 ),
    inference(avatar_component_clause,[],[f214])).

fof(f214,plain,
    ( spl12_10
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).

fof(f4426,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl12_12
    | ~ spl12_23
    | ~ spl12_48 ),
    inference(subsumption_resolution,[],[f4425,f222])).

fof(f222,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl12_12 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl12_12
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).

fof(f4425,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl12_23
    | ~ spl12_48 ),
    inference(subsumption_resolution,[],[f4419,f292])).

fof(f292,plain,
    ( ~ r1_orders_2(sK0,sK1,sK2)
    | ~ spl12_23 ),
    inference(avatar_component_clause,[],[f291])).

fof(f291,plain,
    ( spl12_23
  <=> ~ r1_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_23])])).

fof(f4419,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl12_48 ),
    inference(resolution,[],[f436,f129])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
                & ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
                  | ~ r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t38_orders_2.p',d9_orders_2)).

fof(f436,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ spl12_48 ),
    inference(avatar_component_clause,[],[f435])).

fof(f435,plain,
    ( spl12_48
  <=> r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_48])])).

fof(f2799,plain,
    ( ~ spl12_42
    | spl12_49
    | ~ spl12_56
    | spl12_63
    | ~ spl12_88
    | ~ spl12_90 ),
    inference(avatar_contradiction_clause,[],[f2797])).

fof(f2797,plain,
    ( $false
    | ~ spl12_42
    | ~ spl12_49
    | ~ spl12_56
    | ~ spl12_63
    | ~ spl12_88
    | ~ spl12_90 ),
    inference(unit_resulting_resolution,[],[f689,f389,f472,f676,f433,f497,f120])).

fof(f120,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ r7_relat_2(X0,X1)
      | r2_hidden(k4_tarski(X4,X5),X0)
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(k4_tarski(X5,X4),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r7_relat_2(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
              & ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
              & r2_hidden(sK5(X0,X1),X1)
              & r2_hidden(sK4(X0,X1),X1) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X5,X4),X0)
                | r2_hidden(k4_tarski(X4,X5),X0)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X1) )
            | ~ r7_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f83,f84])).

fof(f84,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X3,X2),X0)
          & ~ r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
        & ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
        & r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f83,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r7_relat_2(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                & ~ r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X5,X4),X0)
                | r2_hidden(k4_tarski(X4,X5),X0)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X1) )
            | ~ r7_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f82])).

fof(f82,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r7_relat_2(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                & ~ r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X2,X3] :
                ( r2_hidden(k4_tarski(X3,X2),X0)
                | r2_hidden(k4_tarski(X2,X3),X0)
                | ~ r2_hidden(X3,X1)
                | ~ r2_hidden(X2,X1) )
            | ~ r7_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r7_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r7_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ~ ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                & ~ r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t38_orders_2.p',d7_relat_2)).

fof(f497,plain,
    ( ~ r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0))
    | ~ spl12_63 ),
    inference(avatar_component_clause,[],[f496])).

fof(f496,plain,
    ( spl12_63
  <=> ~ r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_63])])).

fof(f433,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ spl12_49 ),
    inference(avatar_component_clause,[],[f432])).

fof(f432,plain,
    ( spl12_49
  <=> ~ r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_49])])).

fof(f676,plain,
    ( r7_relat_2(u1_orders_2(sK0),sK3)
    | ~ spl12_88 ),
    inference(avatar_component_clause,[],[f675])).

fof(f675,plain,
    ( spl12_88
  <=> r7_relat_2(u1_orders_2(sK0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_88])])).

fof(f472,plain,
    ( r2_hidden(sK2,sK3)
    | ~ spl12_56 ),
    inference(avatar_component_clause,[],[f471])).

fof(f471,plain,
    ( spl12_56
  <=> r2_hidden(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_56])])).

fof(f389,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl12_42 ),
    inference(avatar_component_clause,[],[f388])).

fof(f388,plain,
    ( spl12_42
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_42])])).

fof(f689,plain,
    ( v1_relat_1(u1_orders_2(sK0))
    | ~ spl12_90 ),
    inference(avatar_component_clause,[],[f688])).

fof(f688,plain,
    ( spl12_90
  <=> v1_relat_1(u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_90])])).

fof(f2761,plain,
    ( ~ spl12_71
    | ~ spl12_62 ),
    inference(avatar_split_clause,[],[f2314,f499,f549])).

fof(f549,plain,
    ( spl12_71
  <=> ~ v1_xboole_0(u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_71])])).

fof(f499,plain,
    ( spl12_62
  <=> r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_62])])).

fof(f2314,plain,
    ( ~ v1_xboole_0(u1_orders_2(sK0))
    | ~ spl12_62 ),
    inference(resolution,[],[f500,f148])).

fof(f148,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t38_orders_2.p',t7_boole)).

fof(f500,plain,
    ( r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0))
    | ~ spl12_62 ),
    inference(avatar_component_clause,[],[f499])).

fof(f2721,plain,
    ( spl12_40
    | ~ spl12_24 ),
    inference(avatar_split_clause,[],[f2711,f300,f379])).

fof(f300,plain,
    ( spl12_24
  <=> r1_orders_2(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_24])])).

fof(f2711,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK2,X3)
        | ~ r2_hidden(sK1,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v6_orders_2(X3,sK0) )
    | ~ spl12_24 ),
    inference(subsumption_resolution,[],[f118,f301])).

fof(f301,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | ~ spl12_24 ),
    inference(avatar_component_clause,[],[f300])).

fof(f118,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK2,X3)
      | ~ r2_hidden(sK1,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v6_orders_2(X3,sK0)
      | ~ r1_orders_2(sK0,sK2,sK1) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f2708,plain,
    ( ~ spl12_40
    | ~ spl12_184
    | ~ spl12_274 ),
    inference(avatar_contradiction_clause,[],[f2707])).

fof(f2707,plain,
    ( $false
    | ~ spl12_40
    | ~ spl12_184
    | ~ spl12_274 ),
    inference(subsumption_resolution,[],[f2706,f169])).

fof(f169,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f168])).

fof(f168,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f158])).

fof(f158,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f98])).

fof(f98,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK7(X0,X1,X2) != X1
              & sK7(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( sK7(X0,X1,X2) = X1
            | sK7(X0,X1,X2) = X0
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f96,f97])).

fof(f97,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK7(X0,X1,X2) != X1
            & sK7(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( sK7(X0,X1,X2) = X1
          | sK7(X0,X1,X2) = X0
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f96,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f95])).

fof(f95,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f94])).

fof(f94,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t38_orders_2.p',d2_tarski)).

fof(f2706,plain,
    ( ~ r2_hidden(sK1,k2_tarski(sK1,sK2))
    | ~ spl12_40
    | ~ spl12_184
    | ~ spl12_274 ),
    inference(subsumption_resolution,[],[f2705,f1453])).

fof(f1453,plain,
    ( m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl12_184 ),
    inference(avatar_component_clause,[],[f1452])).

fof(f1452,plain,
    ( spl12_184
  <=> m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_184])])).

fof(f2705,plain,
    ( ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k2_tarski(sK1,sK2))
    | ~ spl12_40
    | ~ spl12_274 ),
    inference(subsumption_resolution,[],[f2702,f167])).

fof(f167,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f166])).

fof(f166,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f159])).

fof(f159,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f98])).

fof(f2702,plain,
    ( ~ r2_hidden(sK2,k2_tarski(sK1,sK2))
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k2_tarski(sK1,sK2))
    | ~ spl12_40
    | ~ spl12_274 ),
    inference(resolution,[],[f2694,f380])).

fof(f380,plain,
    ( ! [X3] :
        ( ~ v6_orders_2(X3,sK0)
        | ~ r2_hidden(sK2,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK1,X3) )
    | ~ spl12_40 ),
    inference(avatar_component_clause,[],[f379])).

fof(f2694,plain,
    ( v6_orders_2(k2_tarski(sK1,sK2),sK0)
    | ~ spl12_274 ),
    inference(avatar_component_clause,[],[f2693])).

fof(f2693,plain,
    ( spl12_274
  <=> v6_orders_2(k2_tarski(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_274])])).

fof(f2696,plain,
    ( spl12_274
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_24
    | ~ spl12_160
    | ~ spl12_258 ),
    inference(avatar_split_clause,[],[f2688,f2230,f1212,f300,f221,f214,f2693])).

fof(f1212,plain,
    ( spl12_160
  <=> k2_tarski(sK1,sK2) = k7_domain_1(u1_struct_0(sK0),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_160])])).

fof(f2230,plain,
    ( spl12_258
  <=> ! [X1,X2] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | v6_orders_2(k7_domain_1(u1_struct_0(sK0),X2,X1),sK0)
        | ~ r1_orders_2(sK0,X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_258])])).

fof(f2688,plain,
    ( v6_orders_2(k2_tarski(sK1,sK2),sK0)
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_24
    | ~ spl12_160
    | ~ spl12_258 ),
    inference(forward_demodulation,[],[f2687,f1213])).

fof(f1213,plain,
    ( k2_tarski(sK1,sK2) = k7_domain_1(u1_struct_0(sK0),sK2,sK1)
    | ~ spl12_160 ),
    inference(avatar_component_clause,[],[f1212])).

fof(f2687,plain,
    ( v6_orders_2(k7_domain_1(u1_struct_0(sK0),sK2,sK1),sK0)
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_24
    | ~ spl12_258 ),
    inference(subsumption_resolution,[],[f2686,f215])).

fof(f2686,plain,
    ( v6_orders_2(k7_domain_1(u1_struct_0(sK0),sK2,sK1),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl12_12
    | ~ spl12_24
    | ~ spl12_258 ),
    inference(subsumption_resolution,[],[f2680,f222])).

fof(f2680,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v6_orders_2(k7_domain_1(u1_struct_0(sK0),sK2,sK1),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl12_24
    | ~ spl12_258 ),
    inference(resolution,[],[f2231,f301])).

fof(f2231,plain,
    ( ! [X2,X1] :
        ( ~ r1_orders_2(sK0,X2,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | v6_orders_2(k7_domain_1(u1_struct_0(sK0),X2,X1),sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl12_258 ),
    inference(avatar_component_clause,[],[f2230])).

fof(f2695,plain,
    ( spl12_274
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_22
    | ~ spl12_156
    | ~ spl12_258 ),
    inference(avatar_split_clause,[],[f2685,f2230,f1173,f294,f221,f214,f2693])).

fof(f1173,plain,
    ( spl12_156
  <=> k2_tarski(sK1,sK2) = k7_domain_1(u1_struct_0(sK0),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_156])])).

fof(f2685,plain,
    ( v6_orders_2(k2_tarski(sK1,sK2),sK0)
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_22
    | ~ spl12_156
    | ~ spl12_258 ),
    inference(forward_demodulation,[],[f2684,f1174])).

fof(f1174,plain,
    ( k2_tarski(sK1,sK2) = k7_domain_1(u1_struct_0(sK0),sK1,sK2)
    | ~ spl12_156 ),
    inference(avatar_component_clause,[],[f1173])).

fof(f2684,plain,
    ( v6_orders_2(k7_domain_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_22
    | ~ spl12_258 ),
    inference(subsumption_resolution,[],[f2683,f222])).

fof(f2683,plain,
    ( v6_orders_2(k7_domain_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl12_10
    | ~ spl12_22
    | ~ spl12_258 ),
    inference(subsumption_resolution,[],[f2679,f215])).

fof(f2679,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v6_orders_2(k7_domain_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl12_22
    | ~ spl12_258 ),
    inference(resolution,[],[f2231,f295])).

fof(f2318,plain,
    ( spl12_24
    | ~ spl12_2
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_62 ),
    inference(avatar_split_clause,[],[f2317,f499,f221,f214,f186,f300])).

fof(f2317,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | ~ spl12_2
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_62 ),
    inference(subsumption_resolution,[],[f2316,f187])).

fof(f2316,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | ~ l1_orders_2(sK0)
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_62 ),
    inference(subsumption_resolution,[],[f2315,f222])).

fof(f2315,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl12_10
    | ~ spl12_62 ),
    inference(subsumption_resolution,[],[f2310,f215])).

fof(f2310,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl12_62 ),
    inference(resolution,[],[f500,f129])).

fof(f2291,plain,
    ( ~ spl12_52
    | spl12_71
    | ~ spl12_86 ),
    inference(avatar_contradiction_clause,[],[f2284])).

fof(f2284,plain,
    ( $false
    | ~ spl12_52
    | ~ spl12_71
    | ~ spl12_86 ),
    inference(unit_resulting_resolution,[],[f550,f669,f449,f141])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t38_orders_2.p',cc4_relset_1)).

fof(f449,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl12_52 ),
    inference(avatar_component_clause,[],[f448])).

fof(f448,plain,
    ( spl12_52
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_52])])).

fof(f669,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl12_86 ),
    inference(avatar_component_clause,[],[f668])).

fof(f668,plain,
    ( spl12_86
  <=> m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_86])])).

fof(f550,plain,
    ( ~ v1_xboole_0(u1_orders_2(sK0))
    | ~ spl12_71 ),
    inference(avatar_component_clause,[],[f549])).

fof(f2232,plain,
    ( spl12_258
    | ~ spl12_0
    | ~ spl12_2
    | spl12_119
    | ~ spl12_126 ),
    inference(avatar_split_clause,[],[f923,f907,f864,f186,f179,f2230])).

fof(f179,plain,
    ( spl12_0
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_0])])).

fof(f864,plain,
    ( spl12_119
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_119])])).

fof(f907,plain,
    ( spl12_126
  <=> ! [X1,X0] :
        ( ~ r3_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v6_orders_2(k7_domain_1(u1_struct_0(sK0),X0,X1),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_126])])).

fof(f923,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | v6_orders_2(k7_domain_1(u1_struct_0(sK0),X2,X1),sK0)
        | ~ r1_orders_2(sK0,X2,X1) )
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_119
    | ~ spl12_126 ),
    inference(subsumption_resolution,[],[f922,f865])).

fof(f865,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl12_119 ),
    inference(avatar_component_clause,[],[f864])).

fof(f922,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | v6_orders_2(k7_domain_1(u1_struct_0(sK0),X2,X1),sK0)
        | ~ r1_orders_2(sK0,X2,X1)
        | v2_struct_0(sK0) )
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_126 ),
    inference(subsumption_resolution,[],[f921,f180])).

fof(f180,plain,
    ( v3_orders_2(sK0)
    | ~ spl12_0 ),
    inference(avatar_component_clause,[],[f179])).

fof(f921,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | v6_orders_2(k7_domain_1(u1_struct_0(sK0),X2,X1),sK0)
        | ~ r1_orders_2(sK0,X2,X1)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl12_2
    | ~ spl12_126 ),
    inference(subsumption_resolution,[],[f916,f187])).

fof(f916,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | v6_orders_2(k7_domain_1(u1_struct_0(sK0),X2,X1),sK0)
        | ~ r1_orders_2(sK0,X2,X1)
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl12_126 ),
    inference(duplicate_literal_removal,[],[f915])).

fof(f915,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | v6_orders_2(k7_domain_1(u1_struct_0(sK0),X2,X1),sK0)
        | ~ r1_orders_2(sK0,X2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl12_126 ),
    inference(resolution,[],[f908,f152])).

fof(f152,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f93,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t38_orders_2.p',redefinition_r3_orders_2)).

fof(f908,plain,
    ( ! [X0,X1] :
        ( ~ r3_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v6_orders_2(k7_domain_1(u1_struct_0(sK0),X0,X1),sK0) )
    | ~ spl12_126 ),
    inference(avatar_component_clause,[],[f907])).

fof(f1482,plain,
    ( spl12_184
    | ~ spl12_10
    | ~ spl12_12
    | spl12_53
    | ~ spl12_160 ),
    inference(avatar_split_clause,[],[f1336,f1212,f445,f221,f214,f1452])).

fof(f445,plain,
    ( spl12_53
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_53])])).

fof(f1336,plain,
    ( m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_53
    | ~ spl12_160 ),
    inference(subsumption_resolution,[],[f1335,f446])).

fof(f446,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl12_53 ),
    inference(avatar_component_clause,[],[f445])).

fof(f1335,plain,
    ( m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_160 ),
    inference(subsumption_resolution,[],[f1334,f222])).

fof(f1334,plain,
    ( m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl12_10
    | ~ spl12_160 ),
    inference(subsumption_resolution,[],[f1318,f215])).

fof(f1318,plain,
    ( m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl12_160 ),
    inference(superposition,[],[f153,f1213])).

fof(f153,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t38_orders_2.p',dt_k7_domain_1)).

fof(f1214,plain,
    ( spl12_160
    | ~ spl12_10
    | ~ spl12_104 ),
    inference(avatar_split_clause,[],[f792,f782,f214,f1212])).

fof(f782,plain,
    ( spl12_104
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k2_tarski(sK2,X3) = k7_domain_1(u1_struct_0(sK0),sK2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_104])])).

fof(f792,plain,
    ( k2_tarski(sK1,sK2) = k7_domain_1(u1_struct_0(sK0),sK2,sK1)
    | ~ spl12_10
    | ~ spl12_104 ),
    inference(forward_demodulation,[],[f789,f140])).

fof(f140,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t38_orders_2.p',commutativity_k2_tarski)).

fof(f789,plain,
    ( k2_tarski(sK2,sK1) = k7_domain_1(u1_struct_0(sK0),sK2,sK1)
    | ~ spl12_10
    | ~ spl12_104 ),
    inference(resolution,[],[f783,f215])).

fof(f783,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k2_tarski(sK2,X3) = k7_domain_1(u1_struct_0(sK0),sK2,X3) )
    | ~ spl12_104 ),
    inference(avatar_component_clause,[],[f782])).

fof(f1175,plain,
    ( spl12_156
    | ~ spl12_12
    | ~ spl12_100 ),
    inference(avatar_split_clause,[],[f769,f759,f221,f1173])).

fof(f759,plain,
    ( spl12_100
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k2_tarski(sK1,X2) = k7_domain_1(u1_struct_0(sK0),sK1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_100])])).

fof(f769,plain,
    ( k2_tarski(sK1,sK2) = k7_domain_1(u1_struct_0(sK0),sK1,sK2)
    | ~ spl12_12
    | ~ spl12_100 ),
    inference(resolution,[],[f760,f222])).

fof(f760,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k2_tarski(sK1,X2) = k7_domain_1(u1_struct_0(sK0),sK1,X2) )
    | ~ spl12_100 ),
    inference(avatar_component_clause,[],[f759])).

fof(f909,plain,
    ( spl12_126
    | ~ spl12_0
    | ~ spl12_2
    | spl12_119 ),
    inference(avatar_split_clause,[],[f898,f864,f186,f179,f907])).

fof(f898,plain,
    ( ! [X0,X1] :
        ( ~ r3_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v6_orders_2(k7_domain_1(u1_struct_0(sK0),X0,X1),sK0) )
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_119 ),
    inference(subsumption_resolution,[],[f562,f865])).

fof(f562,plain,
    ( ! [X0,X1] :
        ( ~ r3_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v6_orders_2(k7_domain_1(u1_struct_0(sK0),X0,X1),sK0)
        | v2_struct_0(sK0) )
    | ~ spl12_0
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f561,f187])).

fof(f561,plain,
    ( ! [X0,X1] :
        ( ~ r3_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | v6_orders_2(k7_domain_1(u1_struct_0(sK0),X0,X1),sK0)
        | v2_struct_0(sK0) )
    | ~ spl12_0 ),
    inference(resolution,[],[f134,f180])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                    & v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) )
                  | ( ~ r3_orders_2(X0,X2,X1)
                    & ~ r3_orders_2(X0,X1,X2) ) )
                & ( r3_orders_2(X0,X2,X1)
                  | r3_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f88])).

fof(f88,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                    & v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) )
                  | ( ~ r3_orders_2(X0,X2,X1)
                    & ~ r3_orders_2(X0,X1,X2) ) )
                & ( r3_orders_2(X0,X2,X1)
                  | r3_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                  & v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) )
              <=> ( r3_orders_2(X0,X2,X1)
                  | r3_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                  & v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) )
              <=> ( r3_orders_2(X0,X2,X1)
                  | r3_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                  & v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) )
              <=> ( r3_orders_2(X0,X2,X1)
                  | r3_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t38_orders_2.p',t36_orders_2)).

fof(f890,plain,
    ( ~ spl12_2
    | spl12_123 ),
    inference(avatar_contradiction_clause,[],[f889])).

fof(f889,plain,
    ( $false
    | ~ spl12_2
    | ~ spl12_123 ),
    inference(subsumption_resolution,[],[f887,f187])).

fof(f887,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl12_123 ),
    inference(resolution,[],[f883,f125])).

fof(f125,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t38_orders_2.p',dt_l1_orders_2)).

fof(f883,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl12_123 ),
    inference(avatar_component_clause,[],[f882])).

fof(f882,plain,
    ( spl12_123
  <=> ~ l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_123])])).

fof(f884,plain,
    ( ~ spl12_123
    | spl12_53
    | ~ spl12_118 ),
    inference(avatar_split_clause,[],[f874,f867,f445,f882])).

fof(f867,plain,
    ( spl12_118
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_118])])).

fof(f874,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl12_53
    | ~ spl12_118 ),
    inference(subsumption_resolution,[],[f873,f446])).

fof(f873,plain,
    ( ~ l1_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl12_118 ),
    inference(resolution,[],[f868,f138])).

fof(f138,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v2_struct_0(X0) )
     => v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t38_orders_2.p',fc1_struct_0)).

fof(f868,plain,
    ( v2_struct_0(sK0)
    | ~ spl12_118 ),
    inference(avatar_component_clause,[],[f867])).

fof(f784,plain,
    ( spl12_104
    | ~ spl12_12
    | spl12_53 ),
    inference(avatar_split_clause,[],[f778,f445,f221,f782])).

fof(f778,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k2_tarski(sK2,X3) = k7_domain_1(u1_struct_0(sK0),sK2,X3) )
    | ~ spl12_12
    | ~ spl12_53 ),
    inference(subsumption_resolution,[],[f359,f446])).

fof(f359,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k2_tarski(sK2,X3) = k7_domain_1(u1_struct_0(sK0),sK2,X3)
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl12_12 ),
    inference(resolution,[],[f154,f222])).

fof(f154,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | ~ m1_subset_1(X2,X0)
      | k2_tarski(X1,X2) = k7_domain_1(X0,X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X1,X2) = k7_domain_1(X0,X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X1,X2) = k7_domain_1(X0,X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k2_tarski(X1,X2) = k7_domain_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t38_orders_2.p',redefinition_k7_domain_1)).

fof(f761,plain,
    ( spl12_100
    | ~ spl12_10
    | spl12_53 ),
    inference(avatar_split_clause,[],[f752,f445,f214,f759])).

fof(f752,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k2_tarski(sK1,X2) = k7_domain_1(u1_struct_0(sK0),sK1,X2) )
    | ~ spl12_10
    | ~ spl12_53 ),
    inference(subsumption_resolution,[],[f358,f446])).

fof(f358,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k2_tarski(sK1,X2) = k7_domain_1(u1_struct_0(sK0),sK1,X2)
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl12_10 ),
    inference(resolution,[],[f154,f215])).

fof(f690,plain,
    ( spl12_90
    | ~ spl12_86 ),
    inference(avatar_split_clause,[],[f678,f668,f688])).

fof(f678,plain,
    ( v1_relat_1(u1_orders_2(sK0))
    | ~ spl12_86 ),
    inference(resolution,[],[f669,f149])).

fof(f149,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t38_orders_2.p',cc1_relset_1)).

fof(f677,plain,
    ( ~ spl12_65
    | spl12_88
    | ~ spl12_2
    | ~ spl12_20 ),
    inference(avatar_split_clause,[],[f383,f288,f186,f675,f516])).

fof(f516,plain,
    ( spl12_65
  <=> ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_65])])).

fof(f288,plain,
    ( spl12_20
  <=> v6_orders_2(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_20])])).

fof(f383,plain,
    ( r7_relat_2(u1_orders_2(sK0),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl12_2
    | ~ spl12_20 ),
    inference(subsumption_resolution,[],[f382,f187])).

fof(f382,plain,
    ( r7_relat_2(u1_orders_2(sK0),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ spl12_20 ),
    inference(resolution,[],[f289,f130])).

fof(f130,plain,(
    ! [X0,X1] :
      ( ~ v6_orders_2(X1,X0)
      | r7_relat_2(u1_orders_2(X0),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_orders_2(X1,X0)
              | ~ r7_relat_2(u1_orders_2(X0),X1) )
            & ( r7_relat_2(u1_orders_2(X0),X1)
              | ~ v6_orders_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t38_orders_2.p',d11_orders_2)).

fof(f289,plain,
    ( v6_orders_2(sK3,sK0)
    | ~ spl12_20 ),
    inference(avatar_component_clause,[],[f288])).

fof(f670,plain,
    ( spl12_86
    | ~ spl12_2 ),
    inference(avatar_split_clause,[],[f309,f186,f668])).

fof(f309,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl12_2 ),
    inference(resolution,[],[f126,f187])).

fof(f126,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t38_orders_2.p',dt_u1_orders_2)).

fof(f608,plain,
    ( ~ spl12_20
    | ~ spl12_40
    | ~ spl12_42
    | ~ spl12_56
    | ~ spl12_64 ),
    inference(avatar_contradiction_clause,[],[f602])).

fof(f602,plain,
    ( $false
    | ~ spl12_20
    | ~ spl12_40
    | ~ spl12_42
    | ~ spl12_56
    | ~ spl12_64 ),
    inference(unit_resulting_resolution,[],[f389,f289,f472,f520,f380])).

fof(f520,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl12_64 ),
    inference(avatar_component_clause,[],[f519])).

fof(f519,plain,
    ( spl12_64
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_64])])).

fof(f551,plain,
    ( ~ spl12_71
    | ~ spl12_48 ),
    inference(avatar_split_clause,[],[f544,f435,f549])).

fof(f544,plain,
    ( ~ v1_xboole_0(u1_orders_2(sK0))
    | ~ spl12_48 ),
    inference(resolution,[],[f436,f148])).

fof(f521,plain,
    ( spl12_64
    | spl12_23
    | spl12_25 ),
    inference(avatar_split_clause,[],[f514,f297,f291,f519])).

fof(f297,plain,
    ( spl12_25
  <=> ~ r1_orders_2(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_25])])).

fof(f514,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl12_23
    | ~ spl12_25 ),
    inference(subsumption_resolution,[],[f502,f298])).

fof(f298,plain,
    ( ~ r1_orders_2(sK0,sK2,sK1)
    | ~ spl12_25 ),
    inference(avatar_component_clause,[],[f297])).

fof(f502,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl12_23 ),
    inference(subsumption_resolution,[],[f108,f292])).

fof(f108,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | r1_orders_2(sK0,sK1,sK2)
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f81])).

fof(f501,plain,
    ( spl12_62
    | ~ spl12_2
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_24 ),
    inference(avatar_split_clause,[],[f477,f300,f221,f214,f186,f499])).

fof(f477,plain,
    ( r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0))
    | ~ spl12_2
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_24 ),
    inference(subsumption_resolution,[],[f476,f187])).

fof(f476,plain,
    ( r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_24 ),
    inference(subsumption_resolution,[],[f475,f222])).

fof(f475,plain,
    ( r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl12_10
    | ~ spl12_24 ),
    inference(subsumption_resolution,[],[f474,f215])).

fof(f474,plain,
    ( r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl12_24 ),
    inference(resolution,[],[f301,f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f473,plain,
    ( spl12_56
    | spl12_24
    | spl12_23 ),
    inference(avatar_split_clause,[],[f459,f291,f300,f471])).

fof(f459,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | r2_hidden(sK2,sK3)
    | ~ spl12_23 ),
    inference(subsumption_resolution,[],[f110,f292])).

fof(f110,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | r1_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f81])).

fof(f455,plain,
    ( spl12_42
    | spl12_24
    | spl12_23 ),
    inference(avatar_split_clause,[],[f451,f291,f300,f388])).

fof(f451,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | r2_hidden(sK1,sK3)
    | ~ spl12_23 ),
    inference(subsumption_resolution,[],[f109,f292])).

fof(f109,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | r1_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK1,sK3) ),
    inference(cnf_transformation,[],[f81])).

fof(f437,plain,
    ( spl12_48
    | ~ spl12_2
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_22 ),
    inference(avatar_split_clause,[],[f430,f294,f221,f214,f186,f435])).

fof(f430,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ spl12_2
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_22 ),
    inference(subsumption_resolution,[],[f429,f187])).

fof(f429,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_22 ),
    inference(subsumption_resolution,[],[f428,f215])).

fof(f428,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl12_12
    | ~ spl12_22 ),
    inference(subsumption_resolution,[],[f427,f222])).

fof(f427,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl12_22 ),
    inference(resolution,[],[f128,f295])).

fof(f390,plain,
    ( spl12_42
    | spl12_40 ),
    inference(avatar_split_clause,[],[f115,f379,f388])).

fof(f115,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK2,X3)
      | ~ r2_hidden(sK1,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v6_orders_2(X3,sK0)
      | r2_hidden(sK1,sK3) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f381,plain,
    ( spl12_20
    | spl12_40 ),
    inference(avatar_split_clause,[],[f113,f379,f288])).

fof(f113,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK2,X3)
      | ~ r2_hidden(sK1,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v6_orders_2(X3,sK0)
      | v6_orders_2(sK3,sK0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f302,plain,
    ( spl12_20
    | spl12_22
    | spl12_24 ),
    inference(avatar_split_clause,[],[f107,f300,f294,f288])).

fof(f107,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | r1_orders_2(sK0,sK1,sK2)
    | v6_orders_2(sK3,sK0) ),
    inference(cnf_transformation,[],[f81])).

fof(f223,plain,(
    spl12_12 ),
    inference(avatar_split_clause,[],[f106,f221])).

fof(f106,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f81])).

fof(f216,plain,(
    spl12_10 ),
    inference(avatar_split_clause,[],[f105,f214])).

fof(f105,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f81])).

fof(f188,plain,(
    spl12_2 ),
    inference(avatar_split_clause,[],[f104,f186])).

fof(f104,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f81])).

fof(f181,plain,(
    spl12_0 ),
    inference(avatar_split_clause,[],[f103,f179])).

fof(f103,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f81])).
%------------------------------------------------------------------------------
