%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1482+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:21 EST 2020

% Result     : Theorem 4.22s
% Output     : Refutation 4.22s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 589 expanded)
%              Number of leaves         :   13 ( 210 expanded)
%              Depth                    :   38
%              Number of atoms          :  854 (3895 expanded)
%              Number of equality atoms :   31 ( 536 expanded)
%              Maximal formula depth    :   19 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20033,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f19814,f19823,f19832,f19841,f20032])).

fof(f20032,plain,
    ( ~ spl1016_1
    | ~ spl1016_2
    | ~ spl1016_3
    | ~ spl1016_4 ),
    inference(avatar_contradiction_clause,[],[f20031])).

fof(f20031,plain,
    ( $false
    | ~ spl1016_1
    | ~ spl1016_2
    | ~ spl1016_3
    | ~ spl1016_4 ),
    inference(subsumption_resolution,[],[f20030,f9223])).

fof(f9223,plain,(
    v5_orders_2(sK28) ),
    inference(cnf_transformation,[],[f6750])).

fof(f6750,plain,
    ( k11_lattice3(sK28,sK29,sK30) != k11_lattice3(sK28,sK30,sK29)
    & m1_subset_1(sK30,u1_struct_0(sK28))
    & m1_subset_1(sK29,u1_struct_0(sK28))
    & l1_orders_2(sK28)
    & v2_lattice3(sK28)
    & v5_orders_2(sK28) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK28,sK29,sK30])],[f2947,f6749,f6748,f6747])).

fof(f6747,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k11_lattice3(X0,X1,X2) != k11_lattice3(X0,X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k11_lattice3(sK28,X1,X2) != k11_lattice3(sK28,X2,X1)
              & m1_subset_1(X2,u1_struct_0(sK28)) )
          & m1_subset_1(X1,u1_struct_0(sK28)) )
      & l1_orders_2(sK28)
      & v2_lattice3(sK28)
      & v5_orders_2(sK28) ) ),
    introduced(choice_axiom,[])).

fof(f6748,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k11_lattice3(sK28,X1,X2) != k11_lattice3(sK28,X2,X1)
            & m1_subset_1(X2,u1_struct_0(sK28)) )
        & m1_subset_1(X1,u1_struct_0(sK28)) )
   => ( ? [X2] :
          ( k11_lattice3(sK28,sK29,X2) != k11_lattice3(sK28,X2,sK29)
          & m1_subset_1(X2,u1_struct_0(sK28)) )
      & m1_subset_1(sK29,u1_struct_0(sK28)) ) ),
    introduced(choice_axiom,[])).

fof(f6749,plain,
    ( ? [X2] :
        ( k11_lattice3(sK28,sK29,X2) != k11_lattice3(sK28,X2,sK29)
        & m1_subset_1(X2,u1_struct_0(sK28)) )
   => ( k11_lattice3(sK28,sK29,sK30) != k11_lattice3(sK28,sK30,sK29)
      & m1_subset_1(sK30,u1_struct_0(sK28)) ) ),
    introduced(choice_axiom,[])).

fof(f2947,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k11_lattice3(X0,X1,X2) != k11_lattice3(X0,X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f2946])).

fof(f2946,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k11_lattice3(X0,X1,X2) != k11_lattice3(X0,X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2847])).

fof(f2847,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) ) ) ) ),
    inference(negated_conjecture,[],[f2846])).

fof(f2846,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_lattice3)).

fof(f20030,plain,
    ( ~ v5_orders_2(sK28)
    | ~ spl1016_1
    | ~ spl1016_2
    | ~ spl1016_3
    | ~ spl1016_4 ),
    inference(subsumption_resolution,[],[f20029,f9224])).

fof(f9224,plain,(
    v2_lattice3(sK28) ),
    inference(cnf_transformation,[],[f6750])).

fof(f20029,plain,
    ( ~ v2_lattice3(sK28)
    | ~ v5_orders_2(sK28)
    | ~ spl1016_1
    | ~ spl1016_2
    | ~ spl1016_3
    | ~ spl1016_4 ),
    inference(subsumption_resolution,[],[f20028,f9225])).

fof(f9225,plain,(
    l1_orders_2(sK28) ),
    inference(cnf_transformation,[],[f6750])).

fof(f20028,plain,
    ( ~ l1_orders_2(sK28)
    | ~ v2_lattice3(sK28)
    | ~ v5_orders_2(sK28)
    | ~ spl1016_1
    | ~ spl1016_2
    | ~ spl1016_3
    | ~ spl1016_4 ),
    inference(subsumption_resolution,[],[f20027,f9226])).

fof(f9226,plain,(
    m1_subset_1(sK29,u1_struct_0(sK28)) ),
    inference(cnf_transformation,[],[f6750])).

fof(f20027,plain,
    ( ~ m1_subset_1(sK29,u1_struct_0(sK28))
    | ~ l1_orders_2(sK28)
    | ~ v2_lattice3(sK28)
    | ~ v5_orders_2(sK28)
    | ~ spl1016_1
    | ~ spl1016_2
    | ~ spl1016_3
    | ~ spl1016_4 ),
    inference(subsumption_resolution,[],[f20026,f9227])).

fof(f9227,plain,(
    m1_subset_1(sK30,u1_struct_0(sK28)) ),
    inference(cnf_transformation,[],[f6750])).

fof(f20026,plain,
    ( ~ m1_subset_1(sK30,u1_struct_0(sK28))
    | ~ m1_subset_1(sK29,u1_struct_0(sK28))
    | ~ l1_orders_2(sK28)
    | ~ v2_lattice3(sK28)
    | ~ v5_orders_2(sK28)
    | ~ spl1016_1
    | ~ spl1016_2
    | ~ spl1016_3
    | ~ spl1016_4 ),
    inference(subsumption_resolution,[],[f20025,f19804])).

fof(f19804,plain,
    ( m1_subset_1(k11_lattice3(sK28,sK30,sK29),u1_struct_0(sK28))
    | ~ spl1016_2 ),
    inference(avatar_component_clause,[],[f19803])).

fof(f19803,plain,
    ( spl1016_2
  <=> m1_subset_1(k11_lattice3(sK28,sK30,sK29),u1_struct_0(sK28)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1016_2])])).

fof(f20025,plain,
    ( ~ m1_subset_1(k11_lattice3(sK28,sK30,sK29),u1_struct_0(sK28))
    | ~ m1_subset_1(sK30,u1_struct_0(sK28))
    | ~ m1_subset_1(sK29,u1_struct_0(sK28))
    | ~ l1_orders_2(sK28)
    | ~ v2_lattice3(sK28)
    | ~ v5_orders_2(sK28)
    | ~ spl1016_1
    | ~ spl1016_2
    | ~ spl1016_3
    | ~ spl1016_4 ),
    inference(subsumption_resolution,[],[f20024,f19808])).

fof(f19808,plain,
    ( r1_orders_2(sK28,k11_lattice3(sK28,sK30,sK29),sK29)
    | ~ spl1016_3 ),
    inference(avatar_component_clause,[],[f19807])).

fof(f19807,plain,
    ( spl1016_3
  <=> r1_orders_2(sK28,k11_lattice3(sK28,sK30,sK29),sK29) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1016_3])])).

fof(f20024,plain,
    ( ~ r1_orders_2(sK28,k11_lattice3(sK28,sK30,sK29),sK29)
    | ~ m1_subset_1(k11_lattice3(sK28,sK30,sK29),u1_struct_0(sK28))
    | ~ m1_subset_1(sK30,u1_struct_0(sK28))
    | ~ m1_subset_1(sK29,u1_struct_0(sK28))
    | ~ l1_orders_2(sK28)
    | ~ v2_lattice3(sK28)
    | ~ v5_orders_2(sK28)
    | ~ spl1016_1
    | ~ spl1016_2
    | ~ spl1016_3
    | ~ spl1016_4 ),
    inference(subsumption_resolution,[],[f20023,f19812])).

fof(f19812,plain,
    ( r1_orders_2(sK28,k11_lattice3(sK28,sK30,sK29),sK30)
    | ~ spl1016_4 ),
    inference(avatar_component_clause,[],[f19811])).

fof(f19811,plain,
    ( spl1016_4
  <=> r1_orders_2(sK28,k11_lattice3(sK28,sK30,sK29),sK30) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1016_4])])).

fof(f20023,plain,
    ( ~ r1_orders_2(sK28,k11_lattice3(sK28,sK30,sK29),sK30)
    | ~ r1_orders_2(sK28,k11_lattice3(sK28,sK30,sK29),sK29)
    | ~ m1_subset_1(k11_lattice3(sK28,sK30,sK29),u1_struct_0(sK28))
    | ~ m1_subset_1(sK30,u1_struct_0(sK28))
    | ~ m1_subset_1(sK29,u1_struct_0(sK28))
    | ~ l1_orders_2(sK28)
    | ~ v2_lattice3(sK28)
    | ~ v5_orders_2(sK28)
    | ~ spl1016_1
    | ~ spl1016_2
    | ~ spl1016_3
    | ~ spl1016_4 ),
    inference(subsumption_resolution,[],[f20019,f15904])).

fof(f15904,plain,(
    ~ sQ1015_eqProxy(k11_lattice3(sK28,sK29,sK30),k11_lattice3(sK28,sK30,sK29)) ),
    inference(equality_proxy_replacement,[],[f9228,f15870])).

fof(f15870,plain,(
    ! [X1,X0] :
      ( sQ1015_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ1015_eqProxy])])).

fof(f9228,plain,(
    k11_lattice3(sK28,sK29,sK30) != k11_lattice3(sK28,sK30,sK29) ),
    inference(cnf_transformation,[],[f6750])).

fof(f20019,plain,
    ( sQ1015_eqProxy(k11_lattice3(sK28,sK29,sK30),k11_lattice3(sK28,sK30,sK29))
    | ~ r1_orders_2(sK28,k11_lattice3(sK28,sK30,sK29),sK30)
    | ~ r1_orders_2(sK28,k11_lattice3(sK28,sK30,sK29),sK29)
    | ~ m1_subset_1(k11_lattice3(sK28,sK30,sK29),u1_struct_0(sK28))
    | ~ m1_subset_1(sK30,u1_struct_0(sK28))
    | ~ m1_subset_1(sK29,u1_struct_0(sK28))
    | ~ l1_orders_2(sK28)
    | ~ v2_lattice3(sK28)
    | ~ v5_orders_2(sK28)
    | ~ spl1016_1
    | ~ spl1016_2
    | ~ spl1016_3
    | ~ spl1016_4 ),
    inference(resolution,[],[f19960,f19693])).

fof(f19693,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK268(X0,X1,X2,X3),u1_struct_0(X0))
      | sQ1015_eqProxy(k11_lattice3(X0,X1,X2),X3)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f16401,f9751])).

fof(f9751,plain,(
    ! [X0] :
      ( ~ v2_lattice3(X0)
      | ~ v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3202])).

fof(f3202,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3201])).

fof(f3201,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2807])).

fof(f2807,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

fof(f16401,plain,(
    ! [X2,X0,X3,X1] :
      ( sQ1015_eqProxy(k11_lattice3(X0,X1,X2),X3)
      | m1_subset_1(sK268(X0,X1,X2,X3),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f10799,f15870])).

fof(f10799,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X0,X1,X2) = X3
      | m1_subset_1(sK268(X0,X1,X2,X3),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f7418])).

fof(f7418,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,sK268(X0,X1,X2,X3),X3)
                        & r1_orders_2(X0,sK268(X0,X1,X2,X3),X2)
                        & r1_orders_2(X0,sK268(X0,X1,X2,X3),X1)
                        & m1_subset_1(sK268(X0,X1,X2,X3),u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK268])],[f7416,f7417])).

fof(f7417,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X2)
          & r1_orders_2(X0,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK268(X0,X1,X2,X3),X3)
        & r1_orders_2(X0,sK268(X0,X1,X2,X3),X2)
        & r1_orders_2(X0,sK268(X0,X1,X2,X3),X1)
        & m1_subset_1(sK268(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f7416,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f7415])).

fof(f7415,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X4,X3)
                            | ~ r1_orders_2(X0,X4,X2)
                            | ~ r1_orders_2(X0,X4,X1)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f7414])).

fof(f7414,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X4,X3)
                            | ~ r1_orders_2(X0,X4,X2)
                            | ~ r1_orders_2(X0,X4,X1)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3920])).

fof(f3920,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k11_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3919])).

fof(f3919,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k11_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2838])).

fof(f2838,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k11_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X4,X2)
                              & r1_orders_2(X0,X4,X1) )
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l28_lattice3)).

fof(f19960,plain,
    ( ~ m1_subset_1(sK268(sK28,sK29,sK30,k11_lattice3(sK28,sK30,sK29)),u1_struct_0(sK28))
    | ~ spl1016_1
    | ~ spl1016_2
    | ~ spl1016_3
    | ~ spl1016_4 ),
    inference(subsumption_resolution,[],[f19959,f19804])).

fof(f19959,plain,
    ( ~ m1_subset_1(sK268(sK28,sK29,sK30,k11_lattice3(sK28,sK30,sK29)),u1_struct_0(sK28))
    | ~ m1_subset_1(k11_lattice3(sK28,sK30,sK29),u1_struct_0(sK28))
    | ~ spl1016_1
    | ~ spl1016_2
    | ~ spl1016_3
    | ~ spl1016_4 ),
    inference(subsumption_resolution,[],[f19958,f19808])).

fof(f19958,plain,
    ( ~ m1_subset_1(sK268(sK28,sK29,sK30,k11_lattice3(sK28,sK30,sK29)),u1_struct_0(sK28))
    | ~ r1_orders_2(sK28,k11_lattice3(sK28,sK30,sK29),sK29)
    | ~ m1_subset_1(k11_lattice3(sK28,sK30,sK29),u1_struct_0(sK28))
    | ~ spl1016_1
    | ~ spl1016_2
    | ~ spl1016_3
    | ~ spl1016_4 ),
    inference(subsumption_resolution,[],[f19957,f19812])).

fof(f19957,plain,
    ( ~ m1_subset_1(sK268(sK28,sK29,sK30,k11_lattice3(sK28,sK30,sK29)),u1_struct_0(sK28))
    | ~ r1_orders_2(sK28,k11_lattice3(sK28,sK30,sK29),sK30)
    | ~ r1_orders_2(sK28,k11_lattice3(sK28,sK30,sK29),sK29)
    | ~ m1_subset_1(k11_lattice3(sK28,sK30,sK29),u1_struct_0(sK28))
    | ~ spl1016_1
    | ~ spl1016_2
    | ~ spl1016_3
    | ~ spl1016_4 ),
    inference(subsumption_resolution,[],[f19956,f19801])).

fof(f19801,plain,
    ( r1_orders_2(sK28,sK268(sK28,sK29,sK30,k11_lattice3(sK28,sK30,sK29)),sK30)
    | ~ spl1016_1 ),
    inference(avatar_component_clause,[],[f19799])).

fof(f19799,plain,
    ( spl1016_1
  <=> r1_orders_2(sK28,sK268(sK28,sK29,sK30,k11_lattice3(sK28,sK30,sK29)),sK30) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1016_1])])).

fof(f19956,plain,
    ( ~ m1_subset_1(sK268(sK28,sK29,sK30,k11_lattice3(sK28,sK30,sK29)),u1_struct_0(sK28))
    | ~ r1_orders_2(sK28,sK268(sK28,sK29,sK30,k11_lattice3(sK28,sK30,sK29)),sK30)
    | ~ r1_orders_2(sK28,k11_lattice3(sK28,sK30,sK29),sK30)
    | ~ r1_orders_2(sK28,k11_lattice3(sK28,sK30,sK29),sK29)
    | ~ m1_subset_1(k11_lattice3(sK28,sK30,sK29),u1_struct_0(sK28))
    | ~ spl1016_2
    | ~ spl1016_3
    | ~ spl1016_4 ),
    inference(subsumption_resolution,[],[f19955,f19850])).

fof(f19850,plain,
    ( r1_orders_2(sK28,sK268(sK28,sK29,sK30,k11_lattice3(sK28,sK30,sK29)),sK29)
    | ~ spl1016_2
    | ~ spl1016_3
    | ~ spl1016_4 ),
    inference(subsumption_resolution,[],[f19849,f19804])).

fof(f19849,plain,
    ( ~ m1_subset_1(k11_lattice3(sK28,sK30,sK29),u1_struct_0(sK28))
    | r1_orders_2(sK28,sK268(sK28,sK29,sK30,k11_lattice3(sK28,sK30,sK29)),sK29)
    | ~ spl1016_3
    | ~ spl1016_4 ),
    inference(subsumption_resolution,[],[f19848,f19808])).

fof(f19848,plain,
    ( ~ r1_orders_2(sK28,k11_lattice3(sK28,sK30,sK29),sK29)
    | ~ m1_subset_1(k11_lattice3(sK28,sK30,sK29),u1_struct_0(sK28))
    | r1_orders_2(sK28,sK268(sK28,sK29,sK30,k11_lattice3(sK28,sK30,sK29)),sK29)
    | ~ spl1016_4 ),
    inference(subsumption_resolution,[],[f19709,f19812])).

fof(f19709,plain,
    ( ~ r1_orders_2(sK28,k11_lattice3(sK28,sK30,sK29),sK30)
    | ~ r1_orders_2(sK28,k11_lattice3(sK28,sK30,sK29),sK29)
    | ~ m1_subset_1(k11_lattice3(sK28,sK30,sK29),u1_struct_0(sK28))
    | r1_orders_2(sK28,sK268(sK28,sK29,sK30,k11_lattice3(sK28,sK30,sK29)),sK29) ),
    inference(subsumption_resolution,[],[f19708,f9226])).

fof(f19708,plain,
    ( ~ r1_orders_2(sK28,k11_lattice3(sK28,sK30,sK29),sK30)
    | ~ r1_orders_2(sK28,k11_lattice3(sK28,sK30,sK29),sK29)
    | ~ m1_subset_1(k11_lattice3(sK28,sK30,sK29),u1_struct_0(sK28))
    | ~ m1_subset_1(sK29,u1_struct_0(sK28))
    | r1_orders_2(sK28,sK268(sK28,sK29,sK30,k11_lattice3(sK28,sK30,sK29)),sK29) ),
    inference(subsumption_resolution,[],[f19707,f9227])).

fof(f19707,plain,
    ( ~ r1_orders_2(sK28,k11_lattice3(sK28,sK30,sK29),sK30)
    | ~ r1_orders_2(sK28,k11_lattice3(sK28,sK30,sK29),sK29)
    | ~ m1_subset_1(k11_lattice3(sK28,sK30,sK29),u1_struct_0(sK28))
    | ~ m1_subset_1(sK30,u1_struct_0(sK28))
    | ~ m1_subset_1(sK29,u1_struct_0(sK28))
    | r1_orders_2(sK28,sK268(sK28,sK29,sK30,k11_lattice3(sK28,sK30,sK29)),sK29) ),
    inference(resolution,[],[f19692,f15904])).

fof(f19692,plain,(
    ! [X2,X0,X1] :
      ( sQ1015_eqProxy(k11_lattice3(sK28,X0,X1),X2)
      | ~ r1_orders_2(sK28,X2,X1)
      | ~ r1_orders_2(sK28,X2,X0)
      | ~ m1_subset_1(X2,u1_struct_0(sK28))
      | ~ m1_subset_1(X1,u1_struct_0(sK28))
      | ~ m1_subset_1(X0,u1_struct_0(sK28))
      | r1_orders_2(sK28,sK268(sK28,X0,X1,X2),X0) ) ),
    inference(subsumption_resolution,[],[f19691,f9223])).

fof(f19691,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(sK28,sK268(sK28,X0,X1,X2),X0)
      | ~ r1_orders_2(sK28,X2,X1)
      | ~ r1_orders_2(sK28,X2,X0)
      | ~ m1_subset_1(X2,u1_struct_0(sK28))
      | ~ m1_subset_1(X1,u1_struct_0(sK28))
      | ~ m1_subset_1(X0,u1_struct_0(sK28))
      | sQ1015_eqProxy(k11_lattice3(sK28,X0,X1),X2)
      | ~ v5_orders_2(sK28) ) ),
    inference(subsumption_resolution,[],[f19690,f9225])).

fof(f19690,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(sK28,sK268(sK28,X0,X1,X2),X0)
      | ~ r1_orders_2(sK28,X2,X1)
      | ~ r1_orders_2(sK28,X2,X0)
      | ~ m1_subset_1(X2,u1_struct_0(sK28))
      | ~ m1_subset_1(X1,u1_struct_0(sK28))
      | ~ m1_subset_1(X0,u1_struct_0(sK28))
      | ~ l1_orders_2(sK28)
      | sQ1015_eqProxy(k11_lattice3(sK28,X0,X1),X2)
      | ~ v5_orders_2(sK28) ) ),
    inference(resolution,[],[f19689,f9224])).

fof(f19689,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_lattice3(X0)
      | r1_orders_2(X0,sK268(X0,X1,X2,X3),X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | sQ1015_eqProxy(k11_lattice3(X0,X1,X2),X3)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f16400,f9751])).

fof(f16400,plain,(
    ! [X2,X0,X3,X1] :
      ( sQ1015_eqProxy(k11_lattice3(X0,X1,X2),X3)
      | r1_orders_2(X0,sK268(X0,X1,X2,X3),X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f10800,f15870])).

fof(f10800,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X0,X1,X2) = X3
      | r1_orders_2(X0,sK268(X0,X1,X2,X3),X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f7418])).

fof(f19955,plain,
    ( ~ m1_subset_1(sK268(sK28,sK29,sK30,k11_lattice3(sK28,sK30,sK29)),u1_struct_0(sK28))
    | ~ r1_orders_2(sK28,sK268(sK28,sK29,sK30,k11_lattice3(sK28,sK30,sK29)),sK29)
    | ~ r1_orders_2(sK28,sK268(sK28,sK29,sK30,k11_lattice3(sK28,sK30,sK29)),sK30)
    | ~ r1_orders_2(sK28,k11_lattice3(sK28,sK30,sK29),sK30)
    | ~ r1_orders_2(sK28,k11_lattice3(sK28,sK30,sK29),sK29)
    | ~ m1_subset_1(k11_lattice3(sK28,sK30,sK29),u1_struct_0(sK28)) ),
    inference(subsumption_resolution,[],[f19954,f9227])).

fof(f19954,plain,
    ( ~ m1_subset_1(sK268(sK28,sK29,sK30,k11_lattice3(sK28,sK30,sK29)),u1_struct_0(sK28))
    | ~ m1_subset_1(sK30,u1_struct_0(sK28))
    | ~ r1_orders_2(sK28,sK268(sK28,sK29,sK30,k11_lattice3(sK28,sK30,sK29)),sK29)
    | ~ r1_orders_2(sK28,sK268(sK28,sK29,sK30,k11_lattice3(sK28,sK30,sK29)),sK30)
    | ~ r1_orders_2(sK28,k11_lattice3(sK28,sK30,sK29),sK30)
    | ~ r1_orders_2(sK28,k11_lattice3(sK28,sK30,sK29),sK29)
    | ~ m1_subset_1(k11_lattice3(sK28,sK30,sK29),u1_struct_0(sK28)) ),
    inference(subsumption_resolution,[],[f19953,f9226])).

fof(f19953,plain,
    ( ~ m1_subset_1(sK268(sK28,sK29,sK30,k11_lattice3(sK28,sK30,sK29)),u1_struct_0(sK28))
    | ~ m1_subset_1(sK29,u1_struct_0(sK28))
    | ~ m1_subset_1(sK30,u1_struct_0(sK28))
    | ~ r1_orders_2(sK28,sK268(sK28,sK29,sK30,k11_lattice3(sK28,sK30,sK29)),sK29)
    | ~ r1_orders_2(sK28,sK268(sK28,sK29,sK30,k11_lattice3(sK28,sK30,sK29)),sK30)
    | ~ r1_orders_2(sK28,k11_lattice3(sK28,sK30,sK29),sK30)
    | ~ r1_orders_2(sK28,k11_lattice3(sK28,sK30,sK29),sK29)
    | ~ m1_subset_1(k11_lattice3(sK28,sK30,sK29),u1_struct_0(sK28)) ),
    inference(duplicate_literal_removal,[],[f19952])).

fof(f19952,plain,
    ( ~ m1_subset_1(sK268(sK28,sK29,sK30,k11_lattice3(sK28,sK30,sK29)),u1_struct_0(sK28))
    | ~ m1_subset_1(sK29,u1_struct_0(sK28))
    | ~ m1_subset_1(sK30,u1_struct_0(sK28))
    | ~ r1_orders_2(sK28,sK268(sK28,sK29,sK30,k11_lattice3(sK28,sK30,sK29)),sK29)
    | ~ r1_orders_2(sK28,sK268(sK28,sK29,sK30,k11_lattice3(sK28,sK30,sK29)),sK30)
    | ~ r1_orders_2(sK28,k11_lattice3(sK28,sK30,sK29),sK30)
    | ~ r1_orders_2(sK28,k11_lattice3(sK28,sK30,sK29),sK29)
    | ~ m1_subset_1(k11_lattice3(sK28,sK30,sK29),u1_struct_0(sK28))
    | ~ m1_subset_1(sK30,u1_struct_0(sK28))
    | ~ m1_subset_1(sK29,u1_struct_0(sK28)) ),
    inference(resolution,[],[f19703,f15904])).

fof(f19703,plain,(
    ! [X4,X2,X5,X3] :
      ( sQ1015_eqProxy(k11_lattice3(sK28,X2,X3),k11_lattice3(sK28,X4,X5))
      | ~ m1_subset_1(sK268(sK28,X2,X3,k11_lattice3(sK28,X4,X5)),u1_struct_0(sK28))
      | ~ m1_subset_1(X5,u1_struct_0(sK28))
      | ~ m1_subset_1(X4,u1_struct_0(sK28))
      | ~ r1_orders_2(sK28,sK268(sK28,X2,X3,k11_lattice3(sK28,X4,X5)),X5)
      | ~ r1_orders_2(sK28,sK268(sK28,X2,X3,k11_lattice3(sK28,X4,X5)),X4)
      | ~ r1_orders_2(sK28,k11_lattice3(sK28,X4,X5),X3)
      | ~ r1_orders_2(sK28,k11_lattice3(sK28,X4,X5),X2)
      | ~ m1_subset_1(k11_lattice3(sK28,X4,X5),u1_struct_0(sK28))
      | ~ m1_subset_1(X3,u1_struct_0(sK28))
      | ~ m1_subset_1(X2,u1_struct_0(sK28)) ) ),
    inference(subsumption_resolution,[],[f19702,f9223])).

fof(f19702,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ r1_orders_2(sK28,sK268(sK28,X2,X3,k11_lattice3(sK28,X4,X5)),X4)
      | ~ m1_subset_1(sK268(sK28,X2,X3,k11_lattice3(sK28,X4,X5)),u1_struct_0(sK28))
      | ~ m1_subset_1(X5,u1_struct_0(sK28))
      | ~ m1_subset_1(X4,u1_struct_0(sK28))
      | ~ r1_orders_2(sK28,sK268(sK28,X2,X3,k11_lattice3(sK28,X4,X5)),X5)
      | sQ1015_eqProxy(k11_lattice3(sK28,X2,X3),k11_lattice3(sK28,X4,X5))
      | ~ r1_orders_2(sK28,k11_lattice3(sK28,X4,X5),X3)
      | ~ r1_orders_2(sK28,k11_lattice3(sK28,X4,X5),X2)
      | ~ m1_subset_1(k11_lattice3(sK28,X4,X5),u1_struct_0(sK28))
      | ~ m1_subset_1(X3,u1_struct_0(sK28))
      | ~ m1_subset_1(X2,u1_struct_0(sK28))
      | ~ v5_orders_2(sK28) ) ),
    inference(subsumption_resolution,[],[f19701,f9224])).

fof(f19701,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ r1_orders_2(sK28,sK268(sK28,X2,X3,k11_lattice3(sK28,X4,X5)),X4)
      | ~ m1_subset_1(sK268(sK28,X2,X3,k11_lattice3(sK28,X4,X5)),u1_struct_0(sK28))
      | ~ m1_subset_1(X5,u1_struct_0(sK28))
      | ~ m1_subset_1(X4,u1_struct_0(sK28))
      | ~ r1_orders_2(sK28,sK268(sK28,X2,X3,k11_lattice3(sK28,X4,X5)),X5)
      | sQ1015_eqProxy(k11_lattice3(sK28,X2,X3),k11_lattice3(sK28,X4,X5))
      | ~ r1_orders_2(sK28,k11_lattice3(sK28,X4,X5),X3)
      | ~ r1_orders_2(sK28,k11_lattice3(sK28,X4,X5),X2)
      | ~ m1_subset_1(k11_lattice3(sK28,X4,X5),u1_struct_0(sK28))
      | ~ m1_subset_1(X3,u1_struct_0(sK28))
      | ~ m1_subset_1(X2,u1_struct_0(sK28))
      | ~ v2_lattice3(sK28)
      | ~ v5_orders_2(sK28) ) ),
    inference(subsumption_resolution,[],[f19700,f9225])).

fof(f19700,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ r1_orders_2(sK28,sK268(sK28,X2,X3,k11_lattice3(sK28,X4,X5)),X4)
      | ~ m1_subset_1(sK268(sK28,X2,X3,k11_lattice3(sK28,X4,X5)),u1_struct_0(sK28))
      | ~ m1_subset_1(X5,u1_struct_0(sK28))
      | ~ m1_subset_1(X4,u1_struct_0(sK28))
      | ~ r1_orders_2(sK28,sK268(sK28,X2,X3,k11_lattice3(sK28,X4,X5)),X5)
      | sQ1015_eqProxy(k11_lattice3(sK28,X2,X3),k11_lattice3(sK28,X4,X5))
      | ~ r1_orders_2(sK28,k11_lattice3(sK28,X4,X5),X3)
      | ~ r1_orders_2(sK28,k11_lattice3(sK28,X4,X5),X2)
      | ~ m1_subset_1(k11_lattice3(sK28,X4,X5),u1_struct_0(sK28))
      | ~ m1_subset_1(X3,u1_struct_0(sK28))
      | ~ m1_subset_1(X2,u1_struct_0(sK28))
      | ~ l1_orders_2(sK28)
      | ~ v2_lattice3(sK28)
      | ~ v5_orders_2(sK28) ) ),
    inference(resolution,[],[f19683,f19684])).

fof(f19684,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK268(X0,X1,X2,X3),X3)
      | sQ1015_eqProxy(k11_lattice3(X0,X1,X2),X3)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f16398,f9751])).

fof(f16398,plain,(
    ! [X2,X0,X3,X1] :
      ( sQ1015_eqProxy(k11_lattice3(X0,X1,X2),X3)
      | ~ r1_orders_2(X0,sK268(X0,X1,X2,X3),X3)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f10802,f15870])).

fof(f10802,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,sK268(X0,X1,X2,X3),X3)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f7418])).

fof(f19683,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(sK28,X0,k11_lattice3(sK28,X2,X1))
      | ~ r1_orders_2(sK28,X0,X2)
      | ~ m1_subset_1(X0,u1_struct_0(sK28))
      | ~ m1_subset_1(X1,u1_struct_0(sK28))
      | ~ m1_subset_1(X2,u1_struct_0(sK28))
      | ~ r1_orders_2(sK28,X0,X1) ) ),
    inference(subsumption_resolution,[],[f19682,f9223])).

fof(f19682,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(sK28,X0,X1)
      | ~ r1_orders_2(sK28,X0,X2)
      | ~ m1_subset_1(X0,u1_struct_0(sK28))
      | ~ m1_subset_1(X1,u1_struct_0(sK28))
      | ~ m1_subset_1(X2,u1_struct_0(sK28))
      | r1_orders_2(sK28,X0,k11_lattice3(sK28,X2,X1))
      | ~ v5_orders_2(sK28) ) ),
    inference(subsumption_resolution,[],[f19681,f9225])).

fof(f19681,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(sK28,X0,X1)
      | ~ r1_orders_2(sK28,X0,X2)
      | ~ m1_subset_1(X0,u1_struct_0(sK28))
      | ~ m1_subset_1(X1,u1_struct_0(sK28))
      | ~ m1_subset_1(X2,u1_struct_0(sK28))
      | ~ l1_orders_2(sK28)
      | r1_orders_2(sK28,X0,k11_lattice3(sK28,X2,X1))
      | ~ v5_orders_2(sK28) ) ),
    inference(resolution,[],[f19680,f9224])).

fof(f19680,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ v2_lattice3(X0)
      | ~ r1_orders_2(X0,X5,X2)
      | ~ r1_orders_2(X0,X5,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X5,k11_lattice3(X0,X1,X2))
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f19679,f13753])).

fof(f13753,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f6013])).

fof(f6013,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f6012])).

fof(f6012,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2822])).

fof(f2822,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_lattice3)).

fof(f19679,plain,(
    ! [X2,X0,X5,X1] :
      ( r1_orders_2(X0,X5,k11_lattice3(X0,X1,X2))
      | ~ r1_orders_2(X0,X5,X2)
      | ~ r1_orders_2(X0,X5,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f15344,f9751])).

fof(f15344,plain,(
    ! [X2,X0,X5,X1] :
      ( r1_orders_2(X0,X5,k11_lattice3(X0,X1,X2))
      | ~ r1_orders_2(X0,X5,X2)
      | ~ r1_orders_2(X0,X5,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f10798])).

fof(f10798,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_orders_2(X0,X5,X3)
      | ~ r1_orders_2(X0,X5,X2)
      | ~ r1_orders_2(X0,X5,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | k11_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f7418])).

fof(f19841,plain,(
    spl1016_4 ),
    inference(avatar_contradiction_clause,[],[f19840])).

fof(f19840,plain,
    ( $false
    | spl1016_4 ),
    inference(subsumption_resolution,[],[f19839,f9223])).

fof(f19839,plain,
    ( ~ v5_orders_2(sK28)
    | spl1016_4 ),
    inference(subsumption_resolution,[],[f19838,f9224])).

fof(f19838,plain,
    ( ~ v2_lattice3(sK28)
    | ~ v5_orders_2(sK28)
    | spl1016_4 ),
    inference(subsumption_resolution,[],[f19837,f9225])).

fof(f19837,plain,
    ( ~ l1_orders_2(sK28)
    | ~ v2_lattice3(sK28)
    | ~ v5_orders_2(sK28)
    | spl1016_4 ),
    inference(subsumption_resolution,[],[f19836,f9227])).

fof(f19836,plain,
    ( ~ m1_subset_1(sK30,u1_struct_0(sK28))
    | ~ l1_orders_2(sK28)
    | ~ v2_lattice3(sK28)
    | ~ v5_orders_2(sK28)
    | spl1016_4 ),
    inference(subsumption_resolution,[],[f19834,f9226])).

fof(f19834,plain,
    ( ~ m1_subset_1(sK29,u1_struct_0(sK28))
    | ~ m1_subset_1(sK30,u1_struct_0(sK28))
    | ~ l1_orders_2(sK28)
    | ~ v2_lattice3(sK28)
    | ~ v5_orders_2(sK28)
    | spl1016_4 ),
    inference(resolution,[],[f19813,f19676])).

fof(f19676,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f19675,f13753])).

fof(f19675,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f15346,f9751])).

fof(f15346,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f10796])).

fof(f10796,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X1)
      | k11_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f7418])).

fof(f19813,plain,
    ( ~ r1_orders_2(sK28,k11_lattice3(sK28,sK30,sK29),sK30)
    | spl1016_4 ),
    inference(avatar_component_clause,[],[f19811])).

fof(f19832,plain,(
    spl1016_3 ),
    inference(avatar_contradiction_clause,[],[f19831])).

fof(f19831,plain,
    ( $false
    | spl1016_3 ),
    inference(subsumption_resolution,[],[f19830,f9223])).

fof(f19830,plain,
    ( ~ v5_orders_2(sK28)
    | spl1016_3 ),
    inference(subsumption_resolution,[],[f19829,f9224])).

fof(f19829,plain,
    ( ~ v2_lattice3(sK28)
    | ~ v5_orders_2(sK28)
    | spl1016_3 ),
    inference(subsumption_resolution,[],[f19828,f9225])).

fof(f19828,plain,
    ( ~ l1_orders_2(sK28)
    | ~ v2_lattice3(sK28)
    | ~ v5_orders_2(sK28)
    | spl1016_3 ),
    inference(subsumption_resolution,[],[f19827,f9227])).

fof(f19827,plain,
    ( ~ m1_subset_1(sK30,u1_struct_0(sK28))
    | ~ l1_orders_2(sK28)
    | ~ v2_lattice3(sK28)
    | ~ v5_orders_2(sK28)
    | spl1016_3 ),
    inference(subsumption_resolution,[],[f19825,f9226])).

fof(f19825,plain,
    ( ~ m1_subset_1(sK29,u1_struct_0(sK28))
    | ~ m1_subset_1(sK30,u1_struct_0(sK28))
    | ~ l1_orders_2(sK28)
    | ~ v2_lattice3(sK28)
    | ~ v5_orders_2(sK28)
    | spl1016_3 ),
    inference(resolution,[],[f19809,f19674])).

fof(f19674,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f19673,f13753])).

fof(f19673,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f15345,f9751])).

fof(f15345,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f10797])).

fof(f10797,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X2)
      | k11_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f7418])).

fof(f19809,plain,
    ( ~ r1_orders_2(sK28,k11_lattice3(sK28,sK30,sK29),sK29)
    | spl1016_3 ),
    inference(avatar_component_clause,[],[f19807])).

fof(f19823,plain,(
    spl1016_2 ),
    inference(avatar_contradiction_clause,[],[f19822])).

fof(f19822,plain,
    ( $false
    | spl1016_2 ),
    inference(subsumption_resolution,[],[f19821,f9225])).

fof(f19821,plain,
    ( ~ l1_orders_2(sK28)
    | spl1016_2 ),
    inference(subsumption_resolution,[],[f19820,f9227])).

fof(f19820,plain,
    ( ~ m1_subset_1(sK30,u1_struct_0(sK28))
    | ~ l1_orders_2(sK28)
    | spl1016_2 ),
    inference(subsumption_resolution,[],[f19816,f9226])).

fof(f19816,plain,
    ( ~ m1_subset_1(sK29,u1_struct_0(sK28))
    | ~ m1_subset_1(sK30,u1_struct_0(sK28))
    | ~ l1_orders_2(sK28)
    | spl1016_2 ),
    inference(resolution,[],[f19805,f13753])).

fof(f19805,plain,
    ( ~ m1_subset_1(k11_lattice3(sK28,sK30,sK29),u1_struct_0(sK28))
    | spl1016_2 ),
    inference(avatar_component_clause,[],[f19803])).

fof(f19814,plain,
    ( spl1016_1
    | ~ spl1016_2
    | ~ spl1016_3
    | ~ spl1016_4 ),
    inference(avatar_split_clause,[],[f19706,f19811,f19807,f19803,f19799])).

fof(f19706,plain,
    ( ~ r1_orders_2(sK28,k11_lattice3(sK28,sK30,sK29),sK30)
    | ~ r1_orders_2(sK28,k11_lattice3(sK28,sK30,sK29),sK29)
    | ~ m1_subset_1(k11_lattice3(sK28,sK30,sK29),u1_struct_0(sK28))
    | r1_orders_2(sK28,sK268(sK28,sK29,sK30,k11_lattice3(sK28,sK30,sK29)),sK30) ),
    inference(subsumption_resolution,[],[f19705,f9226])).

fof(f19705,plain,
    ( ~ r1_orders_2(sK28,k11_lattice3(sK28,sK30,sK29),sK30)
    | ~ r1_orders_2(sK28,k11_lattice3(sK28,sK30,sK29),sK29)
    | ~ m1_subset_1(k11_lattice3(sK28,sK30,sK29),u1_struct_0(sK28))
    | ~ m1_subset_1(sK29,u1_struct_0(sK28))
    | r1_orders_2(sK28,sK268(sK28,sK29,sK30,k11_lattice3(sK28,sK30,sK29)),sK30) ),
    inference(subsumption_resolution,[],[f19704,f9227])).

fof(f19704,plain,
    ( ~ r1_orders_2(sK28,k11_lattice3(sK28,sK30,sK29),sK30)
    | ~ r1_orders_2(sK28,k11_lattice3(sK28,sK30,sK29),sK29)
    | ~ m1_subset_1(k11_lattice3(sK28,sK30,sK29),u1_struct_0(sK28))
    | ~ m1_subset_1(sK30,u1_struct_0(sK28))
    | ~ m1_subset_1(sK29,u1_struct_0(sK28))
    | r1_orders_2(sK28,sK268(sK28,sK29,sK30,k11_lattice3(sK28,sK30,sK29)),sK30) ),
    inference(resolution,[],[f19688,f15904])).

fof(f19688,plain,(
    ! [X2,X0,X1] :
      ( sQ1015_eqProxy(k11_lattice3(sK28,X0,X1),X2)
      | ~ r1_orders_2(sK28,X2,X1)
      | ~ r1_orders_2(sK28,X2,X0)
      | ~ m1_subset_1(X2,u1_struct_0(sK28))
      | ~ m1_subset_1(X1,u1_struct_0(sK28))
      | ~ m1_subset_1(X0,u1_struct_0(sK28))
      | r1_orders_2(sK28,sK268(sK28,X0,X1,X2),X1) ) ),
    inference(subsumption_resolution,[],[f19687,f9223])).

fof(f19687,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(sK28,sK268(sK28,X0,X1,X2),X1)
      | ~ r1_orders_2(sK28,X2,X1)
      | ~ r1_orders_2(sK28,X2,X0)
      | ~ m1_subset_1(X2,u1_struct_0(sK28))
      | ~ m1_subset_1(X1,u1_struct_0(sK28))
      | ~ m1_subset_1(X0,u1_struct_0(sK28))
      | sQ1015_eqProxy(k11_lattice3(sK28,X0,X1),X2)
      | ~ v5_orders_2(sK28) ) ),
    inference(subsumption_resolution,[],[f19686,f9225])).

fof(f19686,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(sK28,sK268(sK28,X0,X1,X2),X1)
      | ~ r1_orders_2(sK28,X2,X1)
      | ~ r1_orders_2(sK28,X2,X0)
      | ~ m1_subset_1(X2,u1_struct_0(sK28))
      | ~ m1_subset_1(X1,u1_struct_0(sK28))
      | ~ m1_subset_1(X0,u1_struct_0(sK28))
      | ~ l1_orders_2(sK28)
      | sQ1015_eqProxy(k11_lattice3(sK28,X0,X1),X2)
      | ~ v5_orders_2(sK28) ) ),
    inference(resolution,[],[f19685,f9224])).

fof(f19685,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_lattice3(X0)
      | r1_orders_2(X0,sK268(X0,X1,X2,X3),X2)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | sQ1015_eqProxy(k11_lattice3(X0,X1,X2),X3)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f16399,f9751])).

fof(f16399,plain,(
    ! [X2,X0,X3,X1] :
      ( sQ1015_eqProxy(k11_lattice3(X0,X1,X2),X3)
      | r1_orders_2(X0,sK268(X0,X1,X2,X3),X2)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f10801,f15870])).

fof(f10801,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X0,X1,X2) = X3
      | r1_orders_2(X0,sK268(X0,X1,X2,X3),X2)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f7418])).
%------------------------------------------------------------------------------
