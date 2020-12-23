%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_0__t71_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:48 EDT 2019

% Result     : Theorem 169.61s
% Output     : Refutation 169.61s
% Verified   : 
% Statistics : Number of formulae       :  153 (1835 expanded)
%              Number of leaves         :   28 ( 953 expanded)
%              Depth                    :   23
%              Number of atoms          :  793 (24035 expanded)
%              Number of equality atoms :   90 (6625 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2142928,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2142708,f632])).

fof(f632,plain,(
    k13_lattice3(sK2,sK4,sK5) != k13_lattice3(sK3,sK4,sK5) ),
    inference(forward_demodulation,[],[f631,f139])).

fof(f139,plain,(
    sK4 = sK6 ),
    inference(cnf_transformation,[],[f104])).

fof(f104,plain,
    ( k13_lattice3(sK2,sK6,sK7) != k13_lattice3(sK3,sK4,sK5)
    & sK5 = sK7
    & sK4 = sK6
    & m1_subset_1(sK7,u1_struct_0(sK2))
    & m1_subset_1(sK6,u1_struct_0(sK2))
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & m1_yellow_0(sK3,sK2)
    & v6_yellow_0(sK3,sK2)
    & v4_yellow_0(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_orders_2(sK2)
    & v1_lattice3(sK2)
    & v5_orders_2(sK2)
    & v4_orders_2(sK2)
    & v3_orders_2(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f47,f103,f102,f101,f100,f99,f98])).

fof(f98,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( k13_lattice3(X0,X4,X5) != k13_lattice3(X1,X2,X3)
                            & X3 = X5
                            & X2 = X4
                            & m1_subset_1(X5,u1_struct_0(X0)) )
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                & m1_subset_1(X2,u1_struct_0(X1)) )
            & m1_yellow_0(X1,X0)
            & v6_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( k13_lattice3(sK2,X4,X5) != k13_lattice3(X1,X2,X3)
                          & X3 = X5
                          & X2 = X4
                          & m1_subset_1(X5,u1_struct_0(sK2)) )
                      & m1_subset_1(X4,u1_struct_0(sK2)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_yellow_0(X1,sK2)
          & v6_yellow_0(X1,sK2)
          & v4_yellow_0(X1,sK2)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(sK2)
      & v1_lattice3(sK2)
      & v5_orders_2(sK2)
      & v4_orders_2(sK2)
      & v3_orders_2(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f99,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( k13_lattice3(X0,X4,X5) != k13_lattice3(X1,X2,X3)
                          & X3 = X5
                          & X2 = X4
                          & m1_subset_1(X5,u1_struct_0(X0)) )
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_yellow_0(X1,X0)
          & v6_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( k13_lattice3(sK3,X2,X3) != k13_lattice3(X0,X4,X5)
                        & X3 = X5
                        & X2 = X4
                        & m1_subset_1(X5,u1_struct_0(X0)) )
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                & m1_subset_1(X3,u1_struct_0(sK3)) )
            & m1_subset_1(X2,u1_struct_0(sK3)) )
        & m1_yellow_0(sK3,X0)
        & v6_yellow_0(sK3,X0)
        & v4_yellow_0(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k13_lattice3(X0,X4,X5) != k13_lattice3(X1,X2,X3)
                      & X3 = X5
                      & X2 = X4
                      & m1_subset_1(X5,u1_struct_0(X0)) )
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              & m1_subset_1(X3,u1_struct_0(X1)) )
          & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k13_lattice3(X1,sK4,X3) != k13_lattice3(X0,X4,X5)
                    & X3 = X5
                    & sK4 = X4
                    & m1_subset_1(X5,u1_struct_0(X0)) )
                & m1_subset_1(X4,u1_struct_0(X0)) )
            & m1_subset_1(X3,u1_struct_0(X1)) )
        & m1_subset_1(sK4,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k13_lattice3(X0,X4,X5) != k13_lattice3(X1,X2,X3)
                  & X3 = X5
                  & X2 = X4
                  & m1_subset_1(X5,u1_struct_0(X0)) )
              & m1_subset_1(X4,u1_struct_0(X0)) )
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ? [X4] :
            ( ? [X5] :
                ( k13_lattice3(X1,X2,sK5) != k13_lattice3(X0,X4,X5)
                & sK5 = X5
                & X2 = X4
                & m1_subset_1(X5,u1_struct_0(X0)) )
            & m1_subset_1(X4,u1_struct_0(X0)) )
        & m1_subset_1(sK5,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( k13_lattice3(X0,X4,X5) != k13_lattice3(X1,X2,X3)
              & X3 = X5
              & X2 = X4
              & m1_subset_1(X5,u1_struct_0(X0)) )
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ? [X5] :
            ( k13_lattice3(X0,sK6,X5) != k13_lattice3(X1,X2,X3)
            & X3 = X5
            & sK6 = X2
            & m1_subset_1(X5,u1_struct_0(X0)) )
        & m1_subset_1(sK6,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f103,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k13_lattice3(X0,X4,X5) != k13_lattice3(X1,X2,X3)
          & X3 = X5
          & X2 = X4
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( k13_lattice3(X0,X4,sK7) != k13_lattice3(X1,X2,X3)
        & sK7 = X3
        & X2 = X4
        & m1_subset_1(sK7,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( k13_lattice3(X0,X4,X5) != k13_lattice3(X1,X2,X3)
                          & X3 = X5
                          & X2 = X4
                          & m1_subset_1(X5,u1_struct_0(X0)) )
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_yellow_0(X1,X0)
          & v6_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( k13_lattice3(X0,X4,X5) != k13_lattice3(X1,X2,X3)
                          & X3 = X5
                          & X2 = X4
                          & m1_subset_1(X5,u1_struct_0(X0)) )
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_yellow_0(X1,X0)
          & v6_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( ( m1_yellow_0(X1,X0)
              & v6_yellow_0(X1,X0)
              & v4_yellow_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X0))
                           => ( ( X3 = X5
                                & X2 = X4 )
                             => k13_lattice3(X0,X4,X5) = k13_lattice3(X1,X2,X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v6_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X0))
                         => ( ( X3 = X5
                              & X2 = X4 )
                           => k13_lattice3(X0,X4,X5) = k13_lattice3(X1,X2,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t71_yellow_0.p',t71_yellow_0)).

fof(f631,plain,(
    k13_lattice3(sK2,sK6,sK5) != k13_lattice3(sK3,sK4,sK5) ),
    inference(forward_demodulation,[],[f141,f140])).

fof(f140,plain,(
    sK5 = sK7 ),
    inference(cnf_transformation,[],[f104])).

fof(f141,plain,(
    k13_lattice3(sK2,sK6,sK7) != k13_lattice3(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f104])).

fof(f2142708,plain,(
    k13_lattice3(sK2,sK4,sK5) = k13_lattice3(sK3,sK4,sK5) ),
    inference(backward_demodulation,[],[f2142707,f63744])).

fof(f63744,plain,(
    k13_lattice3(sK3,sK4,sK5) = k1_yellow_0(sK3,k2_tarski(sK4,sK5)) ),
    inference(forward_demodulation,[],[f431,f7565])).

fof(f7565,plain,(
    k2_tarski(sK4,sK5) = k7_domain_1(u1_struct_0(sK3),sK4,sK5) ),
    inference(unit_resulting_resolution,[],[f136,f7556])).

fof(f7556,plain,(
    ! [X18] :
      ( ~ m1_subset_1(X18,u1_struct_0(sK3))
      | k2_tarski(sK4,X18) = k7_domain_1(u1_struct_0(sK3),sK4,X18) ) ),
    inference(subsumption_resolution,[],[f341,f654])).

fof(f654,plain,(
    ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(unit_resulting_resolution,[],[f131,f456,f173])).

fof(f173,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f42,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t71_yellow_0.p',fc2_struct_0)).

fof(f456,plain,(
    l1_struct_0(sK3) ),
    inference(unit_resulting_resolution,[],[f284,f197])).

fof(f197,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f94,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t71_yellow_0.p',dt_l1_orders_2)).

fof(f284,plain,(
    l1_orders_2(sK3) ),
    inference(unit_resulting_resolution,[],[f130,f134,f185])).

fof(f185,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t71_yellow_0.p',dt_m1_yellow_0)).

fof(f134,plain,(
    m1_yellow_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f104])).

fof(f130,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f104])).

fof(f131,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f104])).

fof(f341,plain,(
    ! [X18] :
      ( k2_tarski(sK4,X18) = k7_domain_1(u1_struct_0(sK3),sK4,X18)
      | ~ m1_subset_1(X18,u1_struct_0(sK3))
      | v1_xboole_0(u1_struct_0(sK3)) ) ),
    inference(resolution,[],[f135,f147])).

fof(f147,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = k7_domain_1(X0,X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X1,X2) = k7_domain_1(X0,X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
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
    file('/export/starexec/sandbox2/benchmark/yellow_0__t71_yellow_0.p',redefinition_k7_domain_1)).

fof(f135,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f104])).

fof(f136,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f104])).

fof(f431,plain,(
    k13_lattice3(sK3,sK4,sK5) = k1_yellow_0(sK3,k7_domain_1(u1_struct_0(sK3),sK4,sK5)) ),
    inference(unit_resulting_resolution,[],[f283,f281,f280,f282,f136,f135,f284,f145])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( k13_lattice3(X0,X1,X2) = k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k13_lattice3(X0,X1,X2) = k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k13_lattice3(X0,X1,X2) = k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k13_lattice3(X0,X1,X2) = k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t71_yellow_0.p',t41_yellow_0)).

fof(f282,plain,(
    v1_lattice3(sK3) ),
    inference(unit_resulting_resolution,[],[f127,f128,f129,f130,f131,f132,f133,f134,f179])).

fof(f179,plain,(
    ! [X0,X1] :
      ( v1_lattice3(X1)
      | ~ v6_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | v2_struct_0(X1)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & v1_lattice3(X1)
            & ~ v2_struct_0(X1) )
          | ~ v6_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0)
          | v2_struct_0(X1)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f82])).

fof(f82,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & v1_lattice3(X1)
            & ~ v2_struct_0(X1) )
          | ~ v6_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0)
          | v2_struct_0(X1)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => ( ( v6_yellow_0(X1,X0)
              & v4_yellow_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ( v6_yellow_0(X1,X0)
              & v4_yellow_0(X1,X0)
              & v1_lattice3(X1)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t71_yellow_0.p',cc12_yellow_0)).

fof(f133,plain,(
    v6_yellow_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f104])).

fof(f132,plain,(
    v4_yellow_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f104])).

fof(f129,plain,(
    v1_lattice3(sK2) ),
    inference(cnf_transformation,[],[f104])).

fof(f128,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f104])).

fof(f127,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f104])).

fof(f280,plain,(
    v5_orders_2(sK3) ),
    inference(unit_resulting_resolution,[],[f128,f130,f132,f134,f174])).

fof(f174,plain,(
    ! [X0,X1] :
      ( v5_orders_2(X1)
      | ~ v4_yellow_0(X1,X0)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_yellow_0(X1,X0)
            & v5_orders_2(X1) )
          | ~ v4_yellow_0(X1,X0)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f78])).

fof(f78,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_yellow_0(X1,X0)
            & v5_orders_2(X1) )
          | ~ v4_yellow_0(X1,X0)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => ( v4_yellow_0(X1,X0)
           => ( v4_yellow_0(X1,X0)
              & v5_orders_2(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t71_yellow_0.p',cc8_yellow_0)).

fof(f281,plain,(
    v4_orders_2(sK3) ),
    inference(unit_resulting_resolution,[],[f127,f130,f132,f134,f176])).

fof(f176,plain,(
    ! [X0,X1] :
      ( v4_orders_2(X1)
      | ~ v4_yellow_0(X1,X0)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_yellow_0(X1,X0)
            & v4_orders_2(X1) )
          | ~ v4_yellow_0(X1,X0)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f80])).

fof(f80,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_yellow_0(X1,X0)
            & v4_orders_2(X1) )
          | ~ v4_yellow_0(X1,X0)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => ( v4_yellow_0(X1,X0)
           => ( v4_yellow_0(X1,X0)
              & v4_orders_2(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t71_yellow_0.p',cc7_yellow_0)).

fof(f283,plain,(
    v3_orders_2(sK3) ),
    inference(unit_resulting_resolution,[],[f126,f130,f132,f134,f182])).

fof(f182,plain,(
    ! [X0,X1] :
      ( v3_orders_2(X1)
      | ~ v4_yellow_0(X1,X0)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_yellow_0(X1,X0)
            & v3_orders_2(X1) )
          | ~ v4_yellow_0(X1,X0)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f84])).

fof(f84,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_yellow_0(X1,X0)
            & v3_orders_2(X1) )
          | ~ v4_yellow_0(X1,X0)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => ( v4_yellow_0(X1,X0)
           => ( v4_yellow_0(X1,X0)
              & v3_orders_2(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t71_yellow_0.p',cc6_yellow_0)).

fof(f126,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f104])).

fof(f2142707,plain,(
    k13_lattice3(sK2,sK4,sK5) = k1_yellow_0(sK3,k2_tarski(sK4,sK5)) ),
    inference(subsumption_resolution,[],[f2142706,f131])).

fof(f2142706,plain,
    ( k13_lattice3(sK2,sK4,sK5) = k1_yellow_0(sK3,k2_tarski(sK4,sK5))
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f2142705,f134])).

fof(f2142705,plain,
    ( ~ m1_yellow_0(sK3,sK2)
    | k13_lattice3(sK2,sK4,sK5) = k1_yellow_0(sK3,k2_tarski(sK4,sK5))
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f2142704,f15787])).

fof(f15787,plain,(
    m1_subset_1(k2_tarski(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f15786,f654])).

fof(f15786,plain,
    ( m1_subset_1(k2_tarski(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f15785,f135])).

fof(f15785,plain,
    ( m1_subset_1(k2_tarski(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f15780,f136])).

fof(f15780,plain,
    ( m1_subset_1(k2_tarski(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(superposition,[],[f154,f7565])).

fof(f154,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t71_yellow_0.p',dt_k7_domain_1)).

fof(f2142704,plain,
    ( ~ m1_subset_1(k2_tarski(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_yellow_0(sK3,sK2)
    | k13_lattice3(sK2,sK4,sK5) = k1_yellow_0(sK3,k2_tarski(sK4,sK5))
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f2142703,f1207913])).

fof(f1207913,plain,(
    r2_hidden(k13_lattice3(sK2,sK4,sK5),u1_struct_0(sK3)) ),
    inference(unit_resulting_resolution,[],[f695,f729,f730,f1207864])).

fof(f1207864,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5,u1_struct_0(X0))
      | r2_hidden(k13_lattice3(sK2,sK4,sK5),u1_struct_0(X0))
      | ~ r2_hidden(sK4,u1_struct_0(X0))
      | ~ sP0(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f1207863,f578])).

fof(f578,plain,(
    r1_yellow_0(sK2,k2_tarski(sK4,sK5)) ),
    inference(unit_resulting_resolution,[],[f128,f130,f129,f398,f481,f159])).

fof(f159,plain,(
    ! [X4,X0,X3] :
      ( r1_yellow_0(X0,k2_tarski(X3,X4))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f111])).

fof(f111,plain,(
    ! [X0] :
      ( ( ( v1_lattice3(X0)
          | ( ~ r1_yellow_0(X0,k2_tarski(sK9(X0),sK10(X0)))
            & m1_subset_1(sK10(X0),u1_struct_0(X0))
            & m1_subset_1(sK9(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( r1_yellow_0(X0,k2_tarski(X3,X4))
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v1_lattice3(X0) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f108,f110,f109])).

fof(f109,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ~ r1_yellow_0(X0,k2_tarski(sK9(X0),X2))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK9(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f110,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ~ r1_yellow_0(X0,k2_tarski(X1,sK10(X0)))
        & m1_subset_1(sK10(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f108,plain,(
    ! [X0] :
      ( ( ( v1_lattice3(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( r1_yellow_0(X0,k2_tarski(X3,X4))
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v1_lattice3(X0) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f107])).

fof(f107,plain,(
    ! [X0] :
      ( ( ( v1_lattice3(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( r1_yellow_0(X0,k2_tarski(X1,X2))
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v1_lattice3(X0) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ( v1_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( r1_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( ( v1_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( r1_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ( v1_lattice3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => r1_yellow_0(X0,k2_tarski(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t71_yellow_0.p',t20_yellow_0)).

fof(f481,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f138,f140])).

fof(f138,plain,(
    m1_subset_1(sK7,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f104])).

fof(f398,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f137,f139])).

fof(f137,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f104])).

fof(f1207863,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK2,k2_tarski(sK4,sK5))
      | r2_hidden(k13_lattice3(sK2,sK4,sK5),u1_struct_0(X0))
      | ~ r2_hidden(sK5,u1_struct_0(X0))
      | ~ r2_hidden(sK4,u1_struct_0(X0))
      | ~ sP0(X0,sK2) ) ),
    inference(forward_demodulation,[],[f6408,f8846])).

fof(f8846,plain,(
    k2_tarski(sK4,sK5) = k7_domain_1(u1_struct_0(sK2),sK4,sK5) ),
    inference(unit_resulting_resolution,[],[f481,f8836])).

fof(f8836,plain,(
    ! [X18] :
      ( ~ m1_subset_1(X18,u1_struct_0(sK2))
      | k2_tarski(sK4,X18) = k7_domain_1(u1_struct_0(sK2),sK4,X18) ) ),
    inference(subsumption_resolution,[],[f522,f275])).

fof(f275,plain,(
    ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(unit_resulting_resolution,[],[f231,f233,f173])).

fof(f233,plain,(
    l1_struct_0(sK2) ),
    inference(unit_resulting_resolution,[],[f130,f197])).

fof(f231,plain,(
    ~ v2_struct_0(sK2) ),
    inference(unit_resulting_resolution,[],[f129,f130,f186])).

fof(f186,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f88])).

fof(f88,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t71_yellow_0.p',cc1_lattice3)).

fof(f522,plain,(
    ! [X18] :
      ( k2_tarski(sK4,X18) = k7_domain_1(u1_struct_0(sK2),sK4,X18)
      | ~ m1_subset_1(X18,u1_struct_0(sK2))
      | v1_xboole_0(u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f398,f147])).

fof(f6408,plain,(
    ! [X0] :
      ( r2_hidden(k13_lattice3(sK2,sK4,sK5),u1_struct_0(X0))
      | ~ r1_yellow_0(sK2,k7_domain_1(u1_struct_0(sK2),sK4,sK5))
      | ~ r2_hidden(sK5,u1_struct_0(X0))
      | ~ r2_hidden(sK4,u1_struct_0(X0))
      | ~ sP0(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f6407,f398])).

fof(f6407,plain,(
    ! [X0] :
      ( r2_hidden(k13_lattice3(sK2,sK4,sK5),u1_struct_0(X0))
      | ~ r1_yellow_0(sK2,k7_domain_1(u1_struct_0(sK2),sK4,sK5))
      | ~ r2_hidden(sK5,u1_struct_0(X0))
      | ~ r2_hidden(sK4,u1_struct_0(X0))
      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
      | ~ sP0(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f6401,f481])).

fof(f6401,plain,(
    ! [X0] :
      ( r2_hidden(k13_lattice3(sK2,sK4,sK5),u1_struct_0(X0))
      | ~ r1_yellow_0(sK2,k7_domain_1(u1_struct_0(sK2),sK4,sK5))
      | ~ r2_hidden(sK5,u1_struct_0(X0))
      | ~ r2_hidden(sK4,u1_struct_0(X0))
      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
      | ~ sP0(X0,sK2) ) ),
    inference(superposition,[],[f165,f572])).

fof(f572,plain,(
    k13_lattice3(sK2,sK4,sK5) = k1_yellow_0(sK2,k7_domain_1(u1_struct_0(sK2),sK4,sK5)) ),
    inference(unit_resulting_resolution,[],[f126,f127,f128,f129,f130,f398,f481,f145])).

fof(f165,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X4,X5)),u1_struct_0(X0))
      | ~ r1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X4,X5))
      | ~ r2_hidden(X5,u1_struct_0(X0))
      | ~ r2_hidden(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ~ r2_hidden(k1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),sK11(X0,X1),sK12(X0,X1))),u1_struct_0(X0))
          & r1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),sK11(X0,X1),sK12(X0,X1)))
          & r2_hidden(sK12(X0,X1),u1_struct_0(X0))
          & r2_hidden(sK11(X0,X1),u1_struct_0(X0))
          & m1_subset_1(sK12(X0,X1),u1_struct_0(X1))
          & m1_subset_1(sK11(X0,X1),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( ! [X5] :
                ( r2_hidden(k1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X4,X5)),u1_struct_0(X0))
                | ~ r1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X4,X5))
                | ~ r2_hidden(X5,u1_struct_0(X0))
                | ~ r2_hidden(X4,u1_struct_0(X0))
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12])],[f114,f116,f115])).

fof(f115,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(k1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)),u1_struct_0(X0))
              & r1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3))
              & r2_hidden(X3,u1_struct_0(X0))
              & r2_hidden(X2,u1_struct_0(X0))
              & m1_subset_1(X3,u1_struct_0(X1)) )
          & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ? [X3] :
            ( ~ r2_hidden(k1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),sK11(X0,X1),X3)),u1_struct_0(X0))
            & r1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),sK11(X0,X1),X3))
            & r2_hidden(X3,u1_struct_0(X0))
            & r2_hidden(sK11(X0,X1),u1_struct_0(X0))
            & m1_subset_1(X3,u1_struct_0(X1)) )
        & m1_subset_1(sK11(X0,X1),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f116,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)),u1_struct_0(X0))
          & r1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3))
          & r2_hidden(X3,u1_struct_0(X0))
          & r2_hidden(X2,u1_struct_0(X0))
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r2_hidden(k1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,sK12(X0,X1))),u1_struct_0(X0))
        & r1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,sK12(X0,X1)))
        & r2_hidden(sK12(X0,X1),u1_struct_0(X0))
        & r2_hidden(X2,u1_struct_0(X0))
        & m1_subset_1(sK12(X0,X1),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(k1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)),u1_struct_0(X0))
                & r1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3))
                & r2_hidden(X3,u1_struct_0(X0))
                & r2_hidden(X2,u1_struct_0(X0))
                & m1_subset_1(X3,u1_struct_0(X1)) )
            & m1_subset_1(X2,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( ! [X5] :
                ( r2_hidden(k1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X4,X5)),u1_struct_0(X0))
                | ~ r1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X4,X5))
                | ~ r2_hidden(X5,u1_struct_0(X0))
                | ~ r2_hidden(X4,u1_struct_0(X0))
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f113])).

fof(f113,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X2,X3)),u1_struct_0(X1))
                & r1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X2,X3))
                & r2_hidden(X3,u1_struct_0(X1))
                & r2_hidden(X2,u1_struct_0(X1))
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ! [X2] :
            ( ! [X3] :
                ( r2_hidden(k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X2,X3)),u1_struct_0(X1))
                | ~ r1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X2,X3))
                | ~ r2_hidden(X3,u1_struct_0(X1))
                | ~ r2_hidden(X2,u1_struct_0(X1))
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f95])).

fof(f95,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ! [X2] :
          ( ! [X3] :
              ( r2_hidden(k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X2,X3)),u1_struct_0(X1))
              | ~ r1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X2,X3))
              | ~ r2_hidden(X3,u1_struct_0(X1))
              | ~ r2_hidden(X2,u1_struct_0(X1))
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f730,plain,(
    r2_hidden(sK5,u1_struct_0(sK3)) ),
    inference(unit_resulting_resolution,[],[f136,f654,f155])).

fof(f155,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t71_yellow_0.p',t2_subset)).

fof(f729,plain,(
    r2_hidden(sK4,u1_struct_0(sK3)) ),
    inference(unit_resulting_resolution,[],[f135,f654,f155])).

fof(f695,plain,(
    sP0(sK3,sK2) ),
    inference(unit_resulting_resolution,[],[f133,f279,f163])).

fof(f163,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ v6_yellow_0(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ( ( v6_yellow_0(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v6_yellow_0(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ( v6_yellow_0(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f279,plain,(
    sP1(sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f231,f130,f134,f172])).

fof(f172,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f97,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f75,f96,f95])).

fof(f75,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_yellow_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X2,X3)),u1_struct_0(X1))
                    | ~ r1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X2,X3))
                    | ~ r2_hidden(X3,u1_struct_0(X1))
                    | ~ r2_hidden(X2,u1_struct_0(X1))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f74])).

fof(f74,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_yellow_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X2,X3)),u1_struct_0(X1))
                    | ~ r1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X2,X3))
                    | ~ r2_hidden(X3,u1_struct_0(X1))
                    | ~ r2_hidden(X2,u1_struct_0(X1))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => ( v6_yellow_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X2,X3))
                        & r2_hidden(X3,u1_struct_0(X1))
                        & r2_hidden(X2,u1_struct_0(X1)) )
                     => r2_hidden(k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X2,X3)),u1_struct_0(X1)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t71_yellow_0.p',d17_yellow_0)).

fof(f2142703,plain,
    ( ~ r2_hidden(k13_lattice3(sK2,sK4,sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tarski(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_yellow_0(sK3,sK2)
    | k13_lattice3(sK2,sK4,sK5) = k1_yellow_0(sK3,k2_tarski(sK4,sK5))
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f16058,f132])).

fof(f16058,plain,(
    ! [X3] :
      ( ~ v4_yellow_0(X3,sK2)
      | ~ r2_hidden(k13_lattice3(sK2,sK4,sK5),u1_struct_0(X3))
      | ~ m1_subset_1(k2_tarski(sK4,sK5),k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_yellow_0(X3,sK2)
      | k13_lattice3(sK2,sK4,sK5) = k1_yellow_0(X3,k2_tarski(sK4,sK5))
      | v2_struct_0(X3) ) ),
    inference(forward_demodulation,[],[f16057,f15988])).

fof(f15988,plain,(
    k13_lattice3(sK2,sK4,sK5) = k1_yellow_0(sK2,k2_tarski(sK4,sK5)) ),
    inference(backward_demodulation,[],[f8846,f572])).

fof(f16057,plain,(
    ! [X3] :
      ( ~ r2_hidden(k13_lattice3(sK2,sK4,sK5),u1_struct_0(X3))
      | k1_yellow_0(sK2,k2_tarski(sK4,sK5)) = k1_yellow_0(X3,k2_tarski(sK4,sK5))
      | ~ m1_subset_1(k2_tarski(sK4,sK5),k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_yellow_0(X3,sK2)
      | ~ v4_yellow_0(X3,sK2)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f16056,f231])).

fof(f16056,plain,(
    ! [X3] :
      ( ~ r2_hidden(k13_lattice3(sK2,sK4,sK5),u1_struct_0(X3))
      | k1_yellow_0(sK2,k2_tarski(sK4,sK5)) = k1_yellow_0(X3,k2_tarski(sK4,sK5))
      | ~ m1_subset_1(k2_tarski(sK4,sK5),k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_yellow_0(X3,sK2)
      | ~ v4_yellow_0(X3,sK2)
      | v2_struct_0(X3)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f16055,f127])).

fof(f16055,plain,(
    ! [X3] :
      ( ~ r2_hidden(k13_lattice3(sK2,sK4,sK5),u1_struct_0(X3))
      | k1_yellow_0(sK2,k2_tarski(sK4,sK5)) = k1_yellow_0(X3,k2_tarski(sK4,sK5))
      | ~ m1_subset_1(k2_tarski(sK4,sK5),k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_yellow_0(X3,sK2)
      | ~ v4_yellow_0(X3,sK2)
      | v2_struct_0(X3)
      | ~ v4_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f16054,f130])).

fof(f16054,plain,(
    ! [X3] :
      ( ~ r2_hidden(k13_lattice3(sK2,sK4,sK5),u1_struct_0(X3))
      | k1_yellow_0(sK2,k2_tarski(sK4,sK5)) = k1_yellow_0(X3,k2_tarski(sK4,sK5))
      | ~ m1_subset_1(k2_tarski(sK4,sK5),k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_yellow_0(X3,sK2)
      | ~ v4_yellow_0(X3,sK2)
      | v2_struct_0(X3)
      | ~ l1_orders_2(sK2)
      | ~ v4_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f16046,f578])).

fof(f16046,plain,(
    ! [X3] :
      ( ~ r2_hidden(k13_lattice3(sK2,sK4,sK5),u1_struct_0(X3))
      | k1_yellow_0(sK2,k2_tarski(sK4,sK5)) = k1_yellow_0(X3,k2_tarski(sK4,sK5))
      | ~ r1_yellow_0(sK2,k2_tarski(sK4,sK5))
      | ~ m1_subset_1(k2_tarski(sK4,sK5),k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_yellow_0(X3,sK2)
      | ~ v4_yellow_0(X3,sK2)
      | v2_struct_0(X3)
      | ~ l1_orders_2(sK2)
      | ~ v4_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(superposition,[],[f151,f15988])).

fof(f151,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
      | ~ r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
      | ~ r1_yellow_0(X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
                & r1_yellow_0(X1,X2) )
              | ~ r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
              | ~ r1_yellow_0(X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
                & r1_yellow_0(X1,X2) )
              | ~ r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
              | ~ r1_yellow_0(X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
                  & r1_yellow_0(X0,X2) )
               => ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
                  & r1_yellow_0(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t71_yellow_0.p',t65_yellow_0)).
%------------------------------------------------------------------------------
