%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:03 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 147 expanded)
%              Number of leaves         :   18 (  47 expanded)
%              Depth                    :   15
%              Number of atoms          :  472 ( 827 expanded)
%              Number of equality atoms :   32 (  44 expanded)
%              Maximal formula depth    :   17 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f257,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f53,f55,f54,f56,f57,f58,f251])).

fof(f251,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(k4_waybel_9(X2,X1,X0)),u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X2)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X2)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | v2_struct_0(X2) ) ),
    inference(duplicate_literal_removal,[],[f246])).

fof(f246,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X2)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X2)
      | r1_tarski(u1_struct_0(k4_waybel_9(X2,X1,X0)),u1_struct_0(X1))
      | v2_struct_0(X2)
      | r1_tarski(u1_struct_0(k4_waybel_9(X2,X1,X0)),u1_struct_0(X1)) ) ),
    inference(resolution,[],[f196,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK9(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK9(X0,X1),X1)
        & r2_hidden(sK9(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f26,f51])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK9(X0,X1),X1)
        & r2_hidden(sK9(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f196,plain,(
    ! [X6,X4,X7,X5] :
      ( r2_hidden(sK9(u1_struct_0(k4_waybel_9(X4,X6,X5)),X7),u1_struct_0(X6))
      | ~ m1_subset_1(X5,u1_struct_0(X6))
      | ~ l1_waybel_0(X6,X4)
      | v2_struct_0(X6)
      | ~ l1_struct_0(X4)
      | r1_tarski(u1_struct_0(k4_waybel_9(X4,X6,X5)),X7)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f191,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X1))
      | v2_struct_0(X1)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ v1_xboole_0(u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f100,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(u1_waybel_0(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(u1_waybel_0(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(u1_waybel_0(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_waybel_0(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( ~ v1_xboole_0(u1_waybel_0(X0,X1))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & ~ v1_xboole_0(u1_waybel_0(X0,X1))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc15_yellow_6)).

fof(f100,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(u1_waybel_0(X1,X0))
      | ~ l1_struct_0(X1)
      | ~ l1_waybel_0(X0,X1)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(resolution,[],[f77,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_waybel_0)).

fof(f191,plain,(
    ! [X6,X4,X7,X5] :
      ( v2_struct_0(X4)
      | ~ m1_subset_1(X5,u1_struct_0(X6))
      | ~ l1_waybel_0(X6,X4)
      | v2_struct_0(X6)
      | ~ l1_struct_0(X4)
      | r1_tarski(u1_struct_0(k4_waybel_9(X4,X6,X5)),X7)
      | v1_xboole_0(u1_struct_0(X6))
      | r2_hidden(sK9(u1_struct_0(k4_waybel_9(X4,X6,X5)),X7),u1_struct_0(X6)) ) ),
    inference(resolution,[],[f166,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | v1_xboole_0(u1_struct_0(X1))
      | r2_hidden(X2,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,u1_struct_0(X1))
      | v1_xboole_0(u1_struct_0(X1))
      | ~ sP0(X0,X1,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(superposition,[],[f87,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( sK8(X0,X1,X2) = X2
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ~ r1_orders_2(X1,X0,X3)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ( r1_orders_2(X1,X0,sK8(X0,X1,X2))
          & sK8(X0,X1,X2) = X2
          & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f48,f49])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r1_orders_2(X1,X0,X4)
          & X2 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r1_orders_2(X1,X0,sK8(X0,X1,X2))
        & sK8(X0,X1,X2) = X2
        & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ~ r1_orders_2(X1,X0,X3)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X4] :
            ( r1_orders_2(X1,X0,X4)
            & X2 = X4
            & m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X2,X1,X4] :
      ( ( sP0(X2,X1,X4)
        | ! [X5] :
            ( ~ r1_orders_2(X1,X2,X5)
            | X4 != X5
            | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
      & ( ? [X5] :
            ( r1_orders_2(X1,X2,X5)
            & X4 = X5
            & m1_subset_1(X5,u1_struct_0(X1)) )
        | ~ sP0(X2,X1,X4) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X2,X1,X4] :
      ( sP0(X2,X1,X4)
    <=> ? [X5] :
          ( r1_orders_2(X1,X2,X5)
          & X4 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK8(X0,X1,X2),u1_struct_0(X1))
      | v1_xboole_0(u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(resolution,[],[f69,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f166,plain,(
    ! [X21,X19,X20,X18] :
      ( sP0(X19,X20,sK9(u1_struct_0(k4_waybel_9(X18,X20,X19)),X21))
      | v2_struct_0(X18)
      | ~ m1_subset_1(X19,u1_struct_0(X20))
      | ~ l1_waybel_0(X20,X18)
      | v2_struct_0(X20)
      | ~ l1_struct_0(X18)
      | r1_tarski(u1_struct_0(k4_waybel_9(X18,X20,X19)),X21) ) ),
    inference(resolution,[],[f144,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f144,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_hidden(X7,u1_struct_0(k4_waybel_9(X5,X4,X6)))
      | ~ l1_struct_0(X5)
      | v2_struct_0(X5)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ l1_waybel_0(X4,X5)
      | v2_struct_0(X4)
      | sP0(X6,X4,X7) ) ),
    inference(resolution,[],[f136,f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X4,u1_struct_0(X2))
      | sP0(X1,X0,X4) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(X1,X0,sK7(X0,X1,X2))
            | ~ r2_hidden(sK7(X0,X1,X2),u1_struct_0(X2)) )
          & ( sP0(X1,X0,sK7(X0,X1,X2))
            | r2_hidden(sK7(X0,X1,X2),u1_struct_0(X2)) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,u1_struct_0(X2))
              | ~ sP0(X1,X0,X4) )
            & ( sP0(X1,X0,X4)
              | ~ r2_hidden(X4,u1_struct_0(X2)) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f44,f45])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP0(X1,X0,X3)
            | ~ r2_hidden(X3,u1_struct_0(X2)) )
          & ( sP0(X1,X0,X3)
            | r2_hidden(X3,u1_struct_0(X2)) ) )
     => ( ( ~ sP0(X1,X0,sK7(X0,X1,X2))
          | ~ r2_hidden(sK7(X0,X1,X2),u1_struct_0(X2)) )
        & ( sP0(X1,X0,sK7(X0,X1,X2))
          | r2_hidden(sK7(X0,X1,X2),u1_struct_0(X2)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X0,X3)
              | ~ r2_hidden(X3,u1_struct_0(X2)) )
            & ( sP0(X1,X0,X3)
              | r2_hidden(X3,u1_struct_0(X2)) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,u1_struct_0(X2))
              | ~ sP0(X1,X0,X4) )
            & ( sP0(X1,X0,X4)
              | ~ r2_hidden(X4,u1_struct_0(X2)) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X1,X2,X3] :
      ( ( sP1(X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP0(X2,X1,X4)
              | ~ r2_hidden(X4,u1_struct_0(X3)) )
            & ( sP0(X2,X1,X4)
              | r2_hidden(X4,u1_struct_0(X3)) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,u1_struct_0(X3))
              | ~ sP0(X2,X1,X4) )
            & ( sP0(X2,X1,X4)
              | ~ r2_hidden(X4,u1_struct_0(X3)) ) )
        | ~ sP1(X1,X2,X3) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X1,X2,X3] :
      ( sP1(X1,X2,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,u1_struct_0(X3))
        <=> sP0(X2,X1,X4) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f136,plain,(
    ! [X6,X4,X5] :
      ( sP1(X4,X6,k4_waybel_9(X5,X4,X6))
      | v2_struct_0(X4)
      | ~ l1_struct_0(X5)
      | v2_struct_0(X5)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ l1_waybel_0(X4,X5) ) ),
    inference(resolution,[],[f126,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP2(X0,X1,X2,X3)
      | sP1(X1,X3,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP2(X0,X1,X2,X3)
        | u1_waybel_0(X2,X0) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1),u1_struct_0(X0))
        | ~ r2_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0),k1_toler_1(u1_orders_2(X1),u1_struct_0(X0)))
        | ~ sP1(X1,X3,X0) )
      & ( ( u1_waybel_0(X2,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1),u1_struct_0(X0))
          & r2_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0),k1_toler_1(u1_orders_2(X1),u1_struct_0(X0)))
          & sP1(X1,X3,X0) )
        | ~ sP2(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X3,X1,X0,X2] :
      ( ( sP2(X3,X1,X0,X2)
        | u1_waybel_0(X0,X3) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
        | ~ r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
        | ~ sP1(X1,X2,X3) )
      & ( ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
          & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
          & sP1(X1,X2,X3) )
        | ~ sP2(X3,X1,X0,X2) ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X3,X1,X0,X2] :
      ( ( sP2(X3,X1,X0,X2)
        | u1_waybel_0(X0,X3) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
        | ~ r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
        | ~ sP1(X1,X2,X3) )
      & ( ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
          & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
          & sP1(X1,X2,X3) )
        | ~ sP2(X3,X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X3,X1,X0,X2] :
      ( sP2(X3,X1,X0,X2)
    <=> ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
        & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
        & sP1(X1,X2,X3) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( sP2(k4_waybel_9(X0,X1,X2),X1,X0,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f125,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_waybel_9)).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( ~ v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | sP2(k4_waybel_9(X0,X1,X2),X1,X0,X2) ) ),
    inference(subsumption_resolution,[],[f123,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | sP2(k4_waybel_9(X0,X1,X2),X1,X0,X2) ) ),
    inference(resolution,[],[f73,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X0,X1,X2,k4_waybel_9(X1,X2,X0))
      | sP2(k4_waybel_9(X1,X2,X0),X2,X1,X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X3,X2,X1,X0)
      | k4_waybel_9(X1,X2,X0) != X3
      | ~ sP3(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k4_waybel_9(X1,X2,X0) = X3
          | ~ sP2(X3,X2,X1,X0) )
        & ( sP2(X3,X2,X1,X0)
          | k4_waybel_9(X1,X2,X0) != X3 ) )
      | ~ sP3(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X1,X3] :
      ( ( ( k4_waybel_9(X0,X1,X2) = X3
          | ~ sP2(X3,X1,X0,X2) )
        & ( sP2(X3,X1,X0,X2)
          | k4_waybel_9(X0,X1,X2) != X3 ) )
      | ~ sP3(X2,X0,X1,X3) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X1,X3] :
      ( ( k4_waybel_9(X0,X1,X2) = X3
      <=> sP2(X3,X1,X0,X2) )
      | ~ sP3(X2,X0,X1,X3) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X2,X0,X1,X3)
      | ~ l1_waybel_0(X3,X0)
      | ~ v6_waybel_0(X3,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( sP3(X2,X0,X1,X3)
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f18,f32,f31,f30,f29])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_waybel_9)).

fof(f58,plain,(
    ~ r1_tarski(u1_struct_0(k4_waybel_9(sK4,sK5,sK6)),u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ~ r1_tarski(u1_struct_0(k4_waybel_9(sK4,sK5,sK6)),u1_struct_0(sK5))
    & m1_subset_1(sK6,u1_struct_0(sK5))
    & l1_waybel_0(sK5,sK4)
    & ~ v2_struct_0(sK5)
    & l1_struct_0(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f16,f36,f35,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1))
                & m1_subset_1(X2,u1_struct_0(X1)) )
            & l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(u1_struct_0(k4_waybel_9(sK4,X1,X2)),u1_struct_0(X1))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,sK4)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(u1_struct_0(k4_waybel_9(sK4,X1,X2)),u1_struct_0(X1))
            & m1_subset_1(X2,u1_struct_0(X1)) )
        & l1_waybel_0(X1,sK4)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(u1_struct_0(k4_waybel_9(sK4,sK5,X2)),u1_struct_0(sK5))
          & m1_subset_1(X2,u1_struct_0(sK5)) )
      & l1_waybel_0(sK5,sK4)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X2] :
        ( ~ r1_tarski(u1_struct_0(k4_waybel_9(sK4,sK5,X2)),u1_struct_0(sK5))
        & m1_subset_1(X2,u1_struct_0(sK5)) )
   => ( ~ r1_tarski(u1_struct_0(k4_waybel_9(sK4,sK5,sK6)),u1_struct_0(sK5))
      & m1_subset_1(sK6,u1_struct_0(sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_waybel_9)).

fof(f57,plain,(
    m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f37])).

fof(f56,plain,(
    l1_waybel_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f54,plain,(
    l1_struct_0(sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f55,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f37])).

fof(f53,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:13:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.52  % (2486)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (2494)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (2494)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f257,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f53,f55,f54,f56,f57,f58,f251])).
% 0.21/0.54  fof(f251,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(k4_waybel_9(X2,X1,X0)),u1_struct_0(X1)) | ~l1_waybel_0(X1,X2) | v2_struct_0(X1) | ~l1_struct_0(X2) | ~m1_subset_1(X0,u1_struct_0(X1)) | v2_struct_0(X2)) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f246])).
% 0.21/0.54  fof(f246,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_waybel_0(X1,X2) | v2_struct_0(X1) | ~l1_struct_0(X2) | r1_tarski(u1_struct_0(k4_waybel_9(X2,X1,X0)),u1_struct_0(X1)) | v2_struct_0(X2) | r1_tarski(u1_struct_0(k4_waybel_9(X2,X1,X0)),u1_struct_0(X1))) )),
% 0.21/0.54    inference(resolution,[],[f196,f79])).
% 0.21/0.54  fof(f79,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(sK9(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f52])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0)))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f26,f51])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0)))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,plain,(
% 0.21/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 0.21/0.54    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.54  fof(f196,plain,(
% 0.21/0.54    ( ! [X6,X4,X7,X5] : (r2_hidden(sK9(u1_struct_0(k4_waybel_9(X4,X6,X5)),X7),u1_struct_0(X6)) | ~m1_subset_1(X5,u1_struct_0(X6)) | ~l1_waybel_0(X6,X4) | v2_struct_0(X6) | ~l1_struct_0(X4) | r1_tarski(u1_struct_0(k4_waybel_9(X4,X6,X5)),X7) | v2_struct_0(X4)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f191,f108])).
% 0.21/0.54  fof(f108,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X1)) | v2_struct_0(X1) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f107])).
% 0.21/0.54  fof(f107,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~l1_struct_0(X0) | ~l1_waybel_0(X1,X0) | ~v1_xboole_0(u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(resolution,[],[f100,f76])).
% 0.21/0.54  fof(f76,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_xboole_0(u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0,X1] : (~v1_xboole_0(u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0,X1] : (~v1_xboole_0(u1_waybel_0(X0,X1)) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ! [X0,X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_waybel_0(X0,X1)))),
% 0.21/0.54    inference(pure_predicate_removal,[],[f12])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    ! [X0,X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (~v1_xboole_0(u1_waybel_0(X0,X1)) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 0.21/0.54    inference(pure_predicate_removal,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & ~v1_xboole_0(u1_waybel_0(X0,X1)) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc15_yellow_6)).
% 0.21/0.54  fof(f100,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_xboole_0(u1_waybel_0(X1,X0)) | ~l1_struct_0(X1) | ~l1_waybel_0(X0,X1) | ~v1_xboole_0(u1_struct_0(X0))) )),
% 0.21/0.54    inference(resolution,[],[f77,f74])).
% 0.21/0.54  fof(f74,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X2) | ~v1_xboole_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    ( ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))))),
% 0.21/0.54    inference(pure_predicate_removal,[],[f11])).
% 0.21/0.54  fof(f11,plain,(
% 0.21/0.54    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 0.21/0.54    inference(pure_predicate_removal,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_waybel_0)).
% 0.21/0.54  fof(f191,plain,(
% 0.21/0.54    ( ! [X6,X4,X7,X5] : (v2_struct_0(X4) | ~m1_subset_1(X5,u1_struct_0(X6)) | ~l1_waybel_0(X6,X4) | v2_struct_0(X6) | ~l1_struct_0(X4) | r1_tarski(u1_struct_0(k4_waybel_9(X4,X6,X5)),X7) | v1_xboole_0(u1_struct_0(X6)) | r2_hidden(sK9(u1_struct_0(k4_waybel_9(X4,X6,X5)),X7),u1_struct_0(X6))) )),
% 0.21/0.54    inference(resolution,[],[f166,f99])).
% 0.21/0.54  fof(f99,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | v1_xboole_0(u1_struct_0(X1)) | r2_hidden(X2,u1_struct_0(X1))) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f98])).
% 0.21/0.54  fof(f98,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r2_hidden(X2,u1_struct_0(X1)) | v1_xboole_0(u1_struct_0(X1)) | ~sP0(X0,X1,X2) | ~sP0(X0,X1,X2)) )),
% 0.21/0.54    inference(superposition,[],[f87,f70])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (sK8(X0,X1,X2) = X2 | ~sP0(X0,X1,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f50])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (~r1_orders_2(X1,X0,X3) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r1_orders_2(X1,X0,sK8(X0,X1,X2)) & sK8(X0,X1,X2) = X2 & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1))) | ~sP0(X0,X1,X2)))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f48,f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ! [X2,X1,X0] : (? [X4] : (r1_orders_2(X1,X0,X4) & X2 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r1_orders_2(X1,X0,sK8(X0,X1,X2)) & sK8(X0,X1,X2) = X2 & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (~r1_orders_2(X1,X0,X3) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r1_orders_2(X1,X0,X4) & X2 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~sP0(X0,X1,X2)))),
% 0.21/0.54    inference(rectify,[],[f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ! [X2,X1,X4] : ((sP0(X2,X1,X4) | ! [X5] : (~r1_orders_2(X1,X2,X5) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & (? [X5] : (r1_orders_2(X1,X2,X5) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~sP0(X2,X1,X4)))),
% 0.21/0.54    inference(nnf_transformation,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X2,X1,X4] : (sP0(X2,X1,X4) <=> ? [X5] : (r1_orders_2(X1,X2,X5) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X1))))),
% 0.21/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.54  fof(f87,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK8(X0,X1,X2),u1_struct_0(X1)) | v1_xboole_0(u1_struct_0(X1)) | ~sP0(X0,X1,X2)) )),
% 0.21/0.54    inference(resolution,[],[f69,f75])).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.54    inference(flattening,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1)) | ~sP0(X0,X1,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f50])).
% 0.21/0.54  fof(f166,plain,(
% 0.21/0.54    ( ! [X21,X19,X20,X18] : (sP0(X19,X20,sK9(u1_struct_0(k4_waybel_9(X18,X20,X19)),X21)) | v2_struct_0(X18) | ~m1_subset_1(X19,u1_struct_0(X20)) | ~l1_waybel_0(X20,X18) | v2_struct_0(X20) | ~l1_struct_0(X18) | r1_tarski(u1_struct_0(k4_waybel_9(X18,X20,X19)),X21)) )),
% 0.21/0.54    inference(resolution,[],[f144,f78])).
% 0.21/0.54  fof(f78,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(sK9(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f52])).
% 0.21/0.54  fof(f144,plain,(
% 0.21/0.54    ( ! [X6,X4,X7,X5] : (~r2_hidden(X7,u1_struct_0(k4_waybel_9(X5,X4,X6))) | ~l1_struct_0(X5) | v2_struct_0(X5) | ~m1_subset_1(X6,u1_struct_0(X4)) | ~l1_waybel_0(X4,X5) | v2_struct_0(X4) | sP0(X6,X4,X7)) )),
% 0.21/0.54    inference(resolution,[],[f136,f65])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X4,u1_struct_0(X2)) | sP0(X1,X0,X4)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~sP0(X1,X0,sK7(X0,X1,X2)) | ~r2_hidden(sK7(X0,X1,X2),u1_struct_0(X2))) & (sP0(X1,X0,sK7(X0,X1,X2)) | r2_hidden(sK7(X0,X1,X2),u1_struct_0(X2))))) & (! [X4] : ((r2_hidden(X4,u1_struct_0(X2)) | ~sP0(X1,X0,X4)) & (sP0(X1,X0,X4) | ~r2_hidden(X4,u1_struct_0(X2)))) | ~sP1(X0,X1,X2)))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f44,f45])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ! [X2,X1,X0] : (? [X3] : ((~sP0(X1,X0,X3) | ~r2_hidden(X3,u1_struct_0(X2))) & (sP0(X1,X0,X3) | r2_hidden(X3,u1_struct_0(X2)))) => ((~sP0(X1,X0,sK7(X0,X1,X2)) | ~r2_hidden(sK7(X0,X1,X2),u1_struct_0(X2))) & (sP0(X1,X0,sK7(X0,X1,X2)) | r2_hidden(sK7(X0,X1,X2),u1_struct_0(X2)))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X0,X3) | ~r2_hidden(X3,u1_struct_0(X2))) & (sP0(X1,X0,X3) | r2_hidden(X3,u1_struct_0(X2))))) & (! [X4] : ((r2_hidden(X4,u1_struct_0(X2)) | ~sP0(X1,X0,X4)) & (sP0(X1,X0,X4) | ~r2_hidden(X4,u1_struct_0(X2)))) | ~sP1(X0,X1,X2)))),
% 0.21/0.54    inference(rectify,[],[f43])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ! [X1,X2,X3] : ((sP1(X1,X2,X3) | ? [X4] : ((~sP0(X2,X1,X4) | ~r2_hidden(X4,u1_struct_0(X3))) & (sP0(X2,X1,X4) | r2_hidden(X4,u1_struct_0(X3))))) & (! [X4] : ((r2_hidden(X4,u1_struct_0(X3)) | ~sP0(X2,X1,X4)) & (sP0(X2,X1,X4) | ~r2_hidden(X4,u1_struct_0(X3)))) | ~sP1(X1,X2,X3)))),
% 0.21/0.54    inference(nnf_transformation,[],[f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ! [X1,X2,X3] : (sP1(X1,X2,X3) <=> ! [X4] : (r2_hidden(X4,u1_struct_0(X3)) <=> sP0(X2,X1,X4)))),
% 0.21/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.54  fof(f136,plain,(
% 0.21/0.54    ( ! [X6,X4,X5] : (sP1(X4,X6,k4_waybel_9(X5,X4,X6)) | v2_struct_0(X4) | ~l1_struct_0(X5) | v2_struct_0(X5) | ~m1_subset_1(X6,u1_struct_0(X4)) | ~l1_waybel_0(X4,X5)) )),
% 0.21/0.54    inference(resolution,[],[f126,f61])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~sP2(X0,X1,X2,X3) | sP1(X1,X3,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((sP2(X0,X1,X2,X3) | u1_waybel_0(X2,X0) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1),u1_struct_0(X0)) | ~r2_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0),k1_toler_1(u1_orders_2(X1),u1_struct_0(X0))) | ~sP1(X1,X3,X0)) & ((u1_waybel_0(X2,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1),u1_struct_0(X0)) & r2_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0),k1_toler_1(u1_orders_2(X1),u1_struct_0(X0))) & sP1(X1,X3,X0)) | ~sP2(X0,X1,X2,X3)))),
% 0.21/0.54    inference(rectify,[],[f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ! [X3,X1,X0,X2] : ((sP2(X3,X1,X0,X2) | u1_waybel_0(X0,X3) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) | ~r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) | ~sP1(X1,X2,X3)) & ((u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) & sP1(X1,X2,X3)) | ~sP2(X3,X1,X0,X2)))),
% 0.21/0.54    inference(flattening,[],[f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ! [X3,X1,X0,X2] : ((sP2(X3,X1,X0,X2) | (u1_waybel_0(X0,X3) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) | ~r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) | ~sP1(X1,X2,X3))) & ((u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) & sP1(X1,X2,X3)) | ~sP2(X3,X1,X0,X2)))),
% 0.21/0.54    inference(nnf_transformation,[],[f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X3,X1,X0,X2] : (sP2(X3,X1,X0,X2) <=> (u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) & sP1(X1,X2,X3)))),
% 0.21/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.54  fof(f126,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (sP2(k4_waybel_9(X0,X1,X2),X1,X0,X2) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X1))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f125,f80])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)) | (~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X1)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_waybel_9)).
% 0.21/0.54  fof(f125,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0) | sP2(k4_waybel_9(X0,X1,X2),X1,X0,X2)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f123,f81])).
% 0.21/0.54  fof(f81,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f28])).
% 0.21/0.54  fof(f123,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) | ~v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0) | sP2(k4_waybel_9(X0,X1,X2),X1,X0,X2)) )),
% 0.21/0.54    inference(resolution,[],[f73,f82])).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~sP3(X0,X1,X2,k4_waybel_9(X1,X2,X0)) | sP2(k4_waybel_9(X1,X2,X0),X2,X1,X0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f59])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (sP2(X3,X2,X1,X0) | k4_waybel_9(X1,X2,X0) != X3 | ~sP3(X0,X1,X2,X3)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (((k4_waybel_9(X1,X2,X0) = X3 | ~sP2(X3,X2,X1,X0)) & (sP2(X3,X2,X1,X0) | k4_waybel_9(X1,X2,X0) != X3)) | ~sP3(X0,X1,X2,X3))),
% 0.21/0.54    inference(rectify,[],[f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ! [X2,X0,X1,X3] : (((k4_waybel_9(X0,X1,X2) = X3 | ~sP2(X3,X1,X0,X2)) & (sP2(X3,X1,X0,X2) | k4_waybel_9(X0,X1,X2) != X3)) | ~sP3(X2,X0,X1,X3))),
% 0.21/0.54    inference(nnf_transformation,[],[f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ! [X2,X0,X1,X3] : ((k4_waybel_9(X0,X1,X2) = X3 <=> sP2(X3,X1,X0,X2)) | ~sP3(X2,X0,X1,X3))),
% 0.21/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (sP3(X2,X0,X1,X3) | ~l1_waybel_0(X3,X0) | ~v6_waybel_0(X3,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (sP3(X2,X0,X1,X3) | ~l1_waybel_0(X3,X0) | ~v6_waybel_0(X3,X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(definition_folding,[],[f18,f32,f31,f30,f29])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k4_waybel_9(X0,X1,X2) = X3 <=> (u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) & ! [X4] : (r2_hidden(X4,u1_struct_0(X3)) <=> ? [X5] : (r1_orders_2(X1,X2,X5) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X1)))))) | ~l1_waybel_0(X3,X0) | ~v6_waybel_0(X3,X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k4_waybel_9(X0,X1,X2) = X3 <=> (u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) & ! [X4] : (r2_hidden(X4,u1_struct_0(X3)) <=> ? [X5] : (r1_orders_2(X1,X2,X5) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X1)))))) | (~l1_waybel_0(X3,X0) | ~v6_waybel_0(X3,X0))) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => ! [X3] : ((l1_waybel_0(X3,X0) & v6_waybel_0(X3,X0)) => (k4_waybel_9(X0,X1,X2) = X3 <=> (u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) & ! [X4] : (r2_hidden(X4,u1_struct_0(X3)) <=> ? [X5] : (r1_orders_2(X1,X2,X5) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X1))))))))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_waybel_9)).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ~r1_tarski(u1_struct_0(k4_waybel_9(sK4,sK5,sK6)),u1_struct_0(sK5))),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ((~r1_tarski(u1_struct_0(k4_waybel_9(sK4,sK5,sK6)),u1_struct_0(sK5)) & m1_subset_1(sK6,u1_struct_0(sK5))) & l1_waybel_0(sK5,sK4) & ~v2_struct_0(sK5)) & l1_struct_0(sK4) & ~v2_struct_0(sK4)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f16,f36,f35,f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) & m1_subset_1(X2,u1_struct_0(X1))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(sK4,X1,X2)),u1_struct_0(X1)) & m1_subset_1(X2,u1_struct_0(X1))) & l1_waybel_0(X1,sK4) & ~v2_struct_0(X1)) & l1_struct_0(sK4) & ~v2_struct_0(sK4))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ? [X1] : (? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(sK4,X1,X2)),u1_struct_0(X1)) & m1_subset_1(X2,u1_struct_0(X1))) & l1_waybel_0(X1,sK4) & ~v2_struct_0(X1)) => (? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(sK4,sK5,X2)),u1_struct_0(sK5)) & m1_subset_1(X2,u1_struct_0(sK5))) & l1_waybel_0(sK5,sK4) & ~v2_struct_0(sK5))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(sK4,sK5,X2)),u1_struct_0(sK5)) & m1_subset_1(X2,u1_struct_0(sK5))) => (~r1_tarski(u1_struct_0(k4_waybel_9(sK4,sK5,sK6)),u1_struct_0(sK5)) & m1_subset_1(sK6,u1_struct_0(sK5)))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) & m1_subset_1(X2,u1_struct_0(X1))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) & m1_subset_1(X2,u1_struct_0(X1))) & (l1_waybel_0(X1,X0) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,negated_conjecture,(
% 0.21/0.54    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)))))),
% 0.21/0.54    inference(negated_conjecture,[],[f8])).
% 0.21/0.54  fof(f8,conjecture,(
% 0.21/0.54    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_waybel_9)).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    m1_subset_1(sK6,u1_struct_0(sK5))),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    l1_waybel_0(sK5,sK4)),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    l1_struct_0(sK4)),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ~v2_struct_0(sK5)),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ~v2_struct_0(sK4)),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (2494)------------------------------
% 0.21/0.54  % (2494)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (2494)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (2494)Memory used [KB]: 1918
% 0.21/0.54  % (2494)Time elapsed: 0.095 s
% 0.21/0.54  % (2494)------------------------------
% 0.21/0.54  % (2494)------------------------------
% 0.21/0.55  % (2461)Success in time 0.185 s
%------------------------------------------------------------------------------
