%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:09 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  200 (2011 expanded)
%              Number of leaves         :   20 ( 820 expanded)
%              Depth                    :   40
%              Number of atoms          : 1071 (23652 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f758,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f81,f375,f394,f401,f611,f627,f744,f757])).

fof(f757,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f756])).

fof(f756,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f755,f45])).

fof(f45,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( ( ( r1_tsep_1(sK4,sK3)
          | r1_tsep_1(sK4,sK2) )
        & ~ r1_tsep_1(sK4,k2_tsep_1(sK1,sK2,sK3)) )
      | sP0(sK4,sK3,sK2,sK1) )
    & ~ r1_tsep_1(sK2,sK3)
    & m1_pre_topc(sK4,sK1)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK1)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f28,f34,f33,f32,f31])).

% (19009)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ( r1_tsep_1(X3,X2)
                          | r1_tsep_1(X3,X1) )
                        & ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) )
                      | sP0(X3,X2,X1,X0) )
                    & ~ r1_tsep_1(X1,X2)
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( r1_tsep_1(X3,X2)
                        | r1_tsep_1(X3,X1) )
                      & ~ r1_tsep_1(X3,k2_tsep_1(sK1,X1,X2)) )
                    | sP0(X3,X2,X1,sK1) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,sK1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK1)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ( ( r1_tsep_1(X3,X2)
                      | r1_tsep_1(X3,X1) )
                    & ~ r1_tsep_1(X3,k2_tsep_1(sK1,X1,X2)) )
                  | sP0(X3,X2,X1,sK1) )
                & ~ r1_tsep_1(X1,X2)
                & m1_pre_topc(X3,sK1)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK1)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X3,sK2) )
                  & ~ r1_tsep_1(X3,k2_tsep_1(sK1,sK2,X2)) )
                | sP0(X3,X2,sK2,sK1) )
              & ~ r1_tsep_1(sK2,X2)
              & m1_pre_topc(X3,sK1)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK1)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK2,sK1)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ( ( r1_tsep_1(X3,X2)
                  | r1_tsep_1(X3,sK2) )
                & ~ r1_tsep_1(X3,k2_tsep_1(sK1,sK2,X2)) )
              | sP0(X3,X2,sK2,sK1) )
            & ~ r1_tsep_1(sK2,X2)
            & m1_pre_topc(X3,sK1)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK1)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ( ( ( r1_tsep_1(X3,sK3)
                | r1_tsep_1(X3,sK2) )
              & ~ r1_tsep_1(X3,k2_tsep_1(sK1,sK2,sK3)) )
            | sP0(X3,sK3,sK2,sK1) )
          & ~ r1_tsep_1(sK2,sK3)
          & m1_pre_topc(X3,sK1)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK3,sK1)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X3] :
        ( ( ( ( r1_tsep_1(X3,sK3)
              | r1_tsep_1(X3,sK2) )
            & ~ r1_tsep_1(X3,k2_tsep_1(sK1,sK2,sK3)) )
          | sP0(X3,sK3,sK2,sK1) )
        & ~ r1_tsep_1(sK2,sK3)
        & m1_pre_topc(X3,sK1)
        & ~ v2_struct_0(X3) )
   => ( ( ( ( r1_tsep_1(sK4,sK3)
            | r1_tsep_1(sK4,sK2) )
          & ~ r1_tsep_1(sK4,k2_tsep_1(sK1,sK2,sK3)) )
        | sP0(sK4,sK3,sK2,sK1) )
      & ~ r1_tsep_1(sK2,sK3)
      & m1_pre_topc(sK4,sK1)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( r1_tsep_1(X3,X2)
                        | r1_tsep_1(X3,X1) )
                      & ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) )
                    | sP0(X3,X2,X1,X0) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f13,f27])).

fof(f27,plain,(
    ! [X3,X2,X1,X0] :
      ( ( ( r1_tsep_1(X2,X3)
          | r1_tsep_1(X1,X3) )
        & ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) )
      | ~ sP0(X3,X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( r1_tsep_1(X3,X2)
                        | r1_tsep_1(X3,X1) )
                      & ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) )
                    | ( ( r1_tsep_1(X2,X3)
                        | r1_tsep_1(X1,X3) )
                      & ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) ) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( r1_tsep_1(X3,X2)
                        | r1_tsep_1(X3,X1) )
                      & ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) )
                    | ( ( r1_tsep_1(X2,X3)
                        | r1_tsep_1(X1,X3) )
                      & ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) ) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( ~ r1_tsep_1(X1,X2)
                     => ( ( ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))
                         => ( ~ r1_tsep_1(X3,X2)
                            & ~ r1_tsep_1(X3,X1) ) )
                        & ( ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
                         => ( ~ r1_tsep_1(X2,X3)
                            & ~ r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ~ r1_tsep_1(X1,X2)
                   => ( ( ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))
                       => ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X3,X1) ) )
                      & ( ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
                       => ( ~ r1_tsep_1(X2,X3)
                          & ~ r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tmap_1)).

fof(f755,plain,
    ( v2_struct_0(sK3)
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f754,f46])).

fof(f46,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f754,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f753,f40])).

fof(f40,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f753,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f752,f42])).

fof(f42,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f752,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f751,f43])).

fof(f43,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f751,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f750,f44])).

fof(f44,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f750,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f749,f203])).

fof(f203,plain,(
    ! [X2,X0,X1] :
      ( l1_struct_0(k2_tsep_1(X2,X1,X0))
      | ~ m1_pre_topc(X1,X2)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X0,X2)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f197,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f197,plain,(
    ! [X6,X4,X5] :
      ( l1_pre_topc(k2_tsep_1(X5,X6,X4))
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X6,X5)
      | v2_struct_0(X6)
      | ~ l1_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,X5) ) ),
    inference(duplicate_literal_removal,[],[f194])).

fof(f194,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_pre_topc(X4,X5)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X6,X5)
      | v2_struct_0(X6)
      | ~ l1_pre_topc(X5)
      | v2_struct_0(X5)
      | l1_pre_topc(k2_tsep_1(X5,X6,X4))
      | ~ l1_pre_topc(X5) ) ),
    inference(resolution,[],[f62,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tsep_1)).

fof(f749,plain,
    ( ~ l1_struct_0(k2_tsep_1(sK1,sK2,sK3))
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f748,f45])).

fof(f748,plain,
    ( v2_struct_0(sK3)
    | ~ l1_struct_0(k2_tsep_1(sK1,sK2,sK3))
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f747,f46])).

fof(f747,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ l1_struct_0(k2_tsep_1(sK1,sK2,sK3))
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f745,f49])).

fof(f49,plain,(
    ~ r1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f745,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ l1_struct_0(k2_tsep_1(sK1,sK2,sK3))
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f67,f726])).

fof(f726,plain,
    ( ! [X1] :
        ( ~ sP0(sK4,X1,sK2,sK1)
        | r1_tsep_1(sK2,X1)
        | ~ m1_pre_topc(X1,sK1)
        | v2_struct_0(X1)
        | ~ l1_struct_0(k2_tsep_1(sK1,sK2,X1)) )
    | ~ spl5_2 ),
    inference(resolution,[],[f724,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(k2_tsep_1(X3,X2,X1),X0)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r1_tsep_1(X1,X0)
          | r1_tsep_1(X2,X0) )
        & ~ r1_tsep_1(k2_tsep_1(X3,X2,X1),X0) )
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X3,X2,X1,X0] :
      ( ( ( r1_tsep_1(X2,X3)
          | r1_tsep_1(X1,X3) )
        & ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) )
      | ~ sP0(X3,X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f724,plain,
    ( ! [X0] :
        ( r1_tsep_1(k2_tsep_1(sK1,sK2,X0),sK4)
        | ~ l1_struct_0(k2_tsep_1(sK1,sK2,X0))
        | r1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(X0) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f723,f43])).

fof(f723,plain,
    ( ! [X0] :
        ( r1_tsep_1(k2_tsep_1(sK1,sK2,X0),sK4)
        | ~ l1_struct_0(k2_tsep_1(sK1,sK2,X0))
        | r1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(X0)
        | v2_struct_0(sK2) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f722,f40])).

fof(f722,plain,
    ( ! [X0] :
        ( r1_tsep_1(k2_tsep_1(sK1,sK2,X0),sK4)
        | ~ l1_struct_0(k2_tsep_1(sK1,sK2,X0))
        | r1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(X0)
        | v2_struct_0(sK1)
        | v2_struct_0(sK2) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f721,f41])).

fof(f41,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f721,plain,
    ( ! [X0] :
        ( r1_tsep_1(k2_tsep_1(sK1,sK2,X0),sK4)
        | ~ l1_struct_0(k2_tsep_1(sK1,sK2,X0))
        | r1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | v2_struct_0(sK2) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f720,f42])).

fof(f720,plain,
    ( ! [X0] :
        ( r1_tsep_1(k2_tsep_1(sK1,sK2,X0),sK4)
        | ~ l1_struct_0(k2_tsep_1(sK1,sK2,X0))
        | r1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | v2_struct_0(sK2) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f719,f44])).

fof(f719,plain,
    ( ! [X0] :
        ( r1_tsep_1(k2_tsep_1(sK1,sK2,X0),sK4)
        | ~ l1_struct_0(k2_tsep_1(sK1,sK2,X0))
        | r1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK2,sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | v2_struct_0(sK2) )
    | ~ spl5_2 ),
    inference(duplicate_literal_removal,[],[f716])).

fof(f716,plain,
    ( ! [X0] :
        ( r1_tsep_1(k2_tsep_1(sK1,sK2,X0),sK4)
        | ~ l1_struct_0(k2_tsep_1(sK1,sK2,X0))
        | r1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK2,sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK2,sK1)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | ~ spl5_2 ),
    inference(resolution,[],[f648,f62])).

fof(f648,plain,
    ( ! [X2,X3] :
        ( ~ m1_pre_topc(k2_tsep_1(X2,sK2,X3),sK1)
        | r1_tsep_1(k2_tsep_1(X2,sK2,X3),sK4)
        | ~ l1_struct_0(k2_tsep_1(X2,sK2,X3))
        | r1_tsep_1(sK2,X3)
        | ~ m1_pre_topc(X3,X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(sK2,X2)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f644,f43])).

fof(f644,plain,
    ( ! [X2,X3] :
        ( ~ m1_pre_topc(k2_tsep_1(X2,sK2,X3),sK1)
        | r1_tsep_1(k2_tsep_1(X2,sK2,X3),sK4)
        | ~ l1_struct_0(k2_tsep_1(X2,sK2,X3))
        | r1_tsep_1(sK2,X3)
        | ~ m1_pre_topc(X3,X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(sK2,X2)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl5_2 ),
    inference(resolution,[],[f635,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X1)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X2)
                & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X2)
                & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ~ r1_tsep_1(X1,X2)
               => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X2)
                  & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tsep_1)).

fof(f635,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | ~ m1_pre_topc(X0,sK1)
        | r1_tsep_1(X0,sK4)
        | ~ l1_struct_0(X0) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f633,f91])).

fof(f91,plain,(
    l1_struct_0(sK4) ),
    inference(resolution,[],[f88,f54])).

fof(f88,plain,(
    l1_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f85,f42])).

fof(f85,plain,
    ( l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f55,f48])).

fof(f48,plain,(
    m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f633,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(sK4)
        | ~ m1_pre_topc(X0,sK2)
        | ~ m1_pre_topc(X0,sK1)
        | r1_tsep_1(X0,sK4)
        | ~ l1_struct_0(X0) )
    | ~ spl5_2 ),
    inference(resolution,[],[f94,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(sK2,X1)
      | ~ l1_struct_0(X1)
      | ~ m1_pre_topc(X0,sK2)
      | ~ m1_pre_topc(X0,sK1)
      | r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK1)
      | ~ l1_struct_0(X1)
      | ~ m1_pre_topc(X0,sK2)
      | ~ r1_tsep_1(sK2,X1)
      | r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(resolution,[],[f110,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f110,plain,(
    ! [X2,X3] :
      ( r1_xboole_0(u1_struct_0(X2),u1_struct_0(X3))
      | ~ m1_pre_topc(X2,sK1)
      | ~ l1_struct_0(X3)
      | ~ m1_pre_topc(X2,sK2)
      | ~ r1_tsep_1(sK2,X3) ) ),
    inference(subsumption_resolution,[],[f109,f89])).

fof(f89,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f86,f54])).

fof(f86,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f83,f42])).

fof(f83,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f55,f44])).

fof(f109,plain,(
    ! [X2,X3] :
      ( ~ m1_pre_topc(X2,sK2)
      | ~ m1_pre_topc(X2,sK1)
      | ~ l1_struct_0(X3)
      | ~ l1_struct_0(sK2)
      | r1_xboole_0(u1_struct_0(X2),u1_struct_0(X3))
      | ~ r1_tsep_1(sK2,X3) ) ),
    inference(resolution,[],[f103,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,u1_struct_0(X0))
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0)
      | r1_xboole_0(X2,u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1) ) ),
    inference(resolution,[],[f52,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f103,plain,(
    ! [X0] :
      ( r1_tarski(u1_struct_0(X0),u1_struct_0(sK2))
      | ~ m1_pre_topc(X0,sK2)
      | ~ m1_pre_topc(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f102,f41])).

fof(f102,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2))
      | ~ m1_pre_topc(X0,sK1)
      | ~ v2_pre_topc(sK1) ) ),
    inference(subsumption_resolution,[],[f99,f42])).

% (19020)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
fof(f99,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2))
      | ~ m1_pre_topc(X0,sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1) ) ),
    inference(resolution,[],[f59,f44])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X2)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f94,plain,
    ( r1_tsep_1(sK2,sK4)
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f93,f91])).

fof(f93,plain,
    ( r1_tsep_1(sK2,sK4)
    | ~ l1_struct_0(sK4)
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f92,f89])).

fof(f92,plain,
    ( r1_tsep_1(sK2,sK4)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK4)
    | ~ spl5_2 ),
    inference(resolution,[],[f60,f71])).

fof(f71,plain,
    ( r1_tsep_1(sK4,sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl5_2
  <=> r1_tsep_1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | r1_tsep_1(X1,X0)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f67,plain,
    ( sP0(sK4,sK3,sK2,sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl5_1
  <=> sP0(sK4,sK3,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f744,plain,
    ( ~ spl5_2
    | spl5_4 ),
    inference(avatar_contradiction_clause,[],[f743])).

fof(f743,plain,
    ( $false
    | ~ spl5_2
    | spl5_4 ),
    inference(subsumption_resolution,[],[f742,f45])).

fof(f742,plain,
    ( v2_struct_0(sK3)
    | ~ spl5_2
    | spl5_4 ),
    inference(subsumption_resolution,[],[f741,f46])).

fof(f741,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ spl5_2
    | spl5_4 ),
    inference(subsumption_resolution,[],[f740,f40])).

fof(f740,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ spl5_2
    | spl5_4 ),
    inference(subsumption_resolution,[],[f739,f42])).

fof(f739,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ spl5_2
    | spl5_4 ),
    inference(subsumption_resolution,[],[f738,f43])).

fof(f738,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ spl5_2
    | spl5_4 ),
    inference(subsumption_resolution,[],[f737,f44])).

fof(f737,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ spl5_2
    | spl5_4 ),
    inference(resolution,[],[f736,f203])).

fof(f736,plain,
    ( ~ l1_struct_0(k2_tsep_1(sK1,sK2,sK3))
    | ~ spl5_2
    | spl5_4 ),
    inference(subsumption_resolution,[],[f735,f45])).

fof(f735,plain,
    ( v2_struct_0(sK3)
    | ~ l1_struct_0(k2_tsep_1(sK1,sK2,sK3))
    | ~ spl5_2
    | spl5_4 ),
    inference(subsumption_resolution,[],[f734,f46])).

fof(f734,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ l1_struct_0(k2_tsep_1(sK1,sK2,sK3))
    | ~ spl5_2
    | spl5_4 ),
    inference(subsumption_resolution,[],[f729,f49])).

fof(f729,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ l1_struct_0(k2_tsep_1(sK1,sK2,sK3))
    | ~ spl5_2
    | spl5_4 ),
    inference(resolution,[],[f728,f80])).

fof(f80,plain,
    ( ~ r1_tsep_1(sK4,k2_tsep_1(sK1,sK2,sK3))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl5_4
  <=> r1_tsep_1(sK4,k2_tsep_1(sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f728,plain,
    ( ! [X0] :
        ( r1_tsep_1(sK4,k2_tsep_1(sK1,sK2,X0))
        | r1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(X0)
        | ~ l1_struct_0(k2_tsep_1(sK1,sK2,X0)) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f727,f91])).

fof(f727,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(k2_tsep_1(sK1,sK2,X0))
        | r1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(X0)
        | r1_tsep_1(sK4,k2_tsep_1(sK1,sK2,X0))
        | ~ l1_struct_0(sK4) )
    | ~ spl5_2 ),
    inference(duplicate_literal_removal,[],[f725])).

fof(f725,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(k2_tsep_1(sK1,sK2,X0))
        | r1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(X0)
        | r1_tsep_1(sK4,k2_tsep_1(sK1,sK2,X0))
        | ~ l1_struct_0(sK4)
        | ~ l1_struct_0(k2_tsep_1(sK1,sK2,X0)) )
    | ~ spl5_2 ),
    inference(resolution,[],[f724,f60])).

fof(f627,plain,
    ( ~ spl5_3
    | spl5_4 ),
    inference(avatar_contradiction_clause,[],[f626])).

fof(f626,plain,
    ( $false
    | ~ spl5_3
    | spl5_4 ),
    inference(subsumption_resolution,[],[f625,f45])).

fof(f625,plain,
    ( v2_struct_0(sK3)
    | ~ spl5_3
    | spl5_4 ),
    inference(subsumption_resolution,[],[f624,f46])).

fof(f624,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ spl5_3
    | spl5_4 ),
    inference(subsumption_resolution,[],[f623,f40])).

fof(f623,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ spl5_3
    | spl5_4 ),
    inference(subsumption_resolution,[],[f622,f42])).

fof(f622,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ spl5_3
    | spl5_4 ),
    inference(subsumption_resolution,[],[f621,f43])).

fof(f621,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ spl5_3
    | spl5_4 ),
    inference(subsumption_resolution,[],[f620,f44])).

fof(f620,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ spl5_3
    | spl5_4 ),
    inference(resolution,[],[f619,f203])).

fof(f619,plain,
    ( ~ l1_struct_0(k2_tsep_1(sK1,sK2,sK3))
    | ~ spl5_3
    | spl5_4 ),
    inference(subsumption_resolution,[],[f618,f43])).

fof(f618,plain,
    ( v2_struct_0(sK2)
    | ~ l1_struct_0(k2_tsep_1(sK1,sK2,sK3))
    | ~ spl5_3
    | spl5_4 ),
    inference(subsumption_resolution,[],[f617,f44])).

fof(f617,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK2)
    | ~ l1_struct_0(k2_tsep_1(sK1,sK2,sK3))
    | ~ spl5_3
    | spl5_4 ),
    inference(subsumption_resolution,[],[f612,f49])).

fof(f612,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK2)
    | ~ l1_struct_0(k2_tsep_1(sK1,sK2,sK3))
    | ~ spl5_3
    | spl5_4 ),
    inference(resolution,[],[f599,f80])).

fof(f599,plain,
    ( ! [X0] :
        ( r1_tsep_1(sK4,k2_tsep_1(sK1,X0,sK3))
        | r1_tsep_1(X0,sK3)
        | ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(X0)
        | ~ l1_struct_0(k2_tsep_1(sK1,X0,sK3)) )
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f598,f91])).

fof(f598,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(k2_tsep_1(sK1,X0,sK3))
        | r1_tsep_1(X0,sK3)
        | ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(X0)
        | r1_tsep_1(sK4,k2_tsep_1(sK1,X0,sK3))
        | ~ l1_struct_0(sK4) )
    | ~ spl5_3 ),
    inference(duplicate_literal_removal,[],[f596])).

fof(f596,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(k2_tsep_1(sK1,X0,sK3))
        | r1_tsep_1(X0,sK3)
        | ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(X0)
        | r1_tsep_1(sK4,k2_tsep_1(sK1,X0,sK3))
        | ~ l1_struct_0(sK4)
        | ~ l1_struct_0(k2_tsep_1(sK1,X0,sK3)) )
    | ~ spl5_3 ),
    inference(resolution,[],[f595,f60])).

fof(f595,plain,
    ( ! [X0] :
        ( r1_tsep_1(k2_tsep_1(sK1,X0,sK3),sK4)
        | ~ l1_struct_0(k2_tsep_1(sK1,X0,sK3))
        | r1_tsep_1(X0,sK3)
        | ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(X0) )
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f594,f45])).

fof(f594,plain,
    ( ! [X0] :
        ( r1_tsep_1(k2_tsep_1(sK1,X0,sK3),sK4)
        | ~ l1_struct_0(k2_tsep_1(sK1,X0,sK3))
        | r1_tsep_1(X0,sK3)
        | ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(X0)
        | v2_struct_0(sK3) )
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f593,f40])).

fof(f593,plain,
    ( ! [X0] :
        ( r1_tsep_1(k2_tsep_1(sK1,X0,sK3),sK4)
        | ~ l1_struct_0(k2_tsep_1(sK1,X0,sK3))
        | r1_tsep_1(X0,sK3)
        | ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(X0)
        | v2_struct_0(sK1)
        | v2_struct_0(sK3) )
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f592,f41])).

fof(f592,plain,
    ( ! [X0] :
        ( r1_tsep_1(k2_tsep_1(sK1,X0,sK3),sK4)
        | ~ l1_struct_0(k2_tsep_1(sK1,X0,sK3))
        | r1_tsep_1(X0,sK3)
        | ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | v2_struct_0(sK3) )
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f591,f42])).

fof(f591,plain,
    ( ! [X0] :
        ( r1_tsep_1(k2_tsep_1(sK1,X0,sK3),sK4)
        | ~ l1_struct_0(k2_tsep_1(sK1,X0,sK3))
        | r1_tsep_1(X0,sK3)
        | ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | v2_struct_0(sK3) )
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f590,f46])).

fof(f590,plain,
    ( ! [X0] :
        ( r1_tsep_1(k2_tsep_1(sK1,X0,sK3),sK4)
        | ~ l1_struct_0(k2_tsep_1(sK1,X0,sK3))
        | r1_tsep_1(X0,sK3)
        | ~ m1_pre_topc(sK3,sK1)
        | ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | v2_struct_0(sK3) )
    | ~ spl5_3 ),
    inference(duplicate_literal_removal,[],[f587])).

fof(f587,plain,
    ( ! [X0] :
        ( r1_tsep_1(k2_tsep_1(sK1,X0,sK3),sK4)
        | ~ l1_struct_0(k2_tsep_1(sK1,X0,sK3))
        | r1_tsep_1(X0,sK3)
        | ~ m1_pre_topc(sK3,sK1)
        | ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK3,sK1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | ~ spl5_3 ),
    inference(resolution,[],[f436,f62])).

fof(f436,plain,
    ( ! [X4,X5] :
        ( ~ m1_pre_topc(k2_tsep_1(X4,X5,sK3),sK1)
        | r1_tsep_1(k2_tsep_1(X4,X5,sK3),sK4)
        | ~ l1_struct_0(k2_tsep_1(X4,X5,sK3))
        | r1_tsep_1(X5,sK3)
        | ~ m1_pre_topc(sK3,X4)
        | ~ m1_pre_topc(X5,X4)
        | v2_struct_0(X5)
        | ~ l1_pre_topc(X4)
        | ~ v2_pre_topc(X4)
        | v2_struct_0(X4) )
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f432,f45])).

fof(f432,plain,
    ( ! [X4,X5] :
        ( ~ m1_pre_topc(k2_tsep_1(X4,X5,sK3),sK1)
        | r1_tsep_1(k2_tsep_1(X4,X5,sK3),sK4)
        | ~ l1_struct_0(k2_tsep_1(X4,X5,sK3))
        | r1_tsep_1(X5,sK3)
        | ~ m1_pre_topc(sK3,X4)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X5,X4)
        | v2_struct_0(X5)
        | ~ l1_pre_topc(X4)
        | ~ v2_pre_topc(X4)
        | v2_struct_0(X4) )
    | ~ spl5_3 ),
    inference(resolution,[],[f409,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X2)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f409,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(X0,sK1)
        | r1_tsep_1(X0,sK4)
        | ~ l1_struct_0(X0) )
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f407,f91])).

fof(f407,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(sK4)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(X0,sK1)
        | r1_tsep_1(X0,sK4)
        | ~ l1_struct_0(X0) )
    | ~ spl5_3 ),
    inference(resolution,[],[f299,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(sK3,X1)
      | ~ l1_struct_0(X1)
      | ~ m1_pre_topc(X0,sK3)
      | ~ m1_pre_topc(X0,sK1)
      | r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK1)
      | ~ l1_struct_0(X1)
      | ~ m1_pre_topc(X0,sK3)
      | ~ r1_tsep_1(sK3,X1)
      | r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(resolution,[],[f113,f53])).

fof(f113,plain,(
    ! [X2,X3] :
      ( r1_xboole_0(u1_struct_0(X2),u1_struct_0(X3))
      | ~ m1_pre_topc(X2,sK1)
      | ~ l1_struct_0(X3)
      | ~ m1_pre_topc(X2,sK3)
      | ~ r1_tsep_1(sK3,X3) ) ),
    inference(subsumption_resolution,[],[f112,f90])).

fof(f90,plain,(
    l1_struct_0(sK3) ),
    inference(resolution,[],[f87,f54])).

fof(f87,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f84,f42])).

fof(f84,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f55,f46])).

fof(f112,plain,(
    ! [X2,X3] :
      ( ~ m1_pre_topc(X2,sK3)
      | ~ m1_pre_topc(X2,sK1)
      | ~ l1_struct_0(X3)
      | ~ l1_struct_0(sK3)
      | r1_xboole_0(u1_struct_0(X2),u1_struct_0(X3))
      | ~ r1_tsep_1(sK3,X3) ) ),
    inference(resolution,[],[f105,f96])).

fof(f105,plain,(
    ! [X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(sK3))
      | ~ m1_pre_topc(X1,sK3)
      | ~ m1_pre_topc(X1,sK1) ) ),
    inference(subsumption_resolution,[],[f104,f41])).

fof(f104,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK3)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(sK3))
      | ~ m1_pre_topc(X1,sK1)
      | ~ v2_pre_topc(sK1) ) ),
    inference(subsumption_resolution,[],[f100,f42])).

fof(f100,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK3)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(sK3))
      | ~ m1_pre_topc(X1,sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1) ) ),
    inference(resolution,[],[f59,f46])).

fof(f299,plain,
    ( r1_tsep_1(sK3,sK4)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f298,f91])).

fof(f298,plain,
    ( r1_tsep_1(sK3,sK4)
    | ~ l1_struct_0(sK4)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f296,f90])).

fof(f296,plain,
    ( r1_tsep_1(sK3,sK4)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK4)
    | ~ spl5_3 ),
    inference(resolution,[],[f75,f60])).

fof(f75,plain,
    ( r1_tsep_1(sK4,sK3)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl5_3
  <=> r1_tsep_1(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f611,plain,
    ( ~ spl5_1
    | ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f610])).

fof(f610,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f609,f45])).

fof(f609,plain,
    ( v2_struct_0(sK3)
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f608,f46])).

fof(f608,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f607,f40])).

fof(f607,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f606,f42])).

fof(f606,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f605,f43])).

fof(f605,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f604,f44])).

fof(f604,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(resolution,[],[f603,f203])).

fof(f603,plain,
    ( ~ l1_struct_0(k2_tsep_1(sK1,sK2,sK3))
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f602,f43])).

fof(f602,plain,
    ( v2_struct_0(sK2)
    | ~ l1_struct_0(k2_tsep_1(sK1,sK2,sK3))
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f601,f44])).

fof(f601,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK2)
    | ~ l1_struct_0(k2_tsep_1(sK1,sK2,sK3))
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f600,f49])).

fof(f600,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK2)
    | ~ l1_struct_0(k2_tsep_1(sK1,sK2,sK3))
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(resolution,[],[f597,f67])).

fof(f597,plain,
    ( ! [X1] :
        ( ~ sP0(sK4,sK3,X1,sK1)
        | r1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK1)
        | v2_struct_0(X1)
        | ~ l1_struct_0(k2_tsep_1(sK1,X1,sK3)) )
    | ~ spl5_3 ),
    inference(resolution,[],[f595,f38])).

fof(f401,plain,
    ( spl5_2
    | ~ spl5_34 ),
    inference(avatar_contradiction_clause,[],[f400])).

fof(f400,plain,
    ( $false
    | spl5_2
    | ~ spl5_34 ),
    inference(subsumption_resolution,[],[f399,f89])).

fof(f399,plain,
    ( ~ l1_struct_0(sK2)
    | spl5_2
    | ~ spl5_34 ),
    inference(subsumption_resolution,[],[f398,f91])).

fof(f398,plain,
    ( ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK2)
    | spl5_2
    | ~ spl5_34 ),
    inference(subsumption_resolution,[],[f396,f70])).

fof(f70,plain,
    ( ~ r1_tsep_1(sK4,sK2)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f396,plain,
    ( r1_tsep_1(sK4,sK2)
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK2)
    | ~ spl5_34 ),
    inference(resolution,[],[f374,f60])).

fof(f374,plain,
    ( r1_tsep_1(sK2,sK4)
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f372])).

fof(f372,plain,
    ( spl5_34
  <=> r1_tsep_1(sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f394,plain,
    ( spl5_3
    | ~ spl5_33 ),
    inference(avatar_contradiction_clause,[],[f393])).

% (19021)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
fof(f393,plain,
    ( $false
    | spl5_3
    | ~ spl5_33 ),
    inference(subsumption_resolution,[],[f392,f90])).

fof(f392,plain,
    ( ~ l1_struct_0(sK3)
    | spl5_3
    | ~ spl5_33 ),
    inference(subsumption_resolution,[],[f391,f91])).

fof(f391,plain,
    ( ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK3)
    | spl5_3
    | ~ spl5_33 ),
    inference(subsumption_resolution,[],[f389,f74])).

fof(f74,plain,
    ( ~ r1_tsep_1(sK4,sK3)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f389,plain,
    ( r1_tsep_1(sK4,sK3)
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK3)
    | ~ spl5_33 ),
    inference(resolution,[],[f370,f60])).

fof(f370,plain,
    ( r1_tsep_1(sK3,sK4)
    | ~ spl5_33 ),
    inference(avatar_component_clause,[],[f368])).

fof(f368,plain,
    ( spl5_33
  <=> r1_tsep_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f375,plain,
    ( spl5_33
    | spl5_34
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f366,f65,f372,f368])).

fof(f366,plain,
    ( r1_tsep_1(sK2,sK4)
    | r1_tsep_1(sK3,sK4)
    | ~ spl5_1 ),
    inference(resolution,[],[f67,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | r1_tsep_1(X2,X0)
      | r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f81,plain,
    ( spl5_1
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f50,f78,f65])).

fof(f50,plain,
    ( ~ r1_tsep_1(sK4,k2_tsep_1(sK1,sK2,sK3))
    | sP0(sK4,sK3,sK2,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f76,plain,
    ( spl5_1
    | spl5_2
    | spl5_3 ),
    inference(avatar_split_clause,[],[f51,f73,f69,f65])).

fof(f51,plain,
    ( r1_tsep_1(sK4,sK3)
    | r1_tsep_1(sK4,sK2)
    | sP0(sK4,sK3,sK2,sK1) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.11/0.33  % Computer   : n020.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 19:25:37 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.19/0.46  % (19012)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.19/0.47  % (19013)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.19/0.48  % (19010)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.19/0.49  % (19006)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 0.19/0.49  % (19019)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.19/0.49  % (19022)ott+11_5:1_afp=100000:afq=1.1:br=off:gs=on:nm=64:nwc=1:sos=all:urr=on:updr=off_287 on theBenchmark
% 0.19/0.49  % (19011)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.19/0.50  % (19005)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.19/0.50  % (19012)Refutation found. Thanks to Tanya!
% 0.19/0.50  % SZS status Theorem for theBenchmark
% 0.19/0.50  % (19014)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.19/0.50  % SZS output start Proof for theBenchmark
% 0.19/0.50  fof(f758,plain,(
% 0.19/0.50    $false),
% 0.19/0.50    inference(avatar_sat_refutation,[],[f76,f81,f375,f394,f401,f611,f627,f744,f757])).
% 0.19/0.50  fof(f757,plain,(
% 0.19/0.50    ~spl5_1 | ~spl5_2),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f756])).
% 0.19/0.50  fof(f756,plain,(
% 0.19/0.50    $false | (~spl5_1 | ~spl5_2)),
% 0.19/0.50    inference(subsumption_resolution,[],[f755,f45])).
% 0.19/0.50  fof(f45,plain,(
% 0.19/0.50    ~v2_struct_0(sK3)),
% 0.19/0.50    inference(cnf_transformation,[],[f35])).
% 0.19/0.50  fof(f35,plain,(
% 0.19/0.50    ((((((r1_tsep_1(sK4,sK3) | r1_tsep_1(sK4,sK2)) & ~r1_tsep_1(sK4,k2_tsep_1(sK1,sK2,sK3))) | sP0(sK4,sK3,sK2,sK1)) & ~r1_tsep_1(sK2,sK3) & m1_pre_topc(sK4,sK1) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 0.19/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f28,f34,f33,f32,f31])).
% 0.19/0.50  % (19009)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.19/0.50  fof(f31,plain,(
% 0.19/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(X3,X2) | r1_tsep_1(X3,X1)) & ~r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))) | sP0(X3,X2,X1,X0)) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(X3,X2) | r1_tsep_1(X3,X1)) & ~r1_tsep_1(X3,k2_tsep_1(sK1,X1,X2))) | sP0(X3,X2,X1,sK1)) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f32,plain,(
% 0.19/0.50    ? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(X3,X2) | r1_tsep_1(X3,X1)) & ~r1_tsep_1(X3,k2_tsep_1(sK1,X1,X2))) | sP0(X3,X2,X1,sK1)) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : ((((r1_tsep_1(X3,X2) | r1_tsep_1(X3,sK2)) & ~r1_tsep_1(X3,k2_tsep_1(sK1,sK2,X2))) | sP0(X3,X2,sK2,sK1)) & ~r1_tsep_1(sK2,X2) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f33,plain,(
% 0.19/0.50    ? [X2] : (? [X3] : ((((r1_tsep_1(X3,X2) | r1_tsep_1(X3,sK2)) & ~r1_tsep_1(X3,k2_tsep_1(sK1,sK2,X2))) | sP0(X3,X2,sK2,sK1)) & ~r1_tsep_1(sK2,X2) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) => (? [X3] : ((((r1_tsep_1(X3,sK3) | r1_tsep_1(X3,sK2)) & ~r1_tsep_1(X3,k2_tsep_1(sK1,sK2,sK3))) | sP0(X3,sK3,sK2,sK1)) & ~r1_tsep_1(sK2,sK3) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f34,plain,(
% 0.19/0.50    ? [X3] : ((((r1_tsep_1(X3,sK3) | r1_tsep_1(X3,sK2)) & ~r1_tsep_1(X3,k2_tsep_1(sK1,sK2,sK3))) | sP0(X3,sK3,sK2,sK1)) & ~r1_tsep_1(sK2,sK3) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) => ((((r1_tsep_1(sK4,sK3) | r1_tsep_1(sK4,sK2)) & ~r1_tsep_1(sK4,k2_tsep_1(sK1,sK2,sK3))) | sP0(sK4,sK3,sK2,sK1)) & ~r1_tsep_1(sK2,sK3) & m1_pre_topc(sK4,sK1) & ~v2_struct_0(sK4))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f28,plain,(
% 0.19/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(X3,X2) | r1_tsep_1(X3,X1)) & ~r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))) | sP0(X3,X2,X1,X0)) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.19/0.50    inference(definition_folding,[],[f13,f27])).
% 0.19/0.50  fof(f27,plain,(
% 0.19/0.50    ! [X3,X2,X1,X0] : (((r1_tsep_1(X2,X3) | r1_tsep_1(X1,X3)) & ~r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)) | ~sP0(X3,X2,X1,X0))),
% 0.19/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.19/0.50  fof(f13,plain,(
% 0.19/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(X3,X2) | r1_tsep_1(X3,X1)) & ~r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))) | ((r1_tsep_1(X2,X3) | r1_tsep_1(X1,X3)) & ~r1_tsep_1(k2_tsep_1(X0,X1,X2),X3))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.19/0.50    inference(flattening,[],[f12])).
% 0.19/0.50  fof(f12,plain,(
% 0.19/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((((r1_tsep_1(X3,X2) | r1_tsep_1(X3,X1)) & ~r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))) | ((r1_tsep_1(X2,X3) | r1_tsep_1(X1,X3)) & ~r1_tsep_1(k2_tsep_1(X0,X1,X2),X3))) & ~r1_tsep_1(X1,X2)) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.19/0.50    inference(ennf_transformation,[],[f10])).
% 0.19/0.50  fof(f10,negated_conjecture,(
% 0.19/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X1,X2) => ((~r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) => (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X3,X1))) & (~r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) => (~r1_tsep_1(X2,X3) & ~r1_tsep_1(X1,X3)))))))))),
% 0.19/0.50    inference(negated_conjecture,[],[f9])).
% 0.19/0.50  fof(f9,conjecture,(
% 0.19/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X1,X2) => ((~r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) => (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X3,X1))) & (~r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) => (~r1_tsep_1(X2,X3) & ~r1_tsep_1(X1,X3)))))))))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tmap_1)).
% 0.19/0.50  fof(f755,plain,(
% 0.19/0.50    v2_struct_0(sK3) | (~spl5_1 | ~spl5_2)),
% 0.19/0.50    inference(subsumption_resolution,[],[f754,f46])).
% 0.19/0.50  fof(f46,plain,(
% 0.19/0.50    m1_pre_topc(sK3,sK1)),
% 0.19/0.50    inference(cnf_transformation,[],[f35])).
% 0.19/0.50  fof(f754,plain,(
% 0.19/0.50    ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | (~spl5_1 | ~spl5_2)),
% 0.19/0.50    inference(subsumption_resolution,[],[f753,f40])).
% 0.19/0.50  fof(f40,plain,(
% 0.19/0.50    ~v2_struct_0(sK1)),
% 0.19/0.50    inference(cnf_transformation,[],[f35])).
% 0.19/0.50  fof(f753,plain,(
% 0.19/0.50    v2_struct_0(sK1) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | (~spl5_1 | ~spl5_2)),
% 0.19/0.50    inference(subsumption_resolution,[],[f752,f42])).
% 0.19/0.50  fof(f42,plain,(
% 0.19/0.50    l1_pre_topc(sK1)),
% 0.19/0.50    inference(cnf_transformation,[],[f35])).
% 0.19/0.50  fof(f752,plain,(
% 0.19/0.50    ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | (~spl5_1 | ~spl5_2)),
% 0.19/0.50    inference(subsumption_resolution,[],[f751,f43])).
% 0.19/0.50  fof(f43,plain,(
% 0.19/0.50    ~v2_struct_0(sK2)),
% 0.19/0.50    inference(cnf_transformation,[],[f35])).
% 0.19/0.50  fof(f751,plain,(
% 0.19/0.50    v2_struct_0(sK2) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | (~spl5_1 | ~spl5_2)),
% 0.19/0.50    inference(subsumption_resolution,[],[f750,f44])).
% 0.19/0.50  fof(f44,plain,(
% 0.19/0.50    m1_pre_topc(sK2,sK1)),
% 0.19/0.50    inference(cnf_transformation,[],[f35])).
% 0.19/0.50  fof(f750,plain,(
% 0.19/0.50    ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | (~spl5_1 | ~spl5_2)),
% 0.19/0.50    inference(resolution,[],[f749,f203])).
% 0.19/0.50  fof(f203,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (l1_struct_0(k2_tsep_1(X2,X1,X0)) | ~m1_pre_topc(X1,X2) | v2_struct_0(X1) | ~l1_pre_topc(X2) | v2_struct_0(X2) | ~m1_pre_topc(X0,X2) | v2_struct_0(X0)) )),
% 0.19/0.50    inference(resolution,[],[f197,f54])).
% 0.19/0.50  fof(f54,plain,(
% 0.19/0.50    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f15])).
% 0.19/0.50  fof(f15,plain,(
% 0.19/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.19/0.50    inference(ennf_transformation,[],[f2])).
% 0.19/0.50  fof(f2,axiom,(
% 0.19/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.19/0.50  fof(f197,plain,(
% 0.19/0.50    ( ! [X6,X4,X5] : (l1_pre_topc(k2_tsep_1(X5,X6,X4)) | v2_struct_0(X4) | ~m1_pre_topc(X6,X5) | v2_struct_0(X6) | ~l1_pre_topc(X5) | v2_struct_0(X5) | ~m1_pre_topc(X4,X5)) )),
% 0.19/0.50    inference(duplicate_literal_removal,[],[f194])).
% 0.19/0.50  fof(f194,plain,(
% 0.19/0.50    ( ! [X6,X4,X5] : (~m1_pre_topc(X4,X5) | v2_struct_0(X4) | ~m1_pre_topc(X6,X5) | v2_struct_0(X6) | ~l1_pre_topc(X5) | v2_struct_0(X5) | l1_pre_topc(k2_tsep_1(X5,X6,X4)) | ~l1_pre_topc(X5)) )),
% 0.19/0.50    inference(resolution,[],[f62,f55])).
% 0.19/0.50  fof(f55,plain,(
% 0.19/0.50    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f16])).
% 0.19/0.50  fof(f16,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.19/0.50    inference(ennf_transformation,[],[f3])).
% 0.19/0.50  fof(f3,axiom,(
% 0.19/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.19/0.50  fof(f62,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f24])).
% 0.19/0.50  fof(f24,plain,(
% 0.19/0.50    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.50    inference(flattening,[],[f23])).
% 0.19/0.50  fof(f23,plain,(
% 0.19/0.50    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.50    inference(ennf_transformation,[],[f11])).
% 0.19/0.50  fof(f11,plain,(
% 0.19/0.50    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))))),
% 0.19/0.50    inference(pure_predicate_removal,[],[f5])).
% 0.19/0.50  fof(f5,axiom,(
% 0.19/0.50    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tsep_1)).
% 0.19/0.50  fof(f749,plain,(
% 0.19/0.50    ~l1_struct_0(k2_tsep_1(sK1,sK2,sK3)) | (~spl5_1 | ~spl5_2)),
% 0.19/0.50    inference(subsumption_resolution,[],[f748,f45])).
% 0.19/0.50  fof(f748,plain,(
% 0.19/0.50    v2_struct_0(sK3) | ~l1_struct_0(k2_tsep_1(sK1,sK2,sK3)) | (~spl5_1 | ~spl5_2)),
% 0.19/0.50    inference(subsumption_resolution,[],[f747,f46])).
% 0.19/0.50  fof(f747,plain,(
% 0.19/0.50    ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | ~l1_struct_0(k2_tsep_1(sK1,sK2,sK3)) | (~spl5_1 | ~spl5_2)),
% 0.19/0.50    inference(subsumption_resolution,[],[f745,f49])).
% 0.19/0.50  fof(f49,plain,(
% 0.19/0.50    ~r1_tsep_1(sK2,sK3)),
% 0.19/0.50    inference(cnf_transformation,[],[f35])).
% 0.19/0.50  fof(f745,plain,(
% 0.19/0.50    r1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | ~l1_struct_0(k2_tsep_1(sK1,sK2,sK3)) | (~spl5_1 | ~spl5_2)),
% 0.19/0.50    inference(resolution,[],[f67,f726])).
% 0.19/0.50  fof(f726,plain,(
% 0.19/0.50    ( ! [X1] : (~sP0(sK4,X1,sK2,sK1) | r1_tsep_1(sK2,X1) | ~m1_pre_topc(X1,sK1) | v2_struct_0(X1) | ~l1_struct_0(k2_tsep_1(sK1,sK2,X1))) ) | ~spl5_2),
% 0.19/0.50    inference(resolution,[],[f724,f38])).
% 0.19/0.50  fof(f38,plain,(
% 0.19/0.50    ( ! [X2,X0,X3,X1] : (~r1_tsep_1(k2_tsep_1(X3,X2,X1),X0) | ~sP0(X0,X1,X2,X3)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f30])).
% 0.19/0.50  fof(f30,plain,(
% 0.19/0.50    ! [X0,X1,X2,X3] : (((r1_tsep_1(X1,X0) | r1_tsep_1(X2,X0)) & ~r1_tsep_1(k2_tsep_1(X3,X2,X1),X0)) | ~sP0(X0,X1,X2,X3))),
% 0.19/0.50    inference(rectify,[],[f29])).
% 0.19/0.50  fof(f29,plain,(
% 0.19/0.50    ! [X3,X2,X1,X0] : (((r1_tsep_1(X2,X3) | r1_tsep_1(X1,X3)) & ~r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)) | ~sP0(X3,X2,X1,X0))),
% 0.19/0.50    inference(nnf_transformation,[],[f27])).
% 0.19/0.50  fof(f724,plain,(
% 0.19/0.50    ( ! [X0] : (r1_tsep_1(k2_tsep_1(sK1,sK2,X0),sK4) | ~l1_struct_0(k2_tsep_1(sK1,sK2,X0)) | r1_tsep_1(sK2,X0) | ~m1_pre_topc(X0,sK1) | v2_struct_0(X0)) ) | ~spl5_2),
% 0.19/0.50    inference(subsumption_resolution,[],[f723,f43])).
% 0.19/0.50  fof(f723,plain,(
% 0.19/0.50    ( ! [X0] : (r1_tsep_1(k2_tsep_1(sK1,sK2,X0),sK4) | ~l1_struct_0(k2_tsep_1(sK1,sK2,X0)) | r1_tsep_1(sK2,X0) | ~m1_pre_topc(X0,sK1) | v2_struct_0(X0) | v2_struct_0(sK2)) ) | ~spl5_2),
% 0.19/0.50    inference(subsumption_resolution,[],[f722,f40])).
% 0.19/0.50  fof(f722,plain,(
% 0.19/0.50    ( ! [X0] : (r1_tsep_1(k2_tsep_1(sK1,sK2,X0),sK4) | ~l1_struct_0(k2_tsep_1(sK1,sK2,X0)) | r1_tsep_1(sK2,X0) | ~m1_pre_topc(X0,sK1) | v2_struct_0(X0) | v2_struct_0(sK1) | v2_struct_0(sK2)) ) | ~spl5_2),
% 0.19/0.50    inference(subsumption_resolution,[],[f721,f41])).
% 0.19/0.50  fof(f41,plain,(
% 0.19/0.50    v2_pre_topc(sK1)),
% 0.19/0.50    inference(cnf_transformation,[],[f35])).
% 0.19/0.50  fof(f721,plain,(
% 0.19/0.50    ( ! [X0] : (r1_tsep_1(k2_tsep_1(sK1,sK2,X0),sK4) | ~l1_struct_0(k2_tsep_1(sK1,sK2,X0)) | r1_tsep_1(sK2,X0) | ~m1_pre_topc(X0,sK1) | v2_struct_0(X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | v2_struct_0(sK2)) ) | ~spl5_2),
% 0.19/0.50    inference(subsumption_resolution,[],[f720,f42])).
% 0.19/0.50  fof(f720,plain,(
% 0.19/0.50    ( ! [X0] : (r1_tsep_1(k2_tsep_1(sK1,sK2,X0),sK4) | ~l1_struct_0(k2_tsep_1(sK1,sK2,X0)) | r1_tsep_1(sK2,X0) | ~m1_pre_topc(X0,sK1) | v2_struct_0(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | v2_struct_0(sK2)) ) | ~spl5_2),
% 0.19/0.50    inference(subsumption_resolution,[],[f719,f44])).
% 0.19/0.50  fof(f719,plain,(
% 0.19/0.50    ( ! [X0] : (r1_tsep_1(k2_tsep_1(sK1,sK2,X0),sK4) | ~l1_struct_0(k2_tsep_1(sK1,sK2,X0)) | r1_tsep_1(sK2,X0) | ~m1_pre_topc(X0,sK1) | v2_struct_0(X0) | ~m1_pre_topc(sK2,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | v2_struct_0(sK2)) ) | ~spl5_2),
% 0.19/0.50    inference(duplicate_literal_removal,[],[f716])).
% 0.19/0.50  fof(f716,plain,(
% 0.19/0.50    ( ! [X0] : (r1_tsep_1(k2_tsep_1(sK1,sK2,X0),sK4) | ~l1_struct_0(k2_tsep_1(sK1,sK2,X0)) | r1_tsep_1(sK2,X0) | ~m1_pre_topc(X0,sK1) | v2_struct_0(X0) | ~m1_pre_topc(sK2,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(X0,sK1) | v2_struct_0(X0) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | v2_struct_0(sK1)) ) | ~spl5_2),
% 0.19/0.50    inference(resolution,[],[f648,f62])).
% 0.19/0.50  fof(f648,plain,(
% 0.19/0.50    ( ! [X2,X3] : (~m1_pre_topc(k2_tsep_1(X2,sK2,X3),sK1) | r1_tsep_1(k2_tsep_1(X2,sK2,X3),sK4) | ~l1_struct_0(k2_tsep_1(X2,sK2,X3)) | r1_tsep_1(sK2,X3) | ~m1_pre_topc(X3,X2) | v2_struct_0(X3) | ~m1_pre_topc(sK2,X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | ~spl5_2),
% 0.19/0.50    inference(subsumption_resolution,[],[f644,f43])).
% 0.19/0.50  fof(f644,plain,(
% 0.19/0.50    ( ! [X2,X3] : (~m1_pre_topc(k2_tsep_1(X2,sK2,X3),sK1) | r1_tsep_1(k2_tsep_1(X2,sK2,X3),sK4) | ~l1_struct_0(k2_tsep_1(X2,sK2,X3)) | r1_tsep_1(sK2,X3) | ~m1_pre_topc(X3,X2) | v2_struct_0(X3) | ~m1_pre_topc(sK2,X2) | v2_struct_0(sK2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | ~spl5_2),
% 0.19/0.50    inference(resolution,[],[f635,f56])).
% 0.19/0.50  fof(f56,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),X1) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f18])).
% 0.19/0.50  fof(f18,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X2) & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.50    inference(flattening,[],[f17])).
% 0.19/0.50  fof(f17,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(k2_tsep_1(X0,X1,X2),X2) & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1)) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.50    inference(ennf_transformation,[],[f7])).
% 0.19/0.50  fof(f7,axiom,(
% 0.19/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X2) & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1))))))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tsep_1)).
% 0.19/0.50  fof(f635,plain,(
% 0.19/0.50    ( ! [X0] : (~m1_pre_topc(X0,sK2) | ~m1_pre_topc(X0,sK1) | r1_tsep_1(X0,sK4) | ~l1_struct_0(X0)) ) | ~spl5_2),
% 0.19/0.50    inference(subsumption_resolution,[],[f633,f91])).
% 0.19/0.50  fof(f91,plain,(
% 0.19/0.50    l1_struct_0(sK4)),
% 0.19/0.50    inference(resolution,[],[f88,f54])).
% 0.19/0.50  fof(f88,plain,(
% 0.19/0.50    l1_pre_topc(sK4)),
% 0.19/0.50    inference(subsumption_resolution,[],[f85,f42])).
% 0.19/0.50  fof(f85,plain,(
% 0.19/0.50    l1_pre_topc(sK4) | ~l1_pre_topc(sK1)),
% 0.19/0.50    inference(resolution,[],[f55,f48])).
% 0.19/0.50  fof(f48,plain,(
% 0.19/0.50    m1_pre_topc(sK4,sK1)),
% 0.19/0.50    inference(cnf_transformation,[],[f35])).
% 0.19/0.50  fof(f633,plain,(
% 0.19/0.50    ( ! [X0] : (~l1_struct_0(sK4) | ~m1_pre_topc(X0,sK2) | ~m1_pre_topc(X0,sK1) | r1_tsep_1(X0,sK4) | ~l1_struct_0(X0)) ) | ~spl5_2),
% 0.19/0.50    inference(resolution,[],[f94,f119])).
% 0.19/0.50  fof(f119,plain,(
% 0.19/0.50    ( ! [X0,X1] : (~r1_tsep_1(sK2,X1) | ~l1_struct_0(X1) | ~m1_pre_topc(X0,sK2) | ~m1_pre_topc(X0,sK1) | r1_tsep_1(X0,X1) | ~l1_struct_0(X0)) )),
% 0.19/0.50    inference(duplicate_literal_removal,[],[f117])).
% 0.19/0.50  fof(f117,plain,(
% 0.19/0.50    ( ! [X0,X1] : (~m1_pre_topc(X0,sK1) | ~l1_struct_0(X1) | ~m1_pre_topc(X0,sK2) | ~r1_tsep_1(sK2,X1) | r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.19/0.50    inference(resolution,[],[f110,f53])).
% 0.19/0.50  fof(f53,plain,(
% 0.19/0.50    ( ! [X0,X1] : (~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f36])).
% 0.19/0.50  fof(f36,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : (((r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) & (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.19/0.50    inference(nnf_transformation,[],[f14])).
% 0.19/0.50  fof(f14,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.19/0.50    inference(ennf_transformation,[],[f4])).
% 0.19/0.50  fof(f4,axiom,(
% 0.19/0.50    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).
% 0.19/0.50  fof(f110,plain,(
% 0.19/0.50    ( ! [X2,X3] : (r1_xboole_0(u1_struct_0(X2),u1_struct_0(X3)) | ~m1_pre_topc(X2,sK1) | ~l1_struct_0(X3) | ~m1_pre_topc(X2,sK2) | ~r1_tsep_1(sK2,X3)) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f109,f89])).
% 0.19/0.50  fof(f89,plain,(
% 0.19/0.50    l1_struct_0(sK2)),
% 0.19/0.50    inference(resolution,[],[f86,f54])).
% 0.19/0.50  fof(f86,plain,(
% 0.19/0.50    l1_pre_topc(sK2)),
% 0.19/0.50    inference(subsumption_resolution,[],[f83,f42])).
% 0.19/0.50  fof(f83,plain,(
% 0.19/0.50    l1_pre_topc(sK2) | ~l1_pre_topc(sK1)),
% 0.19/0.50    inference(resolution,[],[f55,f44])).
% 0.19/0.50  fof(f109,plain,(
% 0.19/0.50    ( ! [X2,X3] : (~m1_pre_topc(X2,sK2) | ~m1_pre_topc(X2,sK1) | ~l1_struct_0(X3) | ~l1_struct_0(sK2) | r1_xboole_0(u1_struct_0(X2),u1_struct_0(X3)) | ~r1_tsep_1(sK2,X3)) )),
% 0.19/0.50    inference(resolution,[],[f103,f96])).
% 0.19/0.50  fof(f96,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X2,u1_struct_0(X0)) | ~l1_struct_0(X1) | ~l1_struct_0(X0) | r1_xboole_0(X2,u1_struct_0(X1)) | ~r1_tsep_1(X0,X1)) )),
% 0.19/0.50    inference(resolution,[],[f52,f63])).
% 0.19/0.50  fof(f63,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f26])).
% 0.19/0.50  fof(f26,plain,(
% 0.19/0.50    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.19/0.50    inference(flattening,[],[f25])).
% 0.19/0.50  fof(f25,plain,(
% 0.19/0.50    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.19/0.50    inference(ennf_transformation,[],[f1])).
% 0.19/0.50  fof(f1,axiom,(
% 0.19/0.50    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.19/0.50  fof(f52,plain,(
% 0.19/0.50    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f36])).
% 0.19/0.50  fof(f103,plain,(
% 0.19/0.50    ( ! [X0] : (r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) | ~m1_pre_topc(X0,sK2) | ~m1_pre_topc(X0,sK1)) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f102,f41])).
% 0.19/0.51  fof(f102,plain,(
% 0.19/0.51    ( ! [X0] : (~m1_pre_topc(X0,sK2) | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) | ~m1_pre_topc(X0,sK1) | ~v2_pre_topc(sK1)) )),
% 0.19/0.51    inference(subsumption_resolution,[],[f99,f42])).
% 0.19/0.51  % (19020)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.19/0.51  fof(f99,plain,(
% 0.19/0.51    ( ! [X0] : (~m1_pre_topc(X0,sK2) | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) | ~m1_pre_topc(X0,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)) )),
% 0.19/0.51    inference(resolution,[],[f59,f44])).
% 0.19/0.51  fof(f59,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X2) | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f37])).
% 0.19/0.51  fof(f37,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.51    inference(nnf_transformation,[],[f20])).
% 0.19/0.51  fof(f20,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.51    inference(flattening,[],[f19])).
% 0.19/0.51  fof(f19,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f8])).
% 0.19/0.51  fof(f8,axiom,(
% 0.19/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).
% 0.19/0.51  fof(f94,plain,(
% 0.19/0.51    r1_tsep_1(sK2,sK4) | ~spl5_2),
% 0.19/0.51    inference(subsumption_resolution,[],[f93,f91])).
% 0.19/0.51  fof(f93,plain,(
% 0.19/0.51    r1_tsep_1(sK2,sK4) | ~l1_struct_0(sK4) | ~spl5_2),
% 0.19/0.51    inference(subsumption_resolution,[],[f92,f89])).
% 0.19/0.51  fof(f92,plain,(
% 0.19/0.51    r1_tsep_1(sK2,sK4) | ~l1_struct_0(sK2) | ~l1_struct_0(sK4) | ~spl5_2),
% 0.19/0.51    inference(resolution,[],[f60,f71])).
% 0.19/0.51  fof(f71,plain,(
% 0.19/0.51    r1_tsep_1(sK4,sK2) | ~spl5_2),
% 0.19/0.51    inference(avatar_component_clause,[],[f69])).
% 0.19/0.51  fof(f69,plain,(
% 0.19/0.51    spl5_2 <=> r1_tsep_1(sK4,sK2)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.19/0.51  fof(f60,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~r1_tsep_1(X0,X1) | r1_tsep_1(X1,X0) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f22])).
% 0.19/0.51  fof(f22,plain,(
% 0.19/0.51    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 0.19/0.51    inference(flattening,[],[f21])).
% 0.19/0.51  fof(f21,plain,(
% 0.19/0.51    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f6])).
% 0.19/0.51  fof(f6,axiom,(
% 0.19/0.51    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).
% 0.19/0.51  fof(f67,plain,(
% 0.19/0.51    sP0(sK4,sK3,sK2,sK1) | ~spl5_1),
% 0.19/0.51    inference(avatar_component_clause,[],[f65])).
% 0.19/0.51  fof(f65,plain,(
% 0.19/0.51    spl5_1 <=> sP0(sK4,sK3,sK2,sK1)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.19/0.51  fof(f744,plain,(
% 0.19/0.51    ~spl5_2 | spl5_4),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f743])).
% 0.19/0.51  fof(f743,plain,(
% 0.19/0.51    $false | (~spl5_2 | spl5_4)),
% 0.19/0.51    inference(subsumption_resolution,[],[f742,f45])).
% 0.19/0.51  fof(f742,plain,(
% 0.19/0.51    v2_struct_0(sK3) | (~spl5_2 | spl5_4)),
% 0.19/0.51    inference(subsumption_resolution,[],[f741,f46])).
% 0.19/0.51  fof(f741,plain,(
% 0.19/0.51    ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | (~spl5_2 | spl5_4)),
% 0.19/0.51    inference(subsumption_resolution,[],[f740,f40])).
% 0.19/0.51  fof(f740,plain,(
% 0.19/0.51    v2_struct_0(sK1) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | (~spl5_2 | spl5_4)),
% 0.19/0.51    inference(subsumption_resolution,[],[f739,f42])).
% 0.19/0.51  fof(f739,plain,(
% 0.19/0.51    ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | (~spl5_2 | spl5_4)),
% 0.19/0.51    inference(subsumption_resolution,[],[f738,f43])).
% 0.19/0.51  fof(f738,plain,(
% 0.19/0.51    v2_struct_0(sK2) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | (~spl5_2 | spl5_4)),
% 0.19/0.51    inference(subsumption_resolution,[],[f737,f44])).
% 0.19/0.51  fof(f737,plain,(
% 0.19/0.51    ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | (~spl5_2 | spl5_4)),
% 0.19/0.51    inference(resolution,[],[f736,f203])).
% 0.19/0.51  fof(f736,plain,(
% 0.19/0.51    ~l1_struct_0(k2_tsep_1(sK1,sK2,sK3)) | (~spl5_2 | spl5_4)),
% 0.19/0.51    inference(subsumption_resolution,[],[f735,f45])).
% 0.19/0.51  fof(f735,plain,(
% 0.19/0.51    v2_struct_0(sK3) | ~l1_struct_0(k2_tsep_1(sK1,sK2,sK3)) | (~spl5_2 | spl5_4)),
% 0.19/0.51    inference(subsumption_resolution,[],[f734,f46])).
% 0.19/0.51  fof(f734,plain,(
% 0.19/0.51    ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | ~l1_struct_0(k2_tsep_1(sK1,sK2,sK3)) | (~spl5_2 | spl5_4)),
% 0.19/0.51    inference(subsumption_resolution,[],[f729,f49])).
% 0.19/0.51  fof(f729,plain,(
% 0.19/0.51    r1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | ~l1_struct_0(k2_tsep_1(sK1,sK2,sK3)) | (~spl5_2 | spl5_4)),
% 0.19/0.51    inference(resolution,[],[f728,f80])).
% 0.19/0.51  fof(f80,plain,(
% 0.19/0.51    ~r1_tsep_1(sK4,k2_tsep_1(sK1,sK2,sK3)) | spl5_4),
% 0.19/0.51    inference(avatar_component_clause,[],[f78])).
% 0.19/0.51  fof(f78,plain,(
% 0.19/0.51    spl5_4 <=> r1_tsep_1(sK4,k2_tsep_1(sK1,sK2,sK3))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.19/0.51  fof(f728,plain,(
% 0.19/0.51    ( ! [X0] : (r1_tsep_1(sK4,k2_tsep_1(sK1,sK2,X0)) | r1_tsep_1(sK2,X0) | ~m1_pre_topc(X0,sK1) | v2_struct_0(X0) | ~l1_struct_0(k2_tsep_1(sK1,sK2,X0))) ) | ~spl5_2),
% 0.19/0.51    inference(subsumption_resolution,[],[f727,f91])).
% 0.19/0.51  fof(f727,plain,(
% 0.19/0.51    ( ! [X0] : (~l1_struct_0(k2_tsep_1(sK1,sK2,X0)) | r1_tsep_1(sK2,X0) | ~m1_pre_topc(X0,sK1) | v2_struct_0(X0) | r1_tsep_1(sK4,k2_tsep_1(sK1,sK2,X0)) | ~l1_struct_0(sK4)) ) | ~spl5_2),
% 0.19/0.51    inference(duplicate_literal_removal,[],[f725])).
% 0.19/0.51  fof(f725,plain,(
% 0.19/0.51    ( ! [X0] : (~l1_struct_0(k2_tsep_1(sK1,sK2,X0)) | r1_tsep_1(sK2,X0) | ~m1_pre_topc(X0,sK1) | v2_struct_0(X0) | r1_tsep_1(sK4,k2_tsep_1(sK1,sK2,X0)) | ~l1_struct_0(sK4) | ~l1_struct_0(k2_tsep_1(sK1,sK2,X0))) ) | ~spl5_2),
% 0.19/0.51    inference(resolution,[],[f724,f60])).
% 0.19/0.51  fof(f627,plain,(
% 0.19/0.51    ~spl5_3 | spl5_4),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f626])).
% 0.19/0.51  fof(f626,plain,(
% 0.19/0.51    $false | (~spl5_3 | spl5_4)),
% 0.19/0.51    inference(subsumption_resolution,[],[f625,f45])).
% 0.19/0.51  fof(f625,plain,(
% 0.19/0.51    v2_struct_0(sK3) | (~spl5_3 | spl5_4)),
% 0.19/0.51    inference(subsumption_resolution,[],[f624,f46])).
% 0.19/0.51  fof(f624,plain,(
% 0.19/0.51    ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | (~spl5_3 | spl5_4)),
% 0.19/0.51    inference(subsumption_resolution,[],[f623,f40])).
% 0.19/0.51  fof(f623,plain,(
% 0.19/0.51    v2_struct_0(sK1) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | (~spl5_3 | spl5_4)),
% 0.19/0.51    inference(subsumption_resolution,[],[f622,f42])).
% 0.19/0.51  fof(f622,plain,(
% 0.19/0.51    ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | (~spl5_3 | spl5_4)),
% 0.19/0.51    inference(subsumption_resolution,[],[f621,f43])).
% 0.19/0.51  fof(f621,plain,(
% 0.19/0.51    v2_struct_0(sK2) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | (~spl5_3 | spl5_4)),
% 0.19/0.51    inference(subsumption_resolution,[],[f620,f44])).
% 0.19/0.51  fof(f620,plain,(
% 0.19/0.51    ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | (~spl5_3 | spl5_4)),
% 0.19/0.51    inference(resolution,[],[f619,f203])).
% 0.19/0.51  fof(f619,plain,(
% 0.19/0.51    ~l1_struct_0(k2_tsep_1(sK1,sK2,sK3)) | (~spl5_3 | spl5_4)),
% 0.19/0.51    inference(subsumption_resolution,[],[f618,f43])).
% 0.19/0.51  fof(f618,plain,(
% 0.19/0.51    v2_struct_0(sK2) | ~l1_struct_0(k2_tsep_1(sK1,sK2,sK3)) | (~spl5_3 | spl5_4)),
% 0.19/0.51    inference(subsumption_resolution,[],[f617,f44])).
% 0.19/0.51  fof(f617,plain,(
% 0.19/0.51    ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK2) | ~l1_struct_0(k2_tsep_1(sK1,sK2,sK3)) | (~spl5_3 | spl5_4)),
% 0.19/0.51    inference(subsumption_resolution,[],[f612,f49])).
% 0.19/0.51  fof(f612,plain,(
% 0.19/0.51    r1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK2) | ~l1_struct_0(k2_tsep_1(sK1,sK2,sK3)) | (~spl5_3 | spl5_4)),
% 0.19/0.51    inference(resolution,[],[f599,f80])).
% 0.19/0.51  fof(f599,plain,(
% 0.19/0.51    ( ! [X0] : (r1_tsep_1(sK4,k2_tsep_1(sK1,X0,sK3)) | r1_tsep_1(X0,sK3) | ~m1_pre_topc(X0,sK1) | v2_struct_0(X0) | ~l1_struct_0(k2_tsep_1(sK1,X0,sK3))) ) | ~spl5_3),
% 0.19/0.51    inference(subsumption_resolution,[],[f598,f91])).
% 0.19/0.51  fof(f598,plain,(
% 0.19/0.51    ( ! [X0] : (~l1_struct_0(k2_tsep_1(sK1,X0,sK3)) | r1_tsep_1(X0,sK3) | ~m1_pre_topc(X0,sK1) | v2_struct_0(X0) | r1_tsep_1(sK4,k2_tsep_1(sK1,X0,sK3)) | ~l1_struct_0(sK4)) ) | ~spl5_3),
% 0.19/0.51    inference(duplicate_literal_removal,[],[f596])).
% 0.19/0.51  fof(f596,plain,(
% 0.19/0.51    ( ! [X0] : (~l1_struct_0(k2_tsep_1(sK1,X0,sK3)) | r1_tsep_1(X0,sK3) | ~m1_pre_topc(X0,sK1) | v2_struct_0(X0) | r1_tsep_1(sK4,k2_tsep_1(sK1,X0,sK3)) | ~l1_struct_0(sK4) | ~l1_struct_0(k2_tsep_1(sK1,X0,sK3))) ) | ~spl5_3),
% 0.19/0.51    inference(resolution,[],[f595,f60])).
% 0.19/0.51  fof(f595,plain,(
% 0.19/0.51    ( ! [X0] : (r1_tsep_1(k2_tsep_1(sK1,X0,sK3),sK4) | ~l1_struct_0(k2_tsep_1(sK1,X0,sK3)) | r1_tsep_1(X0,sK3) | ~m1_pre_topc(X0,sK1) | v2_struct_0(X0)) ) | ~spl5_3),
% 0.19/0.51    inference(subsumption_resolution,[],[f594,f45])).
% 0.19/0.51  fof(f594,plain,(
% 0.19/0.51    ( ! [X0] : (r1_tsep_1(k2_tsep_1(sK1,X0,sK3),sK4) | ~l1_struct_0(k2_tsep_1(sK1,X0,sK3)) | r1_tsep_1(X0,sK3) | ~m1_pre_topc(X0,sK1) | v2_struct_0(X0) | v2_struct_0(sK3)) ) | ~spl5_3),
% 0.19/0.51    inference(subsumption_resolution,[],[f593,f40])).
% 0.19/0.51  fof(f593,plain,(
% 0.19/0.51    ( ! [X0] : (r1_tsep_1(k2_tsep_1(sK1,X0,sK3),sK4) | ~l1_struct_0(k2_tsep_1(sK1,X0,sK3)) | r1_tsep_1(X0,sK3) | ~m1_pre_topc(X0,sK1) | v2_struct_0(X0) | v2_struct_0(sK1) | v2_struct_0(sK3)) ) | ~spl5_3),
% 0.19/0.51    inference(subsumption_resolution,[],[f592,f41])).
% 0.19/0.51  fof(f592,plain,(
% 0.19/0.51    ( ! [X0] : (r1_tsep_1(k2_tsep_1(sK1,X0,sK3),sK4) | ~l1_struct_0(k2_tsep_1(sK1,X0,sK3)) | r1_tsep_1(X0,sK3) | ~m1_pre_topc(X0,sK1) | v2_struct_0(X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | v2_struct_0(sK3)) ) | ~spl5_3),
% 0.19/0.51    inference(subsumption_resolution,[],[f591,f42])).
% 0.19/0.51  fof(f591,plain,(
% 0.19/0.51    ( ! [X0] : (r1_tsep_1(k2_tsep_1(sK1,X0,sK3),sK4) | ~l1_struct_0(k2_tsep_1(sK1,X0,sK3)) | r1_tsep_1(X0,sK3) | ~m1_pre_topc(X0,sK1) | v2_struct_0(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | v2_struct_0(sK3)) ) | ~spl5_3),
% 0.19/0.51    inference(subsumption_resolution,[],[f590,f46])).
% 0.19/0.51  fof(f590,plain,(
% 0.19/0.51    ( ! [X0] : (r1_tsep_1(k2_tsep_1(sK1,X0,sK3),sK4) | ~l1_struct_0(k2_tsep_1(sK1,X0,sK3)) | r1_tsep_1(X0,sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_pre_topc(X0,sK1) | v2_struct_0(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | v2_struct_0(sK3)) ) | ~spl5_3),
% 0.19/0.51    inference(duplicate_literal_removal,[],[f587])).
% 0.19/0.51  fof(f587,plain,(
% 0.19/0.51    ( ! [X0] : (r1_tsep_1(k2_tsep_1(sK1,X0,sK3),sK4) | ~l1_struct_0(k2_tsep_1(sK1,X0,sK3)) | r1_tsep_1(X0,sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_pre_topc(X0,sK1) | v2_struct_0(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(X0,sK1) | v2_struct_0(X0) | ~l1_pre_topc(sK1) | v2_struct_0(sK1)) ) | ~spl5_3),
% 0.19/0.51    inference(resolution,[],[f436,f62])).
% 0.19/0.51  fof(f436,plain,(
% 0.19/0.51    ( ! [X4,X5] : (~m1_pre_topc(k2_tsep_1(X4,X5,sK3),sK1) | r1_tsep_1(k2_tsep_1(X4,X5,sK3),sK4) | ~l1_struct_0(k2_tsep_1(X4,X5,sK3)) | r1_tsep_1(X5,sK3) | ~m1_pre_topc(sK3,X4) | ~m1_pre_topc(X5,X4) | v2_struct_0(X5) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) ) | ~spl5_3),
% 0.19/0.51    inference(subsumption_resolution,[],[f432,f45])).
% 0.19/0.51  fof(f432,plain,(
% 0.19/0.51    ( ! [X4,X5] : (~m1_pre_topc(k2_tsep_1(X4,X5,sK3),sK1) | r1_tsep_1(k2_tsep_1(X4,X5,sK3),sK4) | ~l1_struct_0(k2_tsep_1(X4,X5,sK3)) | r1_tsep_1(X5,sK3) | ~m1_pre_topc(sK3,X4) | v2_struct_0(sK3) | ~m1_pre_topc(X5,X4) | v2_struct_0(X5) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) ) | ~spl5_3),
% 0.19/0.51    inference(resolution,[],[f409,f57])).
% 0.19/0.51  fof(f57,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),X2) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f18])).
% 0.19/0.51  fof(f409,plain,(
% 0.19/0.51    ( ! [X0] : (~m1_pre_topc(X0,sK3) | ~m1_pre_topc(X0,sK1) | r1_tsep_1(X0,sK4) | ~l1_struct_0(X0)) ) | ~spl5_3),
% 0.19/0.51    inference(subsumption_resolution,[],[f407,f91])).
% 0.19/0.51  fof(f407,plain,(
% 0.19/0.51    ( ! [X0] : (~l1_struct_0(sK4) | ~m1_pre_topc(X0,sK3) | ~m1_pre_topc(X0,sK1) | r1_tsep_1(X0,sK4) | ~l1_struct_0(X0)) ) | ~spl5_3),
% 0.19/0.51    inference(resolution,[],[f299,f122])).
% 0.19/0.51  fof(f122,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~r1_tsep_1(sK3,X1) | ~l1_struct_0(X1) | ~m1_pre_topc(X0,sK3) | ~m1_pre_topc(X0,sK1) | r1_tsep_1(X0,X1) | ~l1_struct_0(X0)) )),
% 0.19/0.51    inference(duplicate_literal_removal,[],[f120])).
% 0.19/0.51  fof(f120,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~m1_pre_topc(X0,sK1) | ~l1_struct_0(X1) | ~m1_pre_topc(X0,sK3) | ~r1_tsep_1(sK3,X1) | r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.19/0.51    inference(resolution,[],[f113,f53])).
% 0.19/0.51  fof(f113,plain,(
% 0.19/0.51    ( ! [X2,X3] : (r1_xboole_0(u1_struct_0(X2),u1_struct_0(X3)) | ~m1_pre_topc(X2,sK1) | ~l1_struct_0(X3) | ~m1_pre_topc(X2,sK3) | ~r1_tsep_1(sK3,X3)) )),
% 0.19/0.51    inference(subsumption_resolution,[],[f112,f90])).
% 0.19/0.51  fof(f90,plain,(
% 0.19/0.51    l1_struct_0(sK3)),
% 0.19/0.51    inference(resolution,[],[f87,f54])).
% 0.19/0.51  fof(f87,plain,(
% 0.19/0.51    l1_pre_topc(sK3)),
% 0.19/0.51    inference(subsumption_resolution,[],[f84,f42])).
% 0.19/0.51  fof(f84,plain,(
% 0.19/0.51    l1_pre_topc(sK3) | ~l1_pre_topc(sK1)),
% 0.19/0.51    inference(resolution,[],[f55,f46])).
% 0.19/0.51  fof(f112,plain,(
% 0.19/0.51    ( ! [X2,X3] : (~m1_pre_topc(X2,sK3) | ~m1_pre_topc(X2,sK1) | ~l1_struct_0(X3) | ~l1_struct_0(sK3) | r1_xboole_0(u1_struct_0(X2),u1_struct_0(X3)) | ~r1_tsep_1(sK3,X3)) )),
% 0.19/0.51    inference(resolution,[],[f105,f96])).
% 0.19/0.51  fof(f105,plain,(
% 0.19/0.51    ( ! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(sK3)) | ~m1_pre_topc(X1,sK3) | ~m1_pre_topc(X1,sK1)) )),
% 0.19/0.51    inference(subsumption_resolution,[],[f104,f41])).
% 0.19/0.51  fof(f104,plain,(
% 0.19/0.51    ( ! [X1] : (~m1_pre_topc(X1,sK3) | r1_tarski(u1_struct_0(X1),u1_struct_0(sK3)) | ~m1_pre_topc(X1,sK1) | ~v2_pre_topc(sK1)) )),
% 0.19/0.51    inference(subsumption_resolution,[],[f100,f42])).
% 0.19/0.51  fof(f100,plain,(
% 0.19/0.51    ( ! [X1] : (~m1_pre_topc(X1,sK3) | r1_tarski(u1_struct_0(X1),u1_struct_0(sK3)) | ~m1_pre_topc(X1,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)) )),
% 0.19/0.51    inference(resolution,[],[f59,f46])).
% 0.19/0.51  fof(f299,plain,(
% 0.19/0.51    r1_tsep_1(sK3,sK4) | ~spl5_3),
% 0.19/0.51    inference(subsumption_resolution,[],[f298,f91])).
% 0.19/0.51  fof(f298,plain,(
% 0.19/0.51    r1_tsep_1(sK3,sK4) | ~l1_struct_0(sK4) | ~spl5_3),
% 0.19/0.51    inference(subsumption_resolution,[],[f296,f90])).
% 0.19/0.51  fof(f296,plain,(
% 0.19/0.51    r1_tsep_1(sK3,sK4) | ~l1_struct_0(sK3) | ~l1_struct_0(sK4) | ~spl5_3),
% 0.19/0.51    inference(resolution,[],[f75,f60])).
% 0.19/0.51  fof(f75,plain,(
% 0.19/0.51    r1_tsep_1(sK4,sK3) | ~spl5_3),
% 0.19/0.51    inference(avatar_component_clause,[],[f73])).
% 0.19/0.51  fof(f73,plain,(
% 0.19/0.51    spl5_3 <=> r1_tsep_1(sK4,sK3)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.19/0.51  fof(f611,plain,(
% 0.19/0.51    ~spl5_1 | ~spl5_3),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f610])).
% 0.19/0.51  fof(f610,plain,(
% 0.19/0.51    $false | (~spl5_1 | ~spl5_3)),
% 0.19/0.51    inference(subsumption_resolution,[],[f609,f45])).
% 0.19/0.51  fof(f609,plain,(
% 0.19/0.51    v2_struct_0(sK3) | (~spl5_1 | ~spl5_3)),
% 0.19/0.51    inference(subsumption_resolution,[],[f608,f46])).
% 0.19/0.51  fof(f608,plain,(
% 0.19/0.51    ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | (~spl5_1 | ~spl5_3)),
% 0.19/0.51    inference(subsumption_resolution,[],[f607,f40])).
% 0.19/0.51  fof(f607,plain,(
% 0.19/0.51    v2_struct_0(sK1) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | (~spl5_1 | ~spl5_3)),
% 0.19/0.51    inference(subsumption_resolution,[],[f606,f42])).
% 0.19/0.51  fof(f606,plain,(
% 0.19/0.51    ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | (~spl5_1 | ~spl5_3)),
% 0.19/0.51    inference(subsumption_resolution,[],[f605,f43])).
% 0.19/0.51  fof(f605,plain,(
% 0.19/0.51    v2_struct_0(sK2) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | (~spl5_1 | ~spl5_3)),
% 0.19/0.51    inference(subsumption_resolution,[],[f604,f44])).
% 0.19/0.51  fof(f604,plain,(
% 0.19/0.51    ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | (~spl5_1 | ~spl5_3)),
% 0.19/0.51    inference(resolution,[],[f603,f203])).
% 0.19/0.51  fof(f603,plain,(
% 0.19/0.51    ~l1_struct_0(k2_tsep_1(sK1,sK2,sK3)) | (~spl5_1 | ~spl5_3)),
% 0.19/0.51    inference(subsumption_resolution,[],[f602,f43])).
% 0.19/0.51  fof(f602,plain,(
% 0.19/0.51    v2_struct_0(sK2) | ~l1_struct_0(k2_tsep_1(sK1,sK2,sK3)) | (~spl5_1 | ~spl5_3)),
% 0.19/0.51    inference(subsumption_resolution,[],[f601,f44])).
% 0.19/0.51  fof(f601,plain,(
% 0.19/0.51    ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK2) | ~l1_struct_0(k2_tsep_1(sK1,sK2,sK3)) | (~spl5_1 | ~spl5_3)),
% 0.19/0.51    inference(subsumption_resolution,[],[f600,f49])).
% 0.19/0.51  fof(f600,plain,(
% 0.19/0.51    r1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK2) | ~l1_struct_0(k2_tsep_1(sK1,sK2,sK3)) | (~spl5_1 | ~spl5_3)),
% 0.19/0.51    inference(resolution,[],[f597,f67])).
% 0.19/0.51  fof(f597,plain,(
% 0.19/0.51    ( ! [X1] : (~sP0(sK4,sK3,X1,sK1) | r1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK1) | v2_struct_0(X1) | ~l1_struct_0(k2_tsep_1(sK1,X1,sK3))) ) | ~spl5_3),
% 0.19/0.51    inference(resolution,[],[f595,f38])).
% 0.19/0.51  fof(f401,plain,(
% 0.19/0.51    spl5_2 | ~spl5_34),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f400])).
% 0.19/0.51  fof(f400,plain,(
% 0.19/0.51    $false | (spl5_2 | ~spl5_34)),
% 0.19/0.51    inference(subsumption_resolution,[],[f399,f89])).
% 0.19/0.51  fof(f399,plain,(
% 0.19/0.51    ~l1_struct_0(sK2) | (spl5_2 | ~spl5_34)),
% 0.19/0.51    inference(subsumption_resolution,[],[f398,f91])).
% 0.19/0.51  fof(f398,plain,(
% 0.19/0.51    ~l1_struct_0(sK4) | ~l1_struct_0(sK2) | (spl5_2 | ~spl5_34)),
% 0.19/0.51    inference(subsumption_resolution,[],[f396,f70])).
% 0.19/0.51  fof(f70,plain,(
% 0.19/0.51    ~r1_tsep_1(sK4,sK2) | spl5_2),
% 0.19/0.51    inference(avatar_component_clause,[],[f69])).
% 0.19/0.51  fof(f396,plain,(
% 0.19/0.51    r1_tsep_1(sK4,sK2) | ~l1_struct_0(sK4) | ~l1_struct_0(sK2) | ~spl5_34),
% 0.19/0.51    inference(resolution,[],[f374,f60])).
% 0.19/0.51  fof(f374,plain,(
% 0.19/0.51    r1_tsep_1(sK2,sK4) | ~spl5_34),
% 0.19/0.51    inference(avatar_component_clause,[],[f372])).
% 0.19/0.51  fof(f372,plain,(
% 0.19/0.51    spl5_34 <=> r1_tsep_1(sK2,sK4)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).
% 0.19/0.51  fof(f394,plain,(
% 0.19/0.51    spl5_3 | ~spl5_33),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f393])).
% 0.19/0.51  % (19021)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 0.19/0.51  fof(f393,plain,(
% 0.19/0.51    $false | (spl5_3 | ~spl5_33)),
% 0.19/0.51    inference(subsumption_resolution,[],[f392,f90])).
% 0.19/0.51  fof(f392,plain,(
% 0.19/0.51    ~l1_struct_0(sK3) | (spl5_3 | ~spl5_33)),
% 0.19/0.51    inference(subsumption_resolution,[],[f391,f91])).
% 0.19/0.51  fof(f391,plain,(
% 0.19/0.51    ~l1_struct_0(sK4) | ~l1_struct_0(sK3) | (spl5_3 | ~spl5_33)),
% 0.19/0.51    inference(subsumption_resolution,[],[f389,f74])).
% 0.19/0.51  fof(f74,plain,(
% 0.19/0.51    ~r1_tsep_1(sK4,sK3) | spl5_3),
% 0.19/0.51    inference(avatar_component_clause,[],[f73])).
% 0.19/0.51  fof(f389,plain,(
% 0.19/0.51    r1_tsep_1(sK4,sK3) | ~l1_struct_0(sK4) | ~l1_struct_0(sK3) | ~spl5_33),
% 0.19/0.51    inference(resolution,[],[f370,f60])).
% 0.19/0.51  fof(f370,plain,(
% 0.19/0.51    r1_tsep_1(sK3,sK4) | ~spl5_33),
% 0.19/0.51    inference(avatar_component_clause,[],[f368])).
% 0.19/0.51  fof(f368,plain,(
% 0.19/0.51    spl5_33 <=> r1_tsep_1(sK3,sK4)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 0.19/0.51  fof(f375,plain,(
% 0.19/0.51    spl5_33 | spl5_34 | ~spl5_1),
% 0.19/0.51    inference(avatar_split_clause,[],[f366,f65,f372,f368])).
% 0.19/0.51  fof(f366,plain,(
% 0.19/0.51    r1_tsep_1(sK2,sK4) | r1_tsep_1(sK3,sK4) | ~spl5_1),
% 0.19/0.51    inference(resolution,[],[f67,f39])).
% 0.19/0.51  fof(f39,plain,(
% 0.19/0.51    ( ! [X2,X0,X3,X1] : (~sP0(X0,X1,X2,X3) | r1_tsep_1(X2,X0) | r1_tsep_1(X1,X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f30])).
% 0.19/0.51  fof(f81,plain,(
% 0.19/0.51    spl5_1 | ~spl5_4),
% 0.19/0.51    inference(avatar_split_clause,[],[f50,f78,f65])).
% 0.19/0.51  fof(f50,plain,(
% 0.19/0.51    ~r1_tsep_1(sK4,k2_tsep_1(sK1,sK2,sK3)) | sP0(sK4,sK3,sK2,sK1)),
% 0.19/0.51    inference(cnf_transformation,[],[f35])).
% 0.19/0.51  fof(f76,plain,(
% 0.19/0.51    spl5_1 | spl5_2 | spl5_3),
% 0.19/0.51    inference(avatar_split_clause,[],[f51,f73,f69,f65])).
% 0.19/0.51  fof(f51,plain,(
% 0.19/0.51    r1_tsep_1(sK4,sK3) | r1_tsep_1(sK4,sK2) | sP0(sK4,sK3,sK2,sK1)),
% 0.19/0.51    inference(cnf_transformation,[],[f35])).
% 0.19/0.51  % SZS output end Proof for theBenchmark
% 0.19/0.51  % (19012)------------------------------
% 0.19/0.51  % (19012)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (19012)Termination reason: Refutation
% 0.19/0.51  
% 0.19/0.51  % (19012)Memory used [KB]: 5628
% 0.19/0.51  % (19012)Time elapsed: 0.090 s
% 0.19/0.51  % (19012)------------------------------
% 0.19/0.51  % (19012)------------------------------
% 0.19/0.51  % (19008)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.19/0.52  % (19004)Success in time 0.172 s
%------------------------------------------------------------------------------
