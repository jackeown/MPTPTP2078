%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1335+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:45 EST 2020

% Result     : Theorem 1.23s
% Output     : Refutation 1.23s
% Verified   : 
% Statistics : Number of formulae       :  113 (1587 expanded)
%              Number of leaves         :   19 ( 773 expanded)
%              Depth                    :   24
%              Number of atoms          :  522 (21225 expanded)
%              Number of equality atoms :   16 (  56 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1329,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1328,f62])).

fof(f62,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,
    ( ~ v5_pre_topc(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK4),sK0,sK1)
    & v5_pre_topc(sK4,sK2,sK1)
    & v5_pre_topc(sK3,sK0,sK2)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
    & v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2))
    & v1_funct_1(sK3)
    & l1_pre_topc(sK2)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f23,f50,f49,f48,f47,f46])).

fof(f46,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ~ v5_pre_topc(k1_partfun1(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),X3,X4),X0,X1)
                        & v5_pre_topc(X4,X2,X1)
                        & v5_pre_topc(X3,X0,X2)
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                    & v1_funct_1(X3) )
                & l1_pre_topc(X2)
                & ~ v2_struct_0(X2) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ v5_pre_topc(k1_partfun1(u1_struct_0(sK0),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),X3,X4),sK0,X1)
                      & v5_pre_topc(X4,X2,X1)
                      & v5_pre_topc(X3,sK0,X2)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2))))
                  & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2))
                  & v1_funct_1(X3) )
              & l1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ~ v5_pre_topc(k1_partfun1(u1_struct_0(sK0),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),X3,X4),sK0,X1)
                    & v5_pre_topc(X4,X2,X1)
                    & v5_pre_topc(X3,sK0,X2)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2))))
                & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2))
                & v1_funct_1(X3) )
            & l1_pre_topc(X2)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ v5_pre_topc(k1_partfun1(u1_struct_0(sK0),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(sK1),X3,X4),sK0,sK1)
                  & v5_pre_topc(X4,X2,sK1)
                  & v5_pre_topc(X3,sK0,X2)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
                  & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK1))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2))))
              & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2))
              & v1_funct_1(X3) )
          & l1_pre_topc(X2)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ~ v5_pre_topc(k1_partfun1(u1_struct_0(sK0),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(sK1),X3,X4),sK0,sK1)
                & v5_pre_topc(X4,X2,sK1)
                & v5_pre_topc(X3,sK0,X2)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
                & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK1))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2))))
            & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2))
            & v1_funct_1(X3) )
        & l1_pre_topc(X2)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ~ v5_pre_topc(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK1),X3,X4),sK0,sK1)
              & v5_pre_topc(X4,sK2,sK1)
              & v5_pre_topc(X3,sK0,sK2)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
              & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
          & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(sK2))
          & v1_funct_1(X3) )
      & l1_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ~ v5_pre_topc(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK1),X3,X4),sK0,sK1)
            & v5_pre_topc(X4,sK2,sK1)
            & v5_pre_topc(X3,sK0,sK2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
            & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1))
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
        & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(sK2))
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ~ v5_pre_topc(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK1),sK3,X4),sK0,sK1)
          & v5_pre_topc(X4,sK2,sK1)
          & v5_pre_topc(sK3,sK0,sK2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
          & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1))
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
      & v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

% (20805)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
fof(f50,plain,
    ( ? [X4] :
        ( ~ v5_pre_topc(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK1),sK3,X4),sK0,sK1)
        & v5_pre_topc(X4,sK2,sK1)
        & v5_pre_topc(sK3,sK0,sK2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1))
        & v1_funct_1(X4) )
   => ( ~ v5_pre_topc(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK4),sK0,sK1)
      & v5_pre_topc(sK4,sK2,sK1)
      & v5_pre_topc(sK3,sK0,sK2)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ v5_pre_topc(k1_partfun1(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),X3,X4),X0,X1)
                      & v5_pre_topc(X4,X2,X1)
                      & v5_pre_topc(X3,X0,X2)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                  & v1_funct_1(X3) )
              & l1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ v5_pre_topc(k1_partfun1(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),X3,X4),X0,X1)
                      & v5_pre_topc(X4,X2,X1)
                      & v5_pre_topc(X3,X0,X2)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                  & v1_funct_1(X3) )
              & l1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( ( l1_pre_topc(X2)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                      & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                      & v1_funct_1(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( ( v5_pre_topc(X4,X2,X1)
                            & v5_pre_topc(X3,X0,X2) )
                         => v5_pre_topc(k1_partfun1(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),X3,X4),X0,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( ( v5_pre_topc(X4,X2,X1)
                          & v5_pre_topc(X3,X0,X2) )
                       => v5_pre_topc(k1_partfun1(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),X3,X4),X0,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_tops_2)).

fof(f1328,plain,(
    ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f1327,f63])).

fof(f63,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f1327,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f1326,f304])).

fof(f304,plain,(
    v1_funct_1(k5_relat_1(sK3,sK4)) ),
    inference(unit_resulting_resolution,[],[f69,f239,f260,f100])).

fof(f100,plain,(
    ! [X4,X3,X1] :
      ( v1_funct_1(k5_relat_1(X3,X4))
      | ~ v1_funct_1(X4)
      | ~ sP9(X4,X1)
      | sP10(X3,X1) ) ),
    inference(cnf_transformation,[],[f100_D])).

fof(f100_D,plain,(
    ! [X1,X3] :
      ( ! [X4] :
          ( v1_funct_1(k5_relat_1(X3,X4))
          | ~ v1_funct_1(X4)
          | ~ sP9(X4,X1) )
    <=> ~ sP10(X3,X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP10])])).

fof(f260,plain,(
    sP9(sK4,u1_struct_0(sK2)) ),
    inference(unit_resulting_resolution,[],[f70,f71,f98])).

fof(f98,plain,(
    ! [X4,X2,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | sP9(X4,X1) ) ),
    inference(cnf_transformation,[],[f98_D])).

fof(f98_D,plain,(
    ! [X1,X4] :
      ( ! [X2] :
          ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2) )
    <=> ~ sP9(X4,X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).

fof(f71,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f51])).

fof(f70,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f51])).

fof(f239,plain,(
    ~ sP10(sK3,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f238,f167])).

fof(f167,plain,(
    ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(unit_resulting_resolution,[],[f64,f125,f91])).

fof(f91,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f125,plain,(
    l1_struct_0(sK2) ),
    inference(unit_resulting_resolution,[],[f65,f93])).

fof(f93,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f65,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f64,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f238,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ sP10(sK3,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f237,f66])).

fof(f66,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f237,plain,
    ( ~ v1_funct_1(sK3)
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ sP10(sK3,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f225,f67])).

fof(f67,plain,(
    v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f51])).

fof(f225,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ sP10(sK3,u1_struct_0(sK2)) ),
    inference(resolution,[],[f68,f101])).

fof(f101,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X1)
      | ~ sP10(X3,X1) ) ),
    inference(general_splitting,[],[f99,f100_D])).

fof(f99,plain,(
    ! [X4,X0,X3,X1] :
      ( v1_funct_1(k5_relat_1(X3,X4))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X1)
      | ~ sP9(X4,X1) ) ),
    inference(general_splitting,[],[f82,f98_D])).

fof(f82,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k5_relat_1(X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( v1_funct_2(k5_relat_1(X3,X4),X0,X2)
        & v1_funct_1(k5_relat_1(X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( v1_funct_2(k5_relat_1(X3,X4),X0,X2)
        & v1_funct_1(k5_relat_1(X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X4,X1,X2)
        & v1_funct_1(X4)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & ~ v1_xboole_0(X1) )
     => ( v1_funct_2(k5_relat_1(X3,X4),X0,X2)
        & v1_funct_1(k5_relat_1(X3,X4)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_2)).

fof(f68,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f51])).

% (20793)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
fof(f69,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f1326,plain,
    ( ~ v1_funct_1(k5_relat_1(sK3,sK4))
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f1325,f256])).

fof(f256,plain,(
    v1_funct_2(k5_relat_1(sK3,sK4),u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(unit_resulting_resolution,[],[f69,f66,f167,f67,f68,f70,f71,f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k5_relat_1(X3,X4),X0,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1325,plain,
    ( ~ v1_funct_2(k5_relat_1(sK3,sK4),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k5_relat_1(sK3,sK4))
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f1324,f744])).

fof(f744,plain,(
    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(forward_demodulation,[],[f250,f254])).

fof(f254,plain,(
    k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(unit_resulting_resolution,[],[f66,f69,f68,f71,f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f250,plain,(
    m1_subset_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(unit_resulting_resolution,[],[f66,f69,f68,f71,f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f1324,plain,
    ( ~ m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k5_relat_1(sK3,sK4),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k5_relat_1(sK3,sK4))
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f1323,f575])).

fof(f575,plain,(
    ~ v5_pre_topc(k5_relat_1(sK3,sK4),sK0,sK1) ),
    inference(backward_demodulation,[],[f74,f254])).

fof(f74,plain,(
    ~ v5_pre_topc(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK4),sK0,sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f1323,plain,
    ( v5_pre_topc(k5_relat_1(sK3,sK4),sK0,sK1)
    | ~ m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k5_relat_1(sK3,sK4),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k5_relat_1(sK3,sK4))
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f1319,f961])).

fof(f961,plain,(
    v4_pre_topc(k10_relat_1(sK3,k10_relat_1(sK4,sK5(sK0,sK1,k5_relat_1(sK3,sK4)))),sK0) ),
    inference(forward_demodulation,[],[f959,f205])).

fof(f205,plain,(
    ! [X0] : k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK2),sK3,X0) = k10_relat_1(sK3,X0) ),
    inference(unit_resulting_resolution,[],[f68,f89])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f959,plain,(
    v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK2),sK3,k10_relat_1(sK4,sK5(sK0,sK1,k5_relat_1(sK3,sK4)))),sK0) ),
    inference(unit_resulting_resolution,[],[f62,f65,f66,f72,f67,f68,f356,f956,f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X1] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
      | ~ v4_pre_topc(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5(X0,X1,X2)),X0)
                    & v4_pre_topc(sK5(X0,X1,X2),X1)
                    & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v4_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f53,f54])).

fof(f54,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v4_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5(X0,X1,X2)),X0)
        & v4_pre_topc(sK5(X0,X1,X2),X1)
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v4_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v4_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v4_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      | ~ v4_pre_topc(X3,X1)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

% (20803)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( v4_pre_topc(X3,X1)
                     => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_pre_topc)).

fof(f956,plain,(
    v4_pre_topc(k10_relat_1(sK4,sK5(sK0,sK1,k5_relat_1(sK3,sK4))),sK2) ),
    inference(forward_demodulation,[],[f951,f258])).

fof(f258,plain,(
    ! [X0] : k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0) = k10_relat_1(sK4,X0) ),
    inference(unit_resulting_resolution,[],[f71,f89])).

fof(f951,plain,(
    v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,sK5(sK0,sK1,k5_relat_1(sK3,sK4))),sK2) ),
    inference(unit_resulting_resolution,[],[f65,f63,f69,f73,f70,f71,f826,f759,f78])).

fof(f759,plain,(
    m1_subset_1(sK5(sK0,sK1,k5_relat_1(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unit_resulting_resolution,[],[f62,f63,f304,f575,f256,f744,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f826,plain,(
    v4_pre_topc(sK5(sK0,sK1,k5_relat_1(sK3,sK4)),sK1) ),
    inference(subsumption_resolution,[],[f825,f62])).

fof(f825,plain,
    ( v4_pre_topc(sK5(sK0,sK1,k5_relat_1(sK3,sK4)),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f824,f63])).

fof(f824,plain,
    ( v4_pre_topc(sK5(sK0,sK1,k5_relat_1(sK3,sK4)),sK1)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f823,f304])).

fof(f823,plain,
    ( v4_pre_topc(sK5(sK0,sK1,k5_relat_1(sK3,sK4)),sK1)
    | ~ v1_funct_1(k5_relat_1(sK3,sK4))
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f822,f256])).

fof(f822,plain,
    ( v4_pre_topc(sK5(sK0,sK1,k5_relat_1(sK3,sK4)),sK1)
    | ~ v1_funct_2(k5_relat_1(sK3,sK4),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k5_relat_1(sK3,sK4))
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f804,f575])).

fof(f804,plain,
    ( v5_pre_topc(k5_relat_1(sK3,sK4),sK0,sK1)
    | v4_pre_topc(sK5(sK0,sK1,k5_relat_1(sK3,sK4)),sK1)
    | ~ v1_funct_2(k5_relat_1(sK3,sK4),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k5_relat_1(sK3,sK4))
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f744,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | v4_pre_topc(sK5(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f73,plain,(
    v5_pre_topc(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f356,plain,(
    ! [X0] : m1_subset_1(k10_relat_1(sK4,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(backward_demodulation,[],[f257,f258])).

fof(f257,plain,(
    ! [X0] : m1_subset_1(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unit_resulting_resolution,[],[f71,f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).

fof(f72,plain,(
    v5_pre_topc(sK3,sK0,sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f1319,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK3,k10_relat_1(sK4,sK5(sK0,sK1,k5_relat_1(sK3,sK4)))),sK0)
    | v5_pre_topc(k5_relat_1(sK3,sK4),sK0,sK1)
    | ~ m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k5_relat_1(sK3,sK4),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k5_relat_1(sK3,sK4))
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f81,f1258])).

fof(f1258,plain,(
    ! [X0] : k10_relat_1(sK3,k10_relat_1(sK4,X0)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k5_relat_1(sK3,sK4),X0) ),
    inference(forward_demodulation,[],[f799,f297])).

fof(f297,plain,(
    ! [X0] : k10_relat_1(k5_relat_1(sK3,sK4),X0) = k10_relat_1(sK3,k10_relat_1(sK4,X0)) ),
    inference(unit_resulting_resolution,[],[f206,f259,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).

fof(f259,plain,(
    v1_relat_1(sK4) ),
    inference(unit_resulting_resolution,[],[f71,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f206,plain,(
    v1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f68,f90])).

fof(f799,plain,(
    ! [X0] : k10_relat_1(k5_relat_1(sK3,sK4),X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k5_relat_1(sK3,sK4),X0) ),
    inference(unit_resulting_resolution,[],[f744,f89])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5(X0,X1,X2)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

%------------------------------------------------------------------------------
