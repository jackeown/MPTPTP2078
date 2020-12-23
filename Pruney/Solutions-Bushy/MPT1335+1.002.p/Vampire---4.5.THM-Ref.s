%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1335+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 714 expanded)
%              Number of leaves         :   17 ( 313 expanded)
%              Depth                    :   58
%              Number of atoms          :  977 (9226 expanded)
%              Number of equality atoms :   10 (  35 expanded)
%              Maximal formula depth    :   22 (  10 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f239,plain,(
    $false ),
    inference(subsumption_resolution,[],[f238,f55])).

fof(f55,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f19,f44,f43,f42,f41,f40])).

fof(f40,plain,
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

fof(f41,plain,
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

fof(f42,plain,
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

fof(f43,plain,
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

fof(f44,plain,
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

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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

fof(f238,plain,(
    ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f181,f66])).

fof(f66,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f181,plain,(
    ~ l1_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f177,f54])).

fof(f54,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f177,plain,
    ( ~ l1_struct_0(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f176,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f176,plain,(
    v1_xboole_0(u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f175,f57])).

fof(f57,plain,(
    v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f45])).

fof(f175,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f174,f58])).

fof(f58,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f45])).

fof(f174,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f173,f60])).

fof(f60,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f45])).

fof(f173,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2)) ),
    inference(duplicate_literal_removal,[],[f172])).

fof(f172,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(resolution,[],[f169,f61])).

fof(f61,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f45])).

fof(f169,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1))))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ v1_funct_2(sK4,X0,u1_struct_0(sK1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))
      | ~ v1_funct_2(sK3,u1_struct_0(sK0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f166,f113])).

fof(f113,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(k10_relat_1(sK3,k10_relat_1(sK4,sK5(sK0,sK1,k5_relat_1(sK3,sK4)))),sK0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,X0,u1_struct_0(sK1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))
      | ~ v1_funct_2(sK3,u1_struct_0(sK0),X0)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f112,f56])).

fof(f56,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f112,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(k10_relat_1(sK3,k10_relat_1(sK4,sK5(sK0,sK1,k5_relat_1(sK3,sK4)))),sK0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,X0,u1_struct_0(sK1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))
      | ~ v1_funct_2(sK3,u1_struct_0(sK0),X0)
      | ~ v1_funct_1(sK3)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f111,f59])).

fof(f59,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f111,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(k10_relat_1(sK3,k10_relat_1(sK4,sK5(sK0,sK1,k5_relat_1(sK3,sK4)))),sK0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,X0,u1_struct_0(sK1))
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))
      | ~ v1_funct_2(sK3,u1_struct_0(sK0),X0)
      | ~ v1_funct_1(sK3)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f110,f52])).

fof(f52,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f110,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(k10_relat_1(sK3,k10_relat_1(sK4,sK5(sK0,sK1,k5_relat_1(sK3,sK4)))),sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,X0,u1_struct_0(sK1))
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))
      | ~ v1_funct_2(sK3,u1_struct_0(sK0),X0)
      | ~ v1_funct_1(sK3)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f109,f53])).

fof(f53,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f109,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(k10_relat_1(sK3,k10_relat_1(sK4,sK5(sK0,sK1,k5_relat_1(sK3,sK4)))),sK0)
      | ~ l1_pre_topc(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,X0,u1_struct_0(sK1))
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))
      | ~ v1_funct_2(sK3,u1_struct_0(sK0),X0)
      | ~ v1_funct_1(sK3)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f108,f94])).

fof(f94,plain,(
    ~ v5_pre_topc(k5_relat_1(sK3,sK4),sK0,sK1) ),
    inference(subsumption_resolution,[],[f93,f56])).

fof(f93,plain,
    ( ~ v5_pre_topc(k5_relat_1(sK3,sK4),sK0,sK1)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f92,f58])).

fof(f92,plain,
    ( ~ v5_pre_topc(k5_relat_1(sK3,sK4),sK0,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f91,f59])).

fof(f91,plain,
    ( ~ v5_pre_topc(k5_relat_1(sK3,sK4),sK0,sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f88,f61])).

fof(f88,plain,
    ( ~ v5_pre_topc(k5_relat_1(sK3,sK4),sK0,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
    | ~ v1_funct_1(sK3) ),
    inference(superposition,[],[f64,f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f64,plain,(
    ~ v5_pre_topc(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK4),sK0,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f108,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k5_relat_1(X0,X1),X2,X3)
      | ~ v4_pre_topc(k10_relat_1(X0,k10_relat_1(X1,sK5(X2,X3,k5_relat_1(X0,X1)))),X2)
      | ~ l1_pre_topc(X3)
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,u1_struct_0(X3))))
      | ~ v1_funct_2(X1,X4,u1_struct_0(X3))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),X4)))
      | ~ v1_funct_2(X0,u1_struct_0(X2),X4)
      | ~ v1_funct_1(X0)
      | v1_xboole_0(X4) ) ),
    inference(subsumption_resolution,[],[f107,f96])).

fof(f96,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f95])).

fof(f95,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(superposition,[],[f84,f82])).

fof(f84,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f107,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k5_relat_1(X0,X1),X2,X3)
      | ~ m1_subset_1(k5_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
      | ~ v4_pre_topc(k10_relat_1(X0,k10_relat_1(X1,sK5(X2,X3,k5_relat_1(X0,X1)))),X2)
      | ~ l1_pre_topc(X3)
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,u1_struct_0(X3))))
      | ~ v1_funct_2(X1,X4,u1_struct_0(X3))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),X4)))
      | ~ v1_funct_2(X0,u1_struct_0(X2),X4)
      | ~ v1_funct_1(X0)
      | v1_xboole_0(X4) ) ),
    inference(subsumption_resolution,[],[f106,f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k5_relat_1(X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f106,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k5_relat_1(X0,X1),X2,X3)
      | ~ m1_subset_1(k5_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
      | ~ v4_pre_topc(k10_relat_1(X0,k10_relat_1(X1,sK5(X2,X3,k5_relat_1(X0,X1)))),X2)
      | ~ v1_funct_1(k5_relat_1(X0,X1))
      | ~ l1_pre_topc(X3)
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,u1_struct_0(X3))))
      | ~ v1_funct_2(X1,X4,u1_struct_0(X3))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),X4)))
      | ~ v1_funct_2(X0,u1_struct_0(X2),X4)
      | ~ v1_funct_1(X0)
      | v1_xboole_0(X4) ) ),
    inference(subsumption_resolution,[],[f105,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f105,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k5_relat_1(X0,X1),X2,X3)
      | ~ m1_subset_1(k5_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
      | ~ v4_pre_topc(k10_relat_1(X0,k10_relat_1(X1,sK5(X2,X3,k5_relat_1(X0,X1)))),X2)
      | ~ v1_funct_1(k5_relat_1(X0,X1))
      | ~ l1_pre_topc(X3)
      | ~ l1_pre_topc(X2)
      | ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,u1_struct_0(X3))))
      | ~ v1_funct_2(X1,X4,u1_struct_0(X3))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),X4)))
      | ~ v1_funct_2(X0,u1_struct_0(X2),X4)
      | ~ v1_funct_1(X0)
      | v1_xboole_0(X4) ) ),
    inference(subsumption_resolution,[],[f104,f76])).

fof(f104,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k5_relat_1(X0,X1),X2,X3)
      | ~ m1_subset_1(k5_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
      | ~ v4_pre_topc(k10_relat_1(X0,k10_relat_1(X1,sK5(X2,X3,k5_relat_1(X0,X1)))),X2)
      | ~ v1_funct_1(k5_relat_1(X0,X1))
      | ~ l1_pre_topc(X3)
      | ~ l1_pre_topc(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,u1_struct_0(X3))))
      | ~ v1_funct_2(X1,X4,u1_struct_0(X3))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),X4)))
      | ~ v1_funct_2(X0,u1_struct_0(X2),X4)
      | ~ v1_funct_1(X0)
      | v1_xboole_0(X4) ) ),
    inference(resolution,[],[f100,f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k5_relat_1(X3,X4),X0,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(k5_relat_1(X0,X1),u1_struct_0(X2),u1_struct_0(X3))
      | v5_pre_topc(k5_relat_1(X0,X1),X2,X3)
      | ~ m1_subset_1(k5_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
      | ~ v4_pre_topc(k10_relat_1(X0,k10_relat_1(X1,sK5(X2,X3,k5_relat_1(X0,X1)))),X2)
      | ~ v1_funct_1(k5_relat_1(X0,X1))
      | ~ l1_pre_topc(X3)
      | ~ l1_pre_topc(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f99,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_pre_topc(k10_relat_1(X2,sK5(X0,X1,X2)),X0)
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_pre_topc(k10_relat_1(X2,sK5(X0,X1,X2)),X0)
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) ) ),
    inference(superposition,[],[f70,f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5(X0,X1,X2)),X0)
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f47,f48])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v4_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5(X0,X1,X2)),X0)
        & v4_pre_topc(sK5(X0,X1,X2),X1)
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f166,plain,
    ( v4_pre_topc(k10_relat_1(sK3,k10_relat_1(sK4,sK5(sK0,sK1,k5_relat_1(sK3,sK4)))),sK0)
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f165,f52])).

fof(f165,plain,
    ( v4_pre_topc(k10_relat_1(sK3,k10_relat_1(sK4,sK5(sK0,sK1,k5_relat_1(sK3,sK4)))),sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f164,f56])).

fof(f164,plain,
    ( v4_pre_topc(k10_relat_1(sK3,k10_relat_1(sK4,sK5(sK0,sK1,k5_relat_1(sK3,sK4)))),sK0)
    | ~ v1_funct_1(sK3)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f163,f58])).

fof(f163,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
    | v4_pre_topc(k10_relat_1(sK3,k10_relat_1(sK4,sK5(sK0,sK1,k5_relat_1(sK3,sK4)))),sK0)
    | ~ v1_funct_1(sK3)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f161,f62])).

fof(f62,plain,(
    v5_pre_topc(sK3,sK0,sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f161,plain,
    ( ~ v5_pre_topc(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
    | v4_pre_topc(k10_relat_1(sK3,k10_relat_1(sK4,sK5(sK0,sK1,k5_relat_1(sK3,sK4)))),sK0)
    | ~ v1_funct_1(sK3)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(resolution,[],[f158,f57])).

fof(f158,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK2))
      | ~ v5_pre_topc(X1,X0,sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
      | v4_pre_topc(k10_relat_1(X1,k10_relat_1(sK4,sK5(sK0,sK1,k5_relat_1(sK3,sK4)))),X0)
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(u1_struct_0(sK2)) ) ),
    inference(duplicate_literal_removal,[],[f157])).

fof(f157,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k10_relat_1(X1,k10_relat_1(sK4,sK5(sK0,sK1,k5_relat_1(sK3,sK4)))),X0)
      | ~ v5_pre_topc(X1,X0,sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK2))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) ) ),
    inference(superposition,[],[f155,f79])).

fof(f155,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,k10_relat_1(sK4,sK5(sK0,sK1,k5_relat_1(sK3,sK4)))),X1)
      | ~ v5_pre_topc(X0,X1,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | v1_xboole_0(u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f154,f61])).

fof(f154,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X2)))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ v5_pre_topc(X1,X0,sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK2))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(sK2),X1,k10_relat_1(sK4,sK5(sK0,sK1,k5_relat_1(sK3,sK4)))),X0) ) ),
    inference(resolution,[],[f153,f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k10_relat_1(X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k10_relat_1(X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f78,f79])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).

fof(f153,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k10_relat_1(sK4,sK5(sK0,sK1,k5_relat_1(sK3,sK4))),k1_zfmisc_1(u1_struct_0(sK2)))
      | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(sK2),X1,k10_relat_1(sK4,sK5(sK0,sK1,k5_relat_1(sK3,sK4)))),X0)
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ v5_pre_topc(X1,X0,sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK2))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f152,f55])).

% (30204)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
fof(f152,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(u1_struct_0(sK2))
      | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(sK2),X1,k10_relat_1(sK4,sK5(sK0,sK1,k5_relat_1(sK3,sK4)))),X0)
      | ~ m1_subset_1(k10_relat_1(sK4,sK5(sK0,sK1,k5_relat_1(sK3,sK4))),k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v5_pre_topc(X1,X0,sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK2))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(sK2)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f151,f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v4_pre_topc(X4,X1)
      | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f151,plain,
    ( v4_pre_topc(k10_relat_1(sK4,sK5(sK0,sK1,k5_relat_1(sK3,sK4))),sK2)
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f149,f61])).

fof(f149,plain,
    ( v4_pre_topc(k10_relat_1(sK4,sK5(sK0,sK1,k5_relat_1(sK3,sK4))),sK2)
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(superposition,[],[f145,f79])).

fof(f145,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,sK5(sK0,sK1,k5_relat_1(sK3,sK4))),sK2)
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f144,f55])).

fof(f144,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,sK5(sK0,sK1,k5_relat_1(sK3,sK4))),sK2) ),
    inference(subsumption_resolution,[],[f143,f61])).

fof(f143,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,sK5(sK0,sK1,k5_relat_1(sK3,sK4))),sK2) ),
    inference(subsumption_resolution,[],[f142,f59])).

fof(f142,plain,
    ( ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,sK5(sK0,sK1,k5_relat_1(sK3,sK4))),sK2) ),
    inference(subsumption_resolution,[],[f140,f63])).

fof(f63,plain,(
    v5_pre_topc(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f140,plain,
    ( ~ v5_pre_topc(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,sK5(sK0,sK1,k5_relat_1(sK3,sK4))),sK2) ),
    inference(resolution,[],[f139,f60])).

fof(f139,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
      | ~ v5_pre_topc(X0,X1,sK1)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ l1_pre_topc(X1)
      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0,sK5(sK0,sK1,k5_relat_1(sK3,sK4))),X1) ) ),
    inference(resolution,[],[f138,f58])).

fof(f138,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X1,X0,sK1)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X1,sK5(sK0,sK1,k5_relat_1(sK3,sK4))),X0) ) ),
    inference(resolution,[],[f137,f61])).

fof(f137,plain,(
    ! [X6,X10,X8,X7,X5,X9] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | v4_pre_topc(k8_relset_1(u1_struct_0(X5),u1_struct_0(sK1),X6,sK5(sK0,sK1,k5_relat_1(sK3,sK4))),X5)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X6,X5,sK1)
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(sK1))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ l1_pre_topc(X5)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) ) ),
    inference(subsumption_resolution,[],[f136,f56])).

fof(f136,plain,(
    ! [X6,X10,X8,X7,X5,X9] :
      ( ~ l1_pre_topc(X5)
      | v4_pre_topc(k8_relset_1(u1_struct_0(X5),u1_struct_0(sK1),X6,sK5(sK0,sK1,k5_relat_1(sK3,sK4))),X5)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X6,X5,sK1)
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(sK1))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f133,f59])).

fof(f133,plain,(
    ! [X6,X10,X8,X7,X5,X9] :
      ( ~ l1_pre_topc(X5)
      | v4_pre_topc(k8_relset_1(u1_struct_0(X5),u1_struct_0(sK1),X6,sK5(sK0,sK1,k5_relat_1(sK3,sK4))),X5)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X6,X5,sK1)
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(sK1))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f131,f90])).

fof(f90,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k5_relat_1(X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f89])).

fof(f89,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k5_relat_1(X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(superposition,[],[f83,f82])).

fof(f83,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(k5_relat_1(sK3,sK4))
      | ~ l1_pre_topc(X1)
      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0,sK5(sK0,sK1,k5_relat_1(sK3,sK4))),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,X1,sK1)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
      | v1_xboole_0(u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f130,f57])).

fof(f130,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0,sK5(sK0,sK1,k5_relat_1(sK3,sK4))),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,X1,sK1)
      | ~ v1_funct_1(k5_relat_1(sK3,sK4))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2))
      | v1_xboole_0(u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f129,f58])).

fof(f129,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0,sK5(sK0,sK1,k5_relat_1(sK3,sK4))),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,X1,sK1)
      | ~ v1_funct_1(k5_relat_1(sK3,sK4))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2))
      | v1_xboole_0(u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f128,f60])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0,sK5(sK0,sK1,k5_relat_1(sK3,sK4))),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,X1,sK1)
      | ~ v1_funct_1(k5_relat_1(sK3,sK4))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2))
      | v1_xboole_0(u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f127,f61])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK1))))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0,sK5(sK0,sK1,k5_relat_1(sK3,sK4))),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,X1,sK1)
      | ~ v1_funct_1(k5_relat_1(sK3,sK4))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
      | ~ v1_funct_2(sK4,X2,u1_struct_0(sK1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X2)))
      | ~ v1_funct_2(sK3,u1_struct_0(sK0),X2)
      | v1_xboole_0(X2) ) ),
    inference(subsumption_resolution,[],[f126,f56])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0,sK5(sK0,sK1,k5_relat_1(sK3,sK4))),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,X1,sK1)
      | ~ v1_funct_1(k5_relat_1(sK3,sK4))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,X2,u1_struct_0(sK1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X2)))
      | ~ v1_funct_2(sK3,u1_struct_0(sK0),X2)
      | v1_xboole_0(X2)
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f125,f59])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0,sK5(sK0,sK1,k5_relat_1(sK3,sK4))),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,X1,sK1)
      | ~ v1_funct_1(k5_relat_1(sK3,sK4))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,X2,u1_struct_0(sK1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X2)))
      | ~ v1_funct_2(sK3,u1_struct_0(sK0),X2)
      | v1_xboole_0(X2)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_1(sK3) ) ),
    inference(condensation,[],[f124])).

fof(f124,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0,sK5(sK0,sK1,k5_relat_1(sK3,sK4))),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,X1,sK1)
      | ~ v1_funct_1(k5_relat_1(sK3,sK4))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,X2,u1_struct_0(sK1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X2)))
      | ~ v1_funct_2(sK3,u1_struct_0(sK0),X2)
      | v1_xboole_0(X2)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X4)))
      | ~ v1_funct_1(sK3) ) ),
    inference(condensation,[],[f123])).

fof(f123,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0,sK5(sK0,sK1,k5_relat_1(sK3,sK4))),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,X1,sK1)
      | ~ v1_funct_1(k5_relat_1(sK3,sK4))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,X2,u1_struct_0(sK1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X2)))
      | ~ v1_funct_2(sK3,u1_struct_0(sK0),X2)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,u1_struct_0(sK1))))
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X4)))
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f122,f96])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0,sK5(sK0,sK1,k5_relat_1(sK3,sK4))),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,X1,sK1)
      | ~ v1_funct_1(k5_relat_1(sK3,sK4))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,X2,u1_struct_0(sK1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X2)))
      | ~ v1_funct_2(sK3,u1_struct_0(sK0),X2)
      | v1_xboole_0(X2) ) ),
    inference(subsumption_resolution,[],[f121,f56])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0,sK5(sK0,sK1,k5_relat_1(sK3,sK4))),X1)
      | ~ m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,X1,sK1)
      | ~ v1_funct_1(k5_relat_1(sK3,sK4))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,X2,u1_struct_0(sK1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X2)))
      | ~ v1_funct_2(sK3,u1_struct_0(sK0),X2)
      | ~ v1_funct_1(sK3)
      | v1_xboole_0(X2) ) ),
    inference(subsumption_resolution,[],[f120,f59])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0,sK5(sK0,sK1,k5_relat_1(sK3,sK4))),X1)
      | ~ m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,X1,sK1)
      | ~ v1_funct_1(k5_relat_1(sK3,sK4))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,X2,u1_struct_0(sK1))
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X2)))
      | ~ v1_funct_2(sK3,u1_struct_0(sK0),X2)
      | ~ v1_funct_1(sK3)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f119,f81])).

fof(f119,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_2(k5_relat_1(sK3,sK4),u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
      | ~ v1_funct_2(X2,u1_struct_0(X3),u1_struct_0(sK1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X3)
      | v4_pre_topc(k8_relset_1(u1_struct_0(X3),u1_struct_0(sK1),X2,sK5(sK0,sK1,k5_relat_1(sK3,sK4))),X3)
      | ~ m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X2,X3,sK1)
      | ~ v1_funct_1(k5_relat_1(sK3,sK4)) ) ),
    inference(subsumption_resolution,[],[f118,f52])).

fof(f118,plain,(
    ! [X2,X3] :
      ( ~ v5_pre_topc(X2,X3,sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
      | ~ v1_funct_2(X2,u1_struct_0(X3),u1_struct_0(sK1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X3)
      | v4_pre_topc(k8_relset_1(u1_struct_0(X3),u1_struct_0(sK1),X2,sK5(sK0,sK1,k5_relat_1(sK3,sK4))),X3)
      | ~ m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v1_funct_2(k5_relat_1(sK3,sK4),u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(k5_relat_1(sK3,sK4))
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f115,f53])).

fof(f115,plain,(
    ! [X2,X3] :
      ( ~ v5_pre_topc(X2,X3,sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
      | ~ v1_funct_2(X2,u1_struct_0(X3),u1_struct_0(sK1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(sK1)
      | ~ l1_pre_topc(X3)
      | v4_pre_topc(k8_relset_1(u1_struct_0(X3),u1_struct_0(sK1),X2,sK5(sK0,sK1,k5_relat_1(sK3,sK4))),X3)
      | ~ m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v1_funct_2(k5_relat_1(sK3,sK4),u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(k5_relat_1(sK3,sK4))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f103,f94])).

fof(f103,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(X4,X3,X1)
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5(X3,X1,X4)),X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ l1_pre_topc(X3) ) ),
    inference(subsumption_resolution,[],[f102,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f102,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5(X3,X1,X4)),X0)
      | ~ m1_subset_1(sK5(X3,X1,X4),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | v5_pre_topc(X4,X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ l1_pre_topc(X3) ) ),
    inference(duplicate_literal_removal,[],[f101])).

fof(f101,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5(X3,X1,X4)),X0)
      | ~ m1_subset_1(sK5(X3,X1,X4),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | v5_pre_topc(X4,X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X3) ) ),
    inference(resolution,[],[f67,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(sK5(X0,X1,X2),X1)
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

%------------------------------------------------------------------------------
