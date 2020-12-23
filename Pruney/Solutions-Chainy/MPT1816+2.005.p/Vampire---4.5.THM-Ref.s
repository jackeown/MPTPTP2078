%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:45 EST 2020

% Result     : Theorem 1.82s
% Output     : Refutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :  292 (6263 expanded)
%              Number of leaves         :   35 (2577 expanded)
%              Depth                    :   31
%              Number of atoms          : 1703 (229810 expanded)
%              Number of equality atoms :   48 (7415 expanded)
%              Maximal formula depth    :   24 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2912,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f196,f202,f218,f226,f687,f750,f764,f907,f914,f946,f985,f997,f1010,f1026,f1031,f1033,f1035,f1038,f2908])).

fof(f2908,plain,
    ( ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | spl7_47 ),
    inference(avatar_contradiction_clause,[],[f2907])).

fof(f2907,plain,
    ( $false
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | spl7_47 ),
    inference(subsumption_resolution,[],[f2906,f233])).

fof(f233,plain,(
    l1_struct_0(sK5) ),
    inference(resolution,[],[f232,f111])).

fof(f111,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f232,plain,(
    l1_pre_topc(sK5) ),
    inference(subsumption_resolution,[],[f231,f64])).

fof(f64,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,
    ( ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      | ~ v5_pre_topc(sK4,sK2,sK3)
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK4) )
    & ( ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
        & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
        & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
        & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
        & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
        & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
        & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) )
      | ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
        & v5_pre_topc(sK4,sK2,sK3)
        & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
        & v1_funct_1(sK4) ) )
    & r4_tsep_1(sK2,sK5,sK6)
    & sK2 = k1_tsep_1(sK2,sK5,sK6)
    & m1_pre_topc(sK6,sK2)
    & ~ v2_struct_0(sK6)
    & m1_pre_topc(sK5,sK2)
    & ~ v2_struct_0(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    & v1_funct_1(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f45,f50,f49,f48,f47,f46])).

fof(f46,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
                          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          | ~ v5_pre_topc(X2,X0,X1)
                          | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          | ~ v1_funct_1(X2) )
                        & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                            & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
                          | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            & v5_pre_topc(X2,X0,X1)
                            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                            & v1_funct_1(X2) ) )
                        & r4_tsep_1(X0,X3,X4)
                        & k1_tsep_1(X0,X3,X4) = X0
                        & m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1)
                        | ~ v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(sK2,X1,X2,X4))
                        | ~ m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1)
                        | ~ v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(sK2,X1,X2,X3))
                        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                        | ~ v5_pre_topc(X2,sK2,X1)
                        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
                        | ~ v1_funct_1(X2) )
                      & ( ( m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(sK2,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(sK2,X1,X2,X3)) )
                        | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                          & v5_pre_topc(X2,sK2,X1)
                          & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
                          & v1_funct_1(X2) ) )
                      & r4_tsep_1(sK2,X3,X4)
                      & sK2 = k1_tsep_1(sK2,X3,X4)
                      & m1_pre_topc(X4,sK2)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,sK2)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ( ~ m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                      | ~ v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1)
                      | ~ v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                      | ~ v1_funct_1(k2_tmap_1(sK2,X1,X2,X4))
                      | ~ m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1)
                      | ~ v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(k2_tmap_1(sK2,X1,X2,X3))
                      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                      | ~ v5_pre_topc(X2,sK2,X1)
                      | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
                      | ~ v1_funct_1(X2) )
                    & ( ( m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                        & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1)
                        & v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                        & v1_funct_1(k2_tmap_1(sK2,X1,X2,X4))
                        & m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1)
                        & v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(k2_tmap_1(sK2,X1,X2,X3)) )
                      | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                        & v5_pre_topc(X2,sK2,X1)
                        & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
                        & v1_funct_1(X2) ) )
                    & r4_tsep_1(sK2,X3,X4)
                    & sK2 = k1_tsep_1(sK2,X3,X4)
                    & m1_pre_topc(X4,sK2)
                    & ~ v2_struct_0(X4) )
                & m1_pre_topc(X3,sK2)
                & ~ v2_struct_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
                    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X4),X4,sK3)
                    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3))
                    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,X2,X4))
                    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X3),X3,sK3)
                    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3))
                    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,X2,X3))
                    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
                    | ~ v5_pre_topc(X2,sK2,sK3)
                    | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3))
                    | ~ v1_funct_1(X2) )
                  & ( ( m1_subset_1(k2_tmap_1(sK2,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
                      & v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X4),X4,sK3)
                      & v1_funct_2(k2_tmap_1(sK2,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3))
                      & v1_funct_1(k2_tmap_1(sK2,sK3,X2,X4))
                      & m1_subset_1(k2_tmap_1(sK2,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                      & v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X3),X3,sK3)
                      & v1_funct_2(k2_tmap_1(sK2,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3))
                      & v1_funct_1(k2_tmap_1(sK2,sK3,X2,X3)) )
                    | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
                      & v5_pre_topc(X2,sK2,sK3)
                      & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3))
                      & v1_funct_1(X2) ) )
                  & r4_tsep_1(sK2,X3,X4)
                  & sK2 = k1_tsep_1(sK2,X3,X4)
                  & m1_pre_topc(X4,sK2)
                  & ~ v2_struct_0(X4) )
              & m1_pre_topc(X3,sK2)
              & ~ v2_struct_0(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
          & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
                  | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X4),X4,sK3)
                  | ~ v1_funct_2(k2_tmap_1(sK2,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3))
                  | ~ v1_funct_1(k2_tmap_1(sK2,sK3,X2,X4))
                  | ~ m1_subset_1(k2_tmap_1(sK2,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                  | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X3),X3,sK3)
                  | ~ v1_funct_2(k2_tmap_1(sK2,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3))
                  | ~ v1_funct_1(k2_tmap_1(sK2,sK3,X2,X3))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
                  | ~ v5_pre_topc(X2,sK2,sK3)
                  | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3))
                  | ~ v1_funct_1(X2) )
                & ( ( m1_subset_1(k2_tmap_1(sK2,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
                    & v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X4),X4,sK3)
                    & v1_funct_2(k2_tmap_1(sK2,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3))
                    & v1_funct_1(k2_tmap_1(sK2,sK3,X2,X4))
                    & m1_subset_1(k2_tmap_1(sK2,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                    & v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X3),X3,sK3)
                    & v1_funct_2(k2_tmap_1(sK2,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3))
                    & v1_funct_1(k2_tmap_1(sK2,sK3,X2,X3)) )
                  | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
                    & v5_pre_topc(X2,sK2,sK3)
                    & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3))
                    & v1_funct_1(X2) ) )
                & r4_tsep_1(sK2,X3,X4)
                & sK2 = k1_tsep_1(sK2,X3,X4)
                & m1_pre_topc(X4,sK2)
                & ~ v2_struct_0(X4) )
            & m1_pre_topc(X3,sK2)
            & ~ v2_struct_0(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
        & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
                | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3)
                | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3))
                | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4))
                | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X3),X3,sK3)
                | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X3),u1_struct_0(X3),u1_struct_0(sK3))
                | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X3))
                | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
                | ~ v5_pre_topc(sK4,sK2,sK3)
                | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
                | ~ v1_funct_1(sK4) )
              & ( ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
                  & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3)
                  & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3))
                  & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4))
                  & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                  & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X3),X3,sK3)
                  & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X3),u1_struct_0(X3),u1_struct_0(sK3))
                  & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X3)) )
                | ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
                  & v5_pre_topc(sK4,sK2,sK3)
                  & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
                  & v1_funct_1(sK4) ) )
              & r4_tsep_1(sK2,X3,X4)
              & sK2 = k1_tsep_1(sK2,X3,X4)
              & m1_pre_topc(X4,sK2)
              & ~ v2_struct_0(X4) )
          & m1_pre_topc(X3,sK2)
          & ~ v2_struct_0(X3) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
              | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3)
              | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3))
              | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4))
              | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
              | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X3),X3,sK3)
              | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X3),u1_struct_0(X3),u1_struct_0(sK3))
              | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X3))
              | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
              | ~ v5_pre_topc(sK4,sK2,sK3)
              | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
              | ~ v1_funct_1(sK4) )
            & ( ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
                & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3)
                & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3))
                & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4))
                & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X3),X3,sK3)
                & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X3),u1_struct_0(X3),u1_struct_0(sK3))
                & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X3)) )
              | ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
                & v5_pre_topc(sK4,sK2,sK3)
                & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
                & v1_funct_1(sK4) ) )
            & r4_tsep_1(sK2,X3,X4)
            & sK2 = k1_tsep_1(sK2,X3,X4)
            & m1_pre_topc(X4,sK2)
            & ~ v2_struct_0(X4) )
        & m1_pre_topc(X3,sK2)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
            | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3)
            | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3))
            | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4))
            | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
            | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
            | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
            | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
            | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
            | ~ v5_pre_topc(sK4,sK2,sK3)
            | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
            | ~ v1_funct_1(sK4) )
          & ( ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
              & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3)
              & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3))
              & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4))
              & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
              & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
              & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
              & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) )
            | ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
              & v5_pre_topc(sK4,sK2,sK3)
              & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
              & v1_funct_1(sK4) ) )
          & r4_tsep_1(sK2,sK5,X4)
          & sK2 = k1_tsep_1(sK2,sK5,X4)
          & m1_pre_topc(X4,sK2)
          & ~ v2_struct_0(X4) )
      & m1_pre_topc(sK5,sK2)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X4] :
        ( ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
          | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3)
          | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3))
          | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4))
          | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
          | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
          | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
          | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
          | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
          | ~ v5_pre_topc(sK4,sK2,sK3)
          | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
          | ~ v1_funct_1(sK4) )
        & ( ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
            & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3)
            & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3))
            & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4))
            & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
            & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
            & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
            & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) )
          | ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
            & v5_pre_topc(sK4,sK2,sK3)
            & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
            & v1_funct_1(sK4) ) )
        & r4_tsep_1(sK2,sK5,X4)
        & sK2 = k1_tsep_1(sK2,sK5,X4)
        & m1_pre_topc(X4,sK2)
        & ~ v2_struct_0(X4) )
   => ( ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
        | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
        | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
        | ~ v5_pre_topc(sK4,sK2,sK3)
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
        | ~ v1_funct_1(sK4) )
      & ( ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
          & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
          & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
          & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
          & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
          & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
          & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
          & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) )
        | ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
          & v5_pre_topc(sK4,sK2,sK3)
          & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
          & v1_funct_1(sK4) ) )
      & r4_tsep_1(sK2,sK5,sK6)
      & sK2 = k1_tsep_1(sK2,sK5,sK6)
      & m1_pre_topc(sK6,sK2)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
                        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        | ~ v5_pre_topc(X2,X0,X1)
                        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                        | ~ v1_funct_1(X2) )
                      & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
                        | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,X0,X1)
                          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X2) ) )
                      & r4_tsep_1(X0,X3,X4)
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
                        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        | ~ v5_pre_topc(X2,X0,X1)
                        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                        | ~ v1_funct_1(X2) )
                      & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
                        | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,X0,X1)
                          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X2) ) )
                      & r4_tsep_1(X0,X3,X4)
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,X0,X1)
                          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X2) )
                      <~> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) )
                      & r4_tsep_1(X0,X3,X4)
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,X0,X1)
                          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X2) )
                      <~> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) )
                      & r4_tsep_1(X0,X3,X4)
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_pre_topc(X4,X0)
                          & ~ v2_struct_0(X4) )
                       => ( ( r4_tsep_1(X0,X3,X4)
                            & k1_tsep_1(X0,X3,X4) = X0 )
                         => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                              & v5_pre_topc(X2,X0,X1)
                              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                              & v1_funct_1(X2) )
                          <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                              & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                              & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                              & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                              & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                              & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( r4_tsep_1(X0,X3,X4)
                          & k1_tsep_1(X0,X3,X4) = X0 )
                       => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            & v5_pre_topc(X2,X0,X1)
                            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                            & v1_funct_1(X2) )
                        <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                            & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_tmap_1)).

fof(f231,plain,
    ( l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f72,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f72,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f2906,plain,
    ( ~ l1_struct_0(sK5)
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | spl7_47 ),
    inference(subsumption_resolution,[],[f2905,f526])).

fof(f526,plain,
    ( v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK5)),sK5,sK3)
    | ~ spl7_7 ),
    inference(backward_demodulation,[],[f174,f512])).

fof(f512,plain,(
    k2_tmap_1(sK2,sK3,sK4,sK5) = k7_relat_1(sK4,u1_struct_0(sK5)) ),
    inference(resolution,[],[f507,f72])).

fof(f507,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK2)
      | k2_tmap_1(sK2,sK3,sK4,X2) = k7_relat_1(sK4,u1_struct_0(X2)) ) ),
    inference(forward_demodulation,[],[f270,f279])).

fof(f279,plain,(
    ! [X5] : k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X5) = k7_relat_1(sK4,X5) ),
    inference(subsumption_resolution,[],[f251,f68])).

fof(f68,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f251,plain,(
    ! [X5] :
      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X5) = k7_relat_1(sK4,X5)
      | ~ v1_funct_1(sK4) ) ),
    inference(resolution,[],[f70,f145])).

fof(f145,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f70,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f51])).

fof(f270,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK2)
      | k2_tmap_1(sK2,sK3,sK4,X2) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X2)) ) ),
    inference(subsumption_resolution,[],[f269,f62])).

fof(f62,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f269,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK2)
      | k2_tmap_1(sK2,sK3,sK4,X2) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X2))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f268,f63])).

fof(f63,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f268,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK2)
      | k2_tmap_1(sK2,sK3,sK4,X2) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X2))
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f267,f64])).

fof(f267,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK2)
      | k2_tmap_1(sK2,sK3,sK4,X2) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X2))
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f266,f65])).

fof(f65,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f266,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK2)
      | k2_tmap_1(sK2,sK3,sK4,X2) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X2))
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f265,f66])).

fof(f66,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f265,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK2)
      | k2_tmap_1(sK2,sK3,sK4,X2) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X2))
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f264,f67])).

fof(f67,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f264,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK2)
      | k2_tmap_1(sK2,sK3,sK4,X2) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X2))
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f263,f68])).

fof(f263,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK2)
      | k2_tmap_1(sK2,sK3,sK4,X2) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X2))
      | ~ v1_funct_1(sK4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f249,f69])).

fof(f69,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f51])).

fof(f249,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK2)
      | k2_tmap_1(sK2,sK3,sK4,X2) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X2))
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f70,f128])).

fof(f128,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X0)
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f174,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl7_7
  <=> v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f2905,plain,
    ( ~ v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK5)),sK5,sK3)
    | ~ l1_struct_0(sK5)
    | ~ spl7_6
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | spl7_47 ),
    inference(subsumption_resolution,[],[f2904,f900])).

fof(f900,plain,
    ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
    | spl7_47 ),
    inference(avatar_component_clause,[],[f899])).

fof(f899,plain,
    ( spl7_47
  <=> sP0(sK3,sK6,sK4,sK2,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f2904,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5)
    | ~ v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK5)),sK5,sK3)
    | ~ l1_struct_0(sK5)
    | ~ spl7_6
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f2896,f525])).

fof(f525,plain,
    ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f170,f512])).

fof(f170,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl7_6
  <=> v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f2896,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK5),u1_struct_0(sK3))
    | sP0(sK3,sK6,sK4,sK2,sK5)
    | ~ v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK5)),sK5,sK3)
    | ~ l1_struct_0(sK5)
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(superposition,[],[f1507,f512])).

fof(f1507,plain,
    ( ! [X2] :
        ( ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X2),u1_struct_0(X2),u1_struct_0(sK3))
        | sP0(sK3,sK6,sK4,sK2,X2)
        | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X2),X2,sK3)
        | ~ l1_struct_0(X2) )
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f1506,f258])).

fof(f258,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) ) ),
    inference(subsumption_resolution,[],[f257,f229])).

fof(f229,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f64,f111])).

fof(f257,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0))
      | ~ l1_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f256,f230])).

fof(f230,plain,(
    l1_struct_0(sK3) ),
    inference(resolution,[],[f67,f111])).

fof(f256,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0))
      | ~ l1_struct_0(sK3)
      | ~ l1_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f255,f68])).

fof(f255,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0))
      | ~ v1_funct_1(sK4)
      | ~ l1_struct_0(sK3)
      | ~ l1_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f247,f69])).

fof(f247,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0))
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK4)
      | ~ l1_struct_0(sK3)
      | ~ l1_struct_0(sK2) ) ),
    inference(resolution,[],[f70,f142])).

fof(f142,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( l1_struct_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(X2)
        & l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tmap_1)).

fof(f1506,plain,
    ( ! [X2] :
        ( ~ l1_struct_0(X2)
        | sP0(sK3,sK6,sK4,sK2,X2)
        | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X2),X2,sK3)
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X2),u1_struct_0(X2),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X2)) )
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f1505,f612])).

fof(f612,plain,
    ( v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK6)))
    | ~ spl7_9 ),
    inference(backward_demodulation,[],[f182,f513])).

fof(f513,plain,(
    k2_tmap_1(sK2,sK3,sK4,sK6) = k7_relat_1(sK4,u1_struct_0(sK6)) ),
    inference(resolution,[],[f507,f74])).

fof(f74,plain,(
    m1_pre_topc(sK6,sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f182,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl7_9
  <=> v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f1505,plain,
    ( ! [X2] :
        ( ~ l1_struct_0(X2)
        | ~ v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK6)))
        | sP0(sK3,sK6,sK4,sK2,X2)
        | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X2),X2,sK3)
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X2),u1_struct_0(X2),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X2)) )
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f1504,f613])).

fof(f613,plain,
    ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ spl7_10 ),
    inference(backward_demodulation,[],[f186,f513])).

fof(f186,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl7_10
  <=> v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f1504,plain,
    ( ! [X2] :
        ( ~ l1_struct_0(X2)
        | ~ v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3))
        | ~ v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK6)))
        | sP0(sK3,sK6,sK4,sK2,X2)
        | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X2),X2,sK3)
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X2),u1_struct_0(X2),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X2)) )
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f1503,f614])).

fof(f614,plain,
    ( v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3)
    | ~ spl7_11 ),
    inference(backward_demodulation,[],[f190,f513])).

fof(f190,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl7_11
  <=> v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f1503,plain,
    ( ! [X2] :
        ( ~ l1_struct_0(X2)
        | ~ v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3)
        | ~ v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3))
        | ~ v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK6)))
        | sP0(sK3,sK6,sK4,sK2,X2)
        | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X2),X2,sK3)
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X2),u1_struct_0(X2),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X2)) )
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f1495,f615])).

fof(f615,plain,
    ( m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ spl7_12 ),
    inference(backward_demodulation,[],[f194,f513])).

fof(f194,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl7_12
  <=> m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f1495,plain,(
    ! [X2] :
      ( ~ m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
      | ~ l1_struct_0(X2)
      | ~ v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3)
      | ~ v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3))
      | ~ v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK6)))
      | sP0(sK3,sK6,sK4,sK2,X2)
      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X2),X2,sK3)
      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X2),u1_struct_0(X2),u1_struct_0(sK3))
      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X2)) ) ),
    inference(superposition,[],[f477,f513])).

fof(f477,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
      | ~ l1_struct_0(X2)
      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X3),X3,sK3)
      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X3),u1_struct_0(X3),u1_struct_0(sK3))
      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X3))
      | sP0(sK3,X3,sK4,sK2,X2)
      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X2),X2,sK3)
      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X2),u1_struct_0(X2),u1_struct_0(sK3))
      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X2)) ) ),
    inference(resolution,[],[f262,f126])).

fof(f126,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
      | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
      | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
      | sP0(X0,X1,X2,X3,X4)
      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
      | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
      | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
        | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
        | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
        | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
        | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) )
      & ( ( m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
          & v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
          & m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
          & v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
          & v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
          & v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) )
        | ~ sP0(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f56])).

fof(f56,plain,(
    ! [X1,X3,X4,X0,X2] :
      ( ( sP0(X1,X3,X4,X0,X2)
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
        | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
        | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) )
      & ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
          & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) )
        | ~ sP0(X1,X3,X4,X0,X2) ) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X1,X3,X4,X0,X2] :
      ( ( sP0(X1,X3,X4,X0,X2)
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
        | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
        | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) )
      & ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
          & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) )
        | ~ sP0(X1,X3,X4,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X1,X3,X4,X0,X2] :
      ( sP0(X1,X3,X4,X0,X2)
    <=> ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
        & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f262,plain,(
    ! [X1] :
      ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
      | ~ l1_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f261,f229])).

fof(f261,plain,(
    ! [X1] :
      ( ~ l1_struct_0(X1)
      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
      | ~ l1_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f260,f230])).

fof(f260,plain,(
    ! [X1] :
      ( ~ l1_struct_0(X1)
      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
      | ~ l1_struct_0(sK3)
      | ~ l1_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f259,f68])).

fof(f259,plain,(
    ! [X1] :
      ( ~ l1_struct_0(X1)
      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
      | ~ v1_funct_1(sK4)
      | ~ l1_struct_0(sK3)
      | ~ l1_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f248,f69])).

fof(f248,plain,(
    ! [X1] :
      ( ~ l1_struct_0(X1)
      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK4)
      | ~ l1_struct_0(sK3)
      | ~ l1_struct_0(sK2) ) ),
    inference(resolution,[],[f70,f144])).

fof(f144,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f1038,plain,
    ( spl7_3
    | ~ spl7_46
    | ~ spl7_47 ),
    inference(avatar_contradiction_clause,[],[f1037])).

fof(f1037,plain,
    ( $false
    | spl7_3
    | ~ spl7_46
    | ~ spl7_47 ),
    inference(subsumption_resolution,[],[f1036,f159])).

fof(f159,plain,
    ( ~ v5_pre_topc(sK4,sK2,sK3)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl7_3
  <=> v5_pre_topc(sK4,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f1036,plain,
    ( v5_pre_topc(sK4,sK2,sK3)
    | ~ spl7_46
    | ~ spl7_47 ),
    inference(subsumption_resolution,[],[f924,f901])).

fof(f901,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5)
    | ~ spl7_47 ),
    inference(avatar_component_clause,[],[f899])).

fof(f924,plain,
    ( v5_pre_topc(sK4,sK2,sK3)
    | ~ sP0(sK3,sK6,sK4,sK2,sK5)
    | ~ spl7_46 ),
    inference(forward_demodulation,[],[f923,f516])).

fof(f516,plain,(
    sK4 = k2_tmap_1(sK2,sK3,sK4,sK2) ),
    inference(forward_demodulation,[],[f511,f287])).

fof(f287,plain,(
    sK4 = k7_relat_1(sK4,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f284,f280])).

fof(f280,plain,(
    v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f254,f129])).

fof(f129,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f254,plain,
    ( v1_relat_1(sK4)
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) ),
    inference(resolution,[],[f70,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f284,plain,
    ( sK4 = k7_relat_1(sK4,u1_struct_0(sK2))
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f282,f130])).

fof(f130,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(f282,plain,(
    r1_tarski(k1_relat_1(sK4),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f281,f280])).

fof(f281,plain,
    ( r1_tarski(k1_relat_1(sK4),u1_struct_0(sK2))
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f252,f131])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f252,plain,(
    v4_relat_1(sK4,u1_struct_0(sK2)) ),
    inference(resolution,[],[f70,f138])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f511,plain,(
    k7_relat_1(sK4,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK3,sK4,sK2) ),
    inference(resolution,[],[f507,f245])).

fof(f245,plain,(
    m1_pre_topc(sK2,sK2) ),
    inference(subsumption_resolution,[],[f244,f62])).

fof(f244,plain,
    ( m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f243,f64])).

fof(f243,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f242,f71])).

fof(f71,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f242,plain,
    ( m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f241,f72])).

fof(f241,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f240,f73])).

fof(f73,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f51])).

fof(f240,plain,
    ( m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f238,f74])).

fof(f238,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ m1_pre_topc(sK6,sK2)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(superposition,[],[f140,f75])).

fof(f75,plain,(
    sK2 = k1_tsep_1(sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f51])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(f923,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3)
    | ~ sP0(sK3,sK6,sK4,sK2,sK5)
    | ~ spl7_46 ),
    inference(forward_demodulation,[],[f917,f75])).

fof(f917,plain,
    ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)
    | ~ spl7_46 ),
    inference(resolution,[],[f896,f116])).

fof(f116,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3,X4)
      | ~ sP0(X4,X3,X2,X1,X0)
      | v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( ( ( m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))))
            & v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4)
            & v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))
            & v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) )
          | ~ sP0(X4,X3,X2,X1,X0) )
        & ( sP0(X4,X3,X2,X1,X0)
          | ~ m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))))
          | ~ v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4)
          | ~ v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))
          | ~ v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) ) )
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X4,X3,X1] :
      ( ( ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
            & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
            & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
            & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
          | ~ sP0(X1,X3,X4,X0,X2) )
        & ( sP0(X1,X3,X4,X0,X2)
          | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
          | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) ) )
      | ~ sP1(X2,X0,X4,X3,X1) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X4,X3,X1] :
      ( ( ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
            & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
            & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
            & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
          | ~ sP0(X1,X3,X4,X0,X2) )
        & ( sP0(X1,X3,X4,X0,X2)
          | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
          | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) ) )
      | ~ sP1(X2,X0,X4,X3,X1) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X4,X3,X1] :
      ( ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
      <=> sP0(X1,X3,X4,X0,X2) )
      | ~ sP1(X2,X0,X4,X3,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f896,plain,
    ( sP1(sK5,sK2,sK4,sK6,sK3)
    | ~ spl7_46 ),
    inference(avatar_component_clause,[],[f895])).

fof(f895,plain,
    ( spl7_46
  <=> sP1(sK5,sK2,sK4,sK6,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f1035,plain,(
    spl7_4 ),
    inference(avatar_contradiction_clause,[],[f1034])).

fof(f1034,plain,
    ( $false
    | spl7_4 ),
    inference(subsumption_resolution,[],[f163,f70])).

fof(f163,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | spl7_4 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl7_4
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f1033,plain,(
    spl7_2 ),
    inference(avatar_contradiction_clause,[],[f1032])).

fof(f1032,plain,
    ( $false
    | spl7_2 ),
    inference(subsumption_resolution,[],[f155,f69])).

fof(f155,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | spl7_2 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl7_2
  <=> v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f1031,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f1030])).

fof(f1030,plain,
    ( $false
    | spl7_1 ),
    inference(subsumption_resolution,[],[f151,f68])).

fof(f151,plain,
    ( ~ v1_funct_1(sK4)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl7_1
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f1026,plain,
    ( spl7_7
    | ~ spl7_47 ),
    inference(avatar_contradiction_clause,[],[f1025])).

fof(f1025,plain,
    ( $false
    | spl7_7
    | ~ spl7_47 ),
    inference(subsumption_resolution,[],[f937,f1023])).

fof(f1023,plain,
    ( ~ v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK5)),sK5,sK3)
    | spl7_7 ),
    inference(forward_demodulation,[],[f175,f512])).

fof(f175,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f173])).

fof(f937,plain,
    ( v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK5)),sK5,sK3)
    | ~ spl7_47 ),
    inference(forward_demodulation,[],[f929,f512])).

fof(f929,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ spl7_47 ),
    inference(resolution,[],[f901,f120])).

fof(f120,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3,X4)
      | v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f1010,plain,(
    spl7_6 ),
    inference(avatar_contradiction_clause,[],[f1009])).

fof(f1009,plain,
    ( $false
    | spl7_6 ),
    inference(subsumption_resolution,[],[f550,f999])).

fof(f999,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK5),u1_struct_0(sK3))
    | spl7_6 ),
    inference(forward_demodulation,[],[f171,f512])).

fof(f171,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | spl7_6 ),
    inference(avatar_component_clause,[],[f169])).

fof(f550,plain,(
    v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f549,f229])).

fof(f549,plain,
    ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ l1_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f548,f230])).

fof(f548,plain,
    ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f547,f68])).

fof(f547,plain,
    ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f546,f69])).

fof(f546,plain,
    ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f545,f70])).

fof(f545,plain,
    ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f541,f233])).

fof(f541,plain,
    ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ l1_struct_0(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2) ),
    inference(superposition,[],[f143,f512])).

fof(f143,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f997,plain,(
    spl7_8 ),
    inference(avatar_contradiction_clause,[],[f996])).

fof(f996,plain,
    ( $false
    | spl7_8 ),
    inference(subsumption_resolution,[],[f980,f986])).

fof(f986,plain,
    ( ~ r1_tarski(k7_relat_1(sK4,u1_struct_0(sK5)),k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))
    | spl7_8 ),
    inference(resolution,[],[f983,f137])).

fof(f137,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f983,plain,
    ( ~ m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | spl7_8 ),
    inference(forward_demodulation,[],[f179,f512])).

fof(f179,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | spl7_8 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl7_8
  <=> m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f980,plain,(
    r1_tarski(k7_relat_1(sK4,u1_struct_0(sK5)),k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f826,f233])).

fof(f826,plain,
    ( r1_tarski(k7_relat_1(sK4,u1_struct_0(sK5)),k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))
    | ~ l1_struct_0(sK5) ),
    inference(superposition,[],[f484,f512])).

fof(f484,plain,(
    ! [X16] :
      ( r1_tarski(k2_tmap_1(sK2,sK3,sK4,X16),k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(sK3)))
      | ~ l1_struct_0(X16) ) ),
    inference(resolution,[],[f262,f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f985,plain,
    ( spl7_5
    | ~ spl7_47 ),
    inference(avatar_contradiction_clause,[],[f984])).

fof(f984,plain,
    ( $false
    | spl7_5
    | ~ spl7_47 ),
    inference(subsumption_resolution,[],[f935,f979])).

fof(f979,plain,
    ( ~ v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK5)))
    | spl7_5 ),
    inference(forward_demodulation,[],[f167,f512])).

fof(f167,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | spl7_5 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl7_5
  <=> v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f935,plain,
    ( v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK5)))
    | ~ spl7_47 ),
    inference(forward_demodulation,[],[f927,f512])).

fof(f927,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ spl7_47 ),
    inference(resolution,[],[f901,f118])).

fof(f118,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3,X4)
      | v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f946,plain,
    ( spl7_11
    | ~ spl7_47 ),
    inference(avatar_contradiction_clause,[],[f945])).

fof(f945,plain,
    ( $false
    | spl7_11
    | ~ spl7_47 ),
    inference(subsumption_resolution,[],[f941,f777])).

fof(f777,plain,
    ( ~ v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3)
    | spl7_11 ),
    inference(forward_demodulation,[],[f191,f513])).

fof(f191,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | spl7_11 ),
    inference(avatar_component_clause,[],[f189])).

fof(f941,plain,
    ( v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3)
    | ~ spl7_47 ),
    inference(forward_demodulation,[],[f933,f513])).

fof(f933,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ spl7_47 ),
    inference(resolution,[],[f901,f124])).

fof(f124,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3,X4)
      | v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f914,plain,(
    spl7_46 ),
    inference(avatar_contradiction_clause,[],[f913])).

fof(f913,plain,
    ( $false
    | spl7_46 ),
    inference(subsumption_resolution,[],[f912,f71])).

fof(f912,plain,
    ( v2_struct_0(sK5)
    | spl7_46 ),
    inference(subsumption_resolution,[],[f911,f72])).

fof(f911,plain,
    ( ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | spl7_46 ),
    inference(subsumption_resolution,[],[f910,f73])).

fof(f910,plain,
    ( v2_struct_0(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | spl7_46 ),
    inference(subsumption_resolution,[],[f909,f74])).

fof(f909,plain,
    ( ~ m1_pre_topc(sK6,sK2)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | spl7_46 ),
    inference(subsumption_resolution,[],[f908,f76])).

fof(f76,plain,(
    r4_tsep_1(sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f51])).

fof(f908,plain,
    ( ~ r4_tsep_1(sK2,sK5,sK6)
    | ~ m1_pre_topc(sK6,sK2)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | spl7_46 ),
    inference(resolution,[],[f897,f278])).

fof(f278,plain,(
    ! [X4,X3] :
      ( sP1(X3,sK2,sK4,X4,sK3)
      | ~ r4_tsep_1(sK2,X3,X4)
      | ~ m1_pre_topc(X4,sK2)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,sK2)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f277,f62])).

fof(f277,plain,(
    ! [X4,X3] :
      ( sP1(X3,sK2,sK4,X4,sK3)
      | ~ r4_tsep_1(sK2,X3,X4)
      | ~ m1_pre_topc(X4,sK2)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,sK2)
      | v2_struct_0(X3)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f276,f63])).

fof(f276,plain,(
    ! [X4,X3] :
      ( sP1(X3,sK2,sK4,X4,sK3)
      | ~ r4_tsep_1(sK2,X3,X4)
      | ~ m1_pre_topc(X4,sK2)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,sK2)
      | v2_struct_0(X3)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f275,f64])).

fof(f275,plain,(
    ! [X4,X3] :
      ( sP1(X3,sK2,sK4,X4,sK3)
      | ~ r4_tsep_1(sK2,X3,X4)
      | ~ m1_pre_topc(X4,sK2)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,sK2)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f274,f65])).

fof(f274,plain,(
    ! [X4,X3] :
      ( sP1(X3,sK2,sK4,X4,sK3)
      | ~ r4_tsep_1(sK2,X3,X4)
      | ~ m1_pre_topc(X4,sK2)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,sK2)
      | v2_struct_0(X3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f273,f66])).

fof(f273,plain,(
    ! [X4,X3] :
      ( sP1(X3,sK2,sK4,X4,sK3)
      | ~ r4_tsep_1(sK2,X3,X4)
      | ~ m1_pre_topc(X4,sK2)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,sK2)
      | v2_struct_0(X3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f272,f67])).

fof(f272,plain,(
    ! [X4,X3] :
      ( sP1(X3,sK2,sK4,X4,sK3)
      | ~ r4_tsep_1(sK2,X3,X4)
      | ~ m1_pre_topc(X4,sK2)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,sK2)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f271,f68])).

fof(f271,plain,(
    ! [X4,X3] :
      ( sP1(X3,sK2,sK4,X4,sK3)
      | ~ v1_funct_1(sK4)
      | ~ r4_tsep_1(sK2,X3,X4)
      | ~ m1_pre_topc(X4,sK2)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,sK2)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f250,f69])).

fof(f250,plain,(
    ! [X4,X3] :
      ( sP1(X3,sK2,sK4,X4,sK3)
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK4)
      | ~ r4_tsep_1(sK2,X3,X4)
      | ~ m1_pre_topc(X4,sK2)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,sK2)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f70,f127])).

fof(f127,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | sP1(X2,X0,X4,X3,X1)
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ r4_tsep_1(X0,X2,X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( sP1(X2,X0,X4,X3,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r4_tsep_1(X0,X2,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f26,f42,f41])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
                      <=> ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                          & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r4_tsep_1(X0,X2,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
                      <=> ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                          & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r4_tsep_1(X0,X2,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( r4_tsep_1(X0,X2,X3)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
                        <=> ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                            & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_tmap_1)).

fof(f897,plain,
    ( ~ sP1(sK5,sK2,sK4,sK6,sK3)
    | spl7_46 ),
    inference(avatar_component_clause,[],[f895])).

fof(f907,plain,
    ( ~ spl7_46
    | spl7_47
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f906,f157,f899,f895])).

fof(f906,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5)
    | ~ sP1(sK5,sK2,sK4,sK6,sK3)
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f905,f68])).

fof(f905,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5)
    | ~ v1_funct_1(sK4)
    | ~ sP1(sK5,sK2,sK4,sK6,sK3)
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f904,f69])).

fof(f904,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ sP1(sK5,sK2,sK4,sK6,sK3)
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f903,f158])).

fof(f158,plain,
    ( v5_pre_topc(sK4,sK2,sK3)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f157])).

fof(f903,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ sP1(sK5,sK2,sK4,sK6,sK3) ),
    inference(subsumption_resolution,[],[f886,f70])).

fof(f886,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | sP0(sK3,sK6,sK4,sK2,sK5)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ sP1(sK5,sK2,sK4,sK6,sK3) ),
    inference(superposition,[],[f239,f516])).

fof(f239,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_tmap_1(sK2,X0,X1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
      | sP0(X0,sK6,X1,sK2,sK5)
      | ~ v5_pre_topc(k2_tmap_1(sK2,X0,X1,sK2),sK2,X0)
      | ~ v1_funct_2(k2_tmap_1(sK2,X0,X1,sK2),u1_struct_0(sK2),u1_struct_0(X0))
      | ~ v1_funct_1(k2_tmap_1(sK2,X0,X1,sK2))
      | ~ sP1(sK5,sK2,X1,sK6,X0) ) ),
    inference(superposition,[],[f113,f75])).

fof(f113,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))))
      | sP0(X4,X3,X2,X1,X0)
      | ~ v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4)
      | ~ v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))
      | ~ v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)))
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f764,plain,(
    spl7_10 ),
    inference(avatar_contradiction_clause,[],[f763])).

fof(f763,plain,
    ( $false
    | spl7_10 ),
    inference(subsumption_resolution,[],[f637,f753])).

fof(f753,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3))
    | spl7_10 ),
    inference(forward_demodulation,[],[f187,f513])).

fof(f187,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | spl7_10 ),
    inference(avatar_component_clause,[],[f185])).

fof(f637,plain,(
    v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f636,f229])).

fof(f636,plain,
    ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ l1_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f635,f230])).

fof(f635,plain,
    ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f634,f68])).

fof(f634,plain,
    ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f633,f69])).

fof(f633,plain,
    ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f632,f70])).

fof(f632,plain,
    ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f628,f236])).

fof(f236,plain,(
    l1_struct_0(sK6) ),
    inference(resolution,[],[f235,f111])).

fof(f235,plain,(
    l1_pre_topc(sK6) ),
    inference(subsumption_resolution,[],[f234,f64])).

fof(f234,plain,
    ( l1_pre_topc(sK6)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f74,f112])).

fof(f628,plain,
    ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ l1_struct_0(sK6)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2) ),
    inference(superposition,[],[f143,f513])).

fof(f750,plain,(
    spl7_12 ),
    inference(avatar_contradiction_clause,[],[f749])).

fof(f749,plain,
    ( $false
    | spl7_12 ),
    inference(subsumption_resolution,[],[f631,f691])).

fof(f691,plain,
    ( ~ m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | spl7_12 ),
    inference(forward_demodulation,[],[f195,f513])).

fof(f195,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | spl7_12 ),
    inference(avatar_component_clause,[],[f193])).

fof(f631,plain,(
    m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
    inference(subsumption_resolution,[],[f627,f236])).

fof(f627,plain,
    ( m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ l1_struct_0(sK6) ),
    inference(superposition,[],[f262,f513])).

fof(f687,plain,(
    spl7_9 ),
    inference(avatar_contradiction_clause,[],[f686])).

fof(f686,plain,
    ( $false
    | spl7_9 ),
    inference(subsumption_resolution,[],[f684,f685])).

fof(f685,plain,
    ( ~ v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK6)))
    | spl7_9 ),
    inference(forward_demodulation,[],[f183,f513])).

fof(f183,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | spl7_9 ),
    inference(avatar_component_clause,[],[f181])).

fof(f684,plain,(
    v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK6))) ),
    inference(forward_demodulation,[],[f311,f513])).

fof(f311,plain,(
    v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    inference(resolution,[],[f258,f236])).

fof(f226,plain,
    ( spl7_3
    | spl7_5 ),
    inference(avatar_split_clause,[],[f79,f165,f157])).

fof(f79,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f218,plain,
    ( spl7_3
    | spl7_7 ),
    inference(avatar_split_clause,[],[f87,f173,f157])).

fof(f87,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f202,plain,
    ( spl7_3
    | spl7_11 ),
    inference(avatar_split_clause,[],[f103,f189,f157])).

fof(f103,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f196,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f109,f193,f189,f185,f181,f177,f173,f169,f165,f161,f157,f153,f149])).

fof(f109,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f51])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.12/0.32  % Computer   : n021.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 20:19:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.45  % (25278)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.19/0.46  % (25290)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.19/0.47  % (25283)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.19/0.48  % (25272)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.19/0.49  % (25266)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.50  % (25268)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.19/0.50  % (25280)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.50  % (25287)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.19/0.50  % (25279)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.19/0.50  % (25270)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.19/0.50  % (25277)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.19/0.51  % (25274)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.19/0.51  % (25269)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.19/0.51  % (25267)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.19/0.51  % (25282)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.19/0.52  % (25281)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.19/0.52  % (25265)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.19/0.52  % (25289)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.19/0.52  % (25286)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.19/0.52  % (25288)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.19/0.52  % (25285)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.19/0.53  % (25273)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.19/0.54  % (25276)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.19/0.54  % (25284)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.19/0.54  % (25265)Refutation not found, incomplete strategy% (25265)------------------------------
% 0.19/0.54  % (25265)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (25265)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.54  
% 0.19/0.54  % (25265)Memory used [KB]: 10746
% 0.19/0.54  % (25265)Time elapsed: 0.152 s
% 0.19/0.54  % (25265)------------------------------
% 0.19/0.54  % (25265)------------------------------
% 1.69/0.56  % (25291)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.69/0.56  % (25271)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.82/0.59  % (25266)Refutation found. Thanks to Tanya!
% 1.82/0.59  % SZS status Theorem for theBenchmark
% 1.82/0.59  % SZS output start Proof for theBenchmark
% 1.82/0.59  fof(f2912,plain,(
% 1.82/0.59    $false),
% 1.82/0.59    inference(avatar_sat_refutation,[],[f196,f202,f218,f226,f687,f750,f764,f907,f914,f946,f985,f997,f1010,f1026,f1031,f1033,f1035,f1038,f2908])).
% 1.82/0.59  fof(f2908,plain,(
% 1.82/0.59    ~spl7_6 | ~spl7_7 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | spl7_47),
% 1.82/0.59    inference(avatar_contradiction_clause,[],[f2907])).
% 1.82/0.59  fof(f2907,plain,(
% 1.82/0.59    $false | (~spl7_6 | ~spl7_7 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | spl7_47)),
% 1.82/0.59    inference(subsumption_resolution,[],[f2906,f233])).
% 1.82/0.59  fof(f233,plain,(
% 1.82/0.59    l1_struct_0(sK5)),
% 1.82/0.59    inference(resolution,[],[f232,f111])).
% 1.82/0.59  fof(f111,plain,(
% 1.82/0.59    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 1.82/0.59    inference(cnf_transformation,[],[f23])).
% 1.82/0.59  fof(f23,plain,(
% 1.82/0.59    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.82/0.59    inference(ennf_transformation,[],[f10])).
% 1.82/0.59  fof(f10,axiom,(
% 1.82/0.59    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.82/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.82/0.59  fof(f232,plain,(
% 1.82/0.59    l1_pre_topc(sK5)),
% 1.82/0.59    inference(subsumption_resolution,[],[f231,f64])).
% 1.82/0.59  fof(f64,plain,(
% 1.82/0.59    l1_pre_topc(sK2)),
% 1.82/0.59    inference(cnf_transformation,[],[f51])).
% 1.82/0.59  fof(f51,plain,(
% 1.82/0.59    (((((~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)) & ((m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))) | (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(sK4,sK2,sK3) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4))) & r4_tsep_1(sK2,sK5,sK6) & sK2 = k1_tsep_1(sK2,sK5,sK6) & m1_pre_topc(sK6,sK2) & ~v2_struct_0(sK6)) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 1.82/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f45,f50,f49,f48,f47,f46])).
% 1.82/0.59  fof(f46,plain,(
% 1.82/0.59    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(sK2,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(sK2,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) | ~v5_pre_topc(X2,sK2,X1) | ~v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(sK2,X1,X2,X4)) & m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(sK2,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v5_pre_topc(X2,sK2,X1) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(sK2,X3,X4) & sK2 = k1_tsep_1(sK2,X3,X4) & m1_pre_topc(X4,sK2) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 1.82/0.59    introduced(choice_axiom,[])).
% 1.82/0.59  fof(f47,plain,(
% 1.82/0.59    ? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(sK2,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(sK2,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) | ~v5_pre_topc(X2,sK2,X1) | ~v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(sK2,X1,X2,X4)) & m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(sK2,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v5_pre_topc(X2,sK2,X1) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(sK2,X3,X4) & sK2 = k1_tsep_1(sK2,X3,X4) & m1_pre_topc(X4,sK2) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(sK2,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X4),X4,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,X2,X4)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X3),X3,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(X2,sK2,sK3) | ~v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(sK2,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X4),X4,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,X2,X4)) & m1_subset_1(k2_tmap_1(sK2,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X3),X3,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(X2,sK2,sK3) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X2))) & r4_tsep_1(sK2,X3,X4) & sK2 = k1_tsep_1(sK2,X3,X4) & m1_pre_topc(X4,sK2) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 1.82/0.59    introduced(choice_axiom,[])).
% 1.82/0.59  fof(f48,plain,(
% 1.82/0.59    ? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(sK2,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X4),X4,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,X2,X4)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X3),X3,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(X2,sK2,sK3) | ~v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(sK2,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X4),X4,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,X2,X4)) & m1_subset_1(k2_tmap_1(sK2,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X3),X3,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(X2,sK2,sK3) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X2))) & r4_tsep_1(sK2,X3,X4) & sK2 = k1_tsep_1(sK2,X3,X4) & m1_pre_topc(X4,sK2) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X3),X3,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X3),u1_struct_0(X3),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)) & ((m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4)) & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X3),X3,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X3),u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X3))) | (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(sK4,sK2,sK3) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4))) & r4_tsep_1(sK2,X3,X4) & sK2 = k1_tsep_1(sK2,X3,X4) & m1_pre_topc(X4,sK2) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4))),
% 1.82/0.59    introduced(choice_axiom,[])).
% 1.82/0.59  fof(f49,plain,(
% 1.82/0.59    ? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X3),X3,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X3),u1_struct_0(X3),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)) & ((m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4)) & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X3),X3,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X3),u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X3))) | (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(sK4,sK2,sK3) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4))) & r4_tsep_1(sK2,X3,X4) & sK2 = k1_tsep_1(sK2,X3,X4) & m1_pre_topc(X4,sK2) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) => (? [X4] : ((~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)) & ((m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4)) & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))) | (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(sK4,sK2,sK3) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4))) & r4_tsep_1(sK2,sK5,X4) & sK2 = k1_tsep_1(sK2,sK5,X4) & m1_pre_topc(X4,sK2) & ~v2_struct_0(X4)) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5))),
% 1.82/0.59    introduced(choice_axiom,[])).
% 1.82/0.59  fof(f50,plain,(
% 1.82/0.59    ? [X4] : ((~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)) & ((m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4)) & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))) | (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(sK4,sK2,sK3) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4))) & r4_tsep_1(sK2,sK5,X4) & sK2 = k1_tsep_1(sK2,sK5,X4) & m1_pre_topc(X4,sK2) & ~v2_struct_0(X4)) => ((~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)) & ((m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))) | (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(sK4,sK2,sK3) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4))) & r4_tsep_1(sK2,sK5,sK6) & sK2 = k1_tsep_1(sK2,sK5,sK6) & m1_pre_topc(sK6,sK2) & ~v2_struct_0(sK6))),
% 1.82/0.59    introduced(choice_axiom,[])).
% 1.82/0.59  fof(f45,plain,(
% 1.82/0.59    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.82/0.59    inference(flattening,[],[f44])).
% 1.82/0.59  fof(f44,plain,(
% 1.82/0.59    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.82/0.59    inference(nnf_transformation,[],[f21])).
% 1.82/0.59  fof(f21,plain,(
% 1.82/0.59    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <~> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.82/0.59    inference(flattening,[],[f20])).
% 1.82/0.59  fof(f20,plain,(
% 1.82/0.59    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <~> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))) & (r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0)) & (m1_pre_topc(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.82/0.59    inference(ennf_transformation,[],[f17])).
% 1.82/0.59  fof(f17,negated_conjecture,(
% 1.82/0.59    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))))))))),
% 1.82/0.59    inference(negated_conjecture,[],[f16])).
% 1.82/0.59  fof(f16,conjecture,(
% 1.82/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))))))))),
% 1.82/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_tmap_1)).
% 1.82/0.59  fof(f231,plain,(
% 1.82/0.59    l1_pre_topc(sK5) | ~l1_pre_topc(sK2)),
% 1.82/0.59    inference(resolution,[],[f72,f112])).
% 1.82/0.59  fof(f112,plain,(
% 1.82/0.59    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.82/0.59    inference(cnf_transformation,[],[f24])).
% 1.82/0.59  fof(f24,plain,(
% 1.82/0.59    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.82/0.59    inference(ennf_transformation,[],[f11])).
% 1.82/0.59  fof(f11,axiom,(
% 1.82/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.82/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.82/0.59  fof(f72,plain,(
% 1.82/0.59    m1_pre_topc(sK5,sK2)),
% 1.82/0.59    inference(cnf_transformation,[],[f51])).
% 1.82/0.59  fof(f2906,plain,(
% 1.82/0.59    ~l1_struct_0(sK5) | (~spl7_6 | ~spl7_7 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | spl7_47)),
% 1.82/0.59    inference(subsumption_resolution,[],[f2905,f526])).
% 1.82/0.59  fof(f526,plain,(
% 1.82/0.59    v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK5)),sK5,sK3) | ~spl7_7),
% 1.82/0.59    inference(backward_demodulation,[],[f174,f512])).
% 1.82/0.59  fof(f512,plain,(
% 1.82/0.59    k2_tmap_1(sK2,sK3,sK4,sK5) = k7_relat_1(sK4,u1_struct_0(sK5))),
% 1.82/0.59    inference(resolution,[],[f507,f72])).
% 1.82/0.59  fof(f507,plain,(
% 1.82/0.59    ( ! [X2] : (~m1_pre_topc(X2,sK2) | k2_tmap_1(sK2,sK3,sK4,X2) = k7_relat_1(sK4,u1_struct_0(X2))) )),
% 1.82/0.59    inference(forward_demodulation,[],[f270,f279])).
% 1.82/0.59  fof(f279,plain,(
% 1.82/0.59    ( ! [X5] : (k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X5) = k7_relat_1(sK4,X5)) )),
% 1.82/0.59    inference(subsumption_resolution,[],[f251,f68])).
% 1.82/0.59  fof(f68,plain,(
% 1.82/0.59    v1_funct_1(sK4)),
% 1.82/0.59    inference(cnf_transformation,[],[f51])).
% 1.82/0.59  fof(f251,plain,(
% 1.82/0.59    ( ! [X5] : (k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X5) = k7_relat_1(sK4,X5) | ~v1_funct_1(sK4)) )),
% 1.82/0.59    inference(resolution,[],[f70,f145])).
% 1.82/0.59  fof(f145,plain,(
% 1.82/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~v1_funct_1(X2)) )),
% 1.82/0.59    inference(cnf_transformation,[],[f40])).
% 1.82/0.59  fof(f40,plain,(
% 1.82/0.59    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.82/0.59    inference(flattening,[],[f39])).
% 1.82/0.59  fof(f39,plain,(
% 1.82/0.59    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.82/0.59    inference(ennf_transformation,[],[f9])).
% 1.82/0.59  fof(f9,axiom,(
% 1.82/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.82/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.82/0.59  fof(f70,plain,(
% 1.82/0.59    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 1.82/0.59    inference(cnf_transformation,[],[f51])).
% 1.82/0.59  fof(f270,plain,(
% 1.82/0.59    ( ! [X2] : (~m1_pre_topc(X2,sK2) | k2_tmap_1(sK2,sK3,sK4,X2) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X2))) )),
% 1.82/0.59    inference(subsumption_resolution,[],[f269,f62])).
% 1.82/0.59  fof(f62,plain,(
% 1.82/0.59    ~v2_struct_0(sK2)),
% 1.82/0.59    inference(cnf_transformation,[],[f51])).
% 1.82/0.59  fof(f269,plain,(
% 1.82/0.59    ( ! [X2] : (~m1_pre_topc(X2,sK2) | k2_tmap_1(sK2,sK3,sK4,X2) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X2)) | v2_struct_0(sK2)) )),
% 1.82/0.59    inference(subsumption_resolution,[],[f268,f63])).
% 1.82/0.59  fof(f63,plain,(
% 1.82/0.59    v2_pre_topc(sK2)),
% 1.82/0.59    inference(cnf_transformation,[],[f51])).
% 1.82/0.59  fof(f268,plain,(
% 1.82/0.59    ( ! [X2] : (~m1_pre_topc(X2,sK2) | k2_tmap_1(sK2,sK3,sK4,X2) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X2)) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.82/0.59    inference(subsumption_resolution,[],[f267,f64])).
% 1.82/0.59  fof(f267,plain,(
% 1.82/0.59    ( ! [X2] : (~m1_pre_topc(X2,sK2) | k2_tmap_1(sK2,sK3,sK4,X2) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X2)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.82/0.59    inference(subsumption_resolution,[],[f266,f65])).
% 1.82/0.59  fof(f65,plain,(
% 1.82/0.59    ~v2_struct_0(sK3)),
% 1.82/0.59    inference(cnf_transformation,[],[f51])).
% 1.82/0.59  fof(f266,plain,(
% 1.82/0.59    ( ! [X2] : (~m1_pre_topc(X2,sK2) | k2_tmap_1(sK2,sK3,sK4,X2) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X2)) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.82/0.59    inference(subsumption_resolution,[],[f265,f66])).
% 1.82/0.59  fof(f66,plain,(
% 1.82/0.59    v2_pre_topc(sK3)),
% 1.82/0.59    inference(cnf_transformation,[],[f51])).
% 1.82/0.59  fof(f265,plain,(
% 1.82/0.59    ( ! [X2] : (~m1_pre_topc(X2,sK2) | k2_tmap_1(sK2,sK3,sK4,X2) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X2)) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.82/0.59    inference(subsumption_resolution,[],[f264,f67])).
% 1.82/0.59  fof(f67,plain,(
% 1.82/0.59    l1_pre_topc(sK3)),
% 1.82/0.59    inference(cnf_transformation,[],[f51])).
% 1.82/0.59  fof(f264,plain,(
% 1.82/0.59    ( ! [X2] : (~m1_pre_topc(X2,sK2) | k2_tmap_1(sK2,sK3,sK4,X2) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X2)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.82/0.59    inference(subsumption_resolution,[],[f263,f68])).
% 1.82/0.59  fof(f263,plain,(
% 1.82/0.59    ( ! [X2] : (~m1_pre_topc(X2,sK2) | k2_tmap_1(sK2,sK3,sK4,X2) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X2)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.82/0.59    inference(subsumption_resolution,[],[f249,f69])).
% 1.82/0.59  fof(f69,plain,(
% 1.82/0.59    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))),
% 1.82/0.59    inference(cnf_transformation,[],[f51])).
% 1.82/0.59  fof(f249,plain,(
% 1.82/0.59    ( ! [X2] : (~m1_pre_topc(X2,sK2) | k2_tmap_1(sK2,sK3,sK4,X2) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X2)) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.82/0.59    inference(resolution,[],[f70,f128])).
% 1.82/0.59  fof(f128,plain,(
% 1.82/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.82/0.59    inference(cnf_transformation,[],[f28])).
% 1.82/0.59  fof(f28,plain,(
% 1.82/0.59    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.82/0.59    inference(flattening,[],[f27])).
% 1.82/0.59  fof(f27,plain,(
% 1.82/0.59    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.82/0.59    inference(ennf_transformation,[],[f12])).
% 1.82/0.59  fof(f12,axiom,(
% 1.82/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 1.82/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).
% 1.82/0.59  fof(f174,plain,(
% 1.82/0.59    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~spl7_7),
% 1.82/0.59    inference(avatar_component_clause,[],[f173])).
% 1.82/0.59  fof(f173,plain,(
% 1.82/0.59    spl7_7 <=> v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)),
% 1.82/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.82/0.59  fof(f2905,plain,(
% 1.82/0.59    ~v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK5)),sK5,sK3) | ~l1_struct_0(sK5) | (~spl7_6 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | spl7_47)),
% 1.82/0.59    inference(subsumption_resolution,[],[f2904,f900])).
% 1.82/0.59  fof(f900,plain,(
% 1.82/0.59    ~sP0(sK3,sK6,sK4,sK2,sK5) | spl7_47),
% 1.82/0.59    inference(avatar_component_clause,[],[f899])).
% 1.82/0.59  fof(f899,plain,(
% 1.82/0.59    spl7_47 <=> sP0(sK3,sK6,sK4,sK2,sK5)),
% 1.82/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).
% 1.82/0.59  fof(f2904,plain,(
% 1.82/0.59    sP0(sK3,sK6,sK4,sK2,sK5) | ~v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK5)),sK5,sK3) | ~l1_struct_0(sK5) | (~spl7_6 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12)),
% 1.82/0.59    inference(subsumption_resolution,[],[f2896,f525])).
% 1.82/0.59  fof(f525,plain,(
% 1.82/0.59    v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK5),u1_struct_0(sK3)) | ~spl7_6),
% 1.82/0.59    inference(backward_demodulation,[],[f170,f512])).
% 1.82/0.59  fof(f170,plain,(
% 1.82/0.59    v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~spl7_6),
% 1.82/0.59    inference(avatar_component_clause,[],[f169])).
% 1.82/0.59  fof(f169,plain,(
% 1.82/0.59    spl7_6 <=> v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))),
% 1.82/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.82/0.59  fof(f2896,plain,(
% 1.82/0.59    ~v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK5),u1_struct_0(sK3)) | sP0(sK3,sK6,sK4,sK2,sK5) | ~v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK5)),sK5,sK3) | ~l1_struct_0(sK5) | (~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12)),
% 1.82/0.59    inference(superposition,[],[f1507,f512])).
% 1.82/0.59  fof(f1507,plain,(
% 1.82/0.59    ( ! [X2] : (~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X2),u1_struct_0(X2),u1_struct_0(sK3)) | sP0(sK3,sK6,sK4,sK2,X2) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X2),X2,sK3) | ~l1_struct_0(X2)) ) | (~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12)),
% 1.82/0.59    inference(subsumption_resolution,[],[f1506,f258])).
% 1.82/0.59  fof(f258,plain,(
% 1.82/0.59    ( ! [X0] : (~l1_struct_0(X0) | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0))) )),
% 1.82/0.59    inference(subsumption_resolution,[],[f257,f229])).
% 1.82/0.59  fof(f229,plain,(
% 1.82/0.59    l1_struct_0(sK2)),
% 1.82/0.59    inference(resolution,[],[f64,f111])).
% 1.82/0.59  fof(f257,plain,(
% 1.82/0.59    ( ! [X0] : (~l1_struct_0(X0) | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) | ~l1_struct_0(sK2)) )),
% 1.82/0.59    inference(subsumption_resolution,[],[f256,f230])).
% 1.82/0.59  fof(f230,plain,(
% 1.82/0.59    l1_struct_0(sK3)),
% 1.82/0.59    inference(resolution,[],[f67,f111])).
% 1.82/0.59  fof(f256,plain,(
% 1.82/0.59    ( ! [X0] : (~l1_struct_0(X0) | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) | ~l1_struct_0(sK3) | ~l1_struct_0(sK2)) )),
% 1.82/0.59    inference(subsumption_resolution,[],[f255,f68])).
% 1.82/0.59  fof(f255,plain,(
% 1.82/0.59    ( ! [X0] : (~l1_struct_0(X0) | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) | ~v1_funct_1(sK4) | ~l1_struct_0(sK3) | ~l1_struct_0(sK2)) )),
% 1.82/0.59    inference(subsumption_resolution,[],[f247,f69])).
% 1.82/0.59  fof(f247,plain,(
% 1.82/0.59    ( ! [X0] : (~l1_struct_0(X0) | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~l1_struct_0(sK3) | ~l1_struct_0(sK2)) )),
% 1.82/0.59    inference(resolution,[],[f70,f142])).
% 1.82/0.59  fof(f142,plain,(
% 1.82/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_struct_0(X3) | v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 1.82/0.59    inference(cnf_transformation,[],[f38])).
% 1.82/0.59  fof(f38,plain,(
% 1.82/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 1.82/0.59    inference(flattening,[],[f37])).
% 1.82/0.59  fof(f37,plain,(
% 1.82/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 1.82/0.59    inference(ennf_transformation,[],[f14])).
% 1.82/0.59  fof(f14,axiom,(
% 1.82/0.59    ! [X0,X1,X2,X3] : ((l1_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_struct_0(X1) & l1_struct_0(X0)) => (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 1.82/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tmap_1)).
% 1.82/0.59  fof(f1506,plain,(
% 1.82/0.59    ( ! [X2] : (~l1_struct_0(X2) | sP0(sK3,sK6,sK4,sK2,X2) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X2),X2,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X2),u1_struct_0(X2),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X2))) ) | (~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12)),
% 1.82/0.59    inference(subsumption_resolution,[],[f1505,f612])).
% 1.82/0.59  fof(f612,plain,(
% 1.82/0.59    v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK6))) | ~spl7_9),
% 1.82/0.59    inference(backward_demodulation,[],[f182,f513])).
% 1.82/0.59  fof(f513,plain,(
% 1.82/0.59    k2_tmap_1(sK2,sK3,sK4,sK6) = k7_relat_1(sK4,u1_struct_0(sK6))),
% 1.82/0.59    inference(resolution,[],[f507,f74])).
% 1.82/0.59  fof(f74,plain,(
% 1.82/0.59    m1_pre_topc(sK6,sK2)),
% 1.82/0.59    inference(cnf_transformation,[],[f51])).
% 1.82/0.59  fof(f182,plain,(
% 1.82/0.59    v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | ~spl7_9),
% 1.82/0.59    inference(avatar_component_clause,[],[f181])).
% 1.82/0.59  fof(f181,plain,(
% 1.82/0.59    spl7_9 <=> v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))),
% 1.82/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 1.82/0.59  fof(f1505,plain,(
% 1.82/0.59    ( ! [X2] : (~l1_struct_0(X2) | ~v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK6))) | sP0(sK3,sK6,sK4,sK2,X2) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X2),X2,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X2),u1_struct_0(X2),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X2))) ) | (~spl7_10 | ~spl7_11 | ~spl7_12)),
% 1.82/0.59    inference(subsumption_resolution,[],[f1504,f613])).
% 1.82/0.60  fof(f613,plain,(
% 1.82/0.60    v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3)) | ~spl7_10),
% 1.82/0.60    inference(backward_demodulation,[],[f186,f513])).
% 1.82/0.60  fof(f186,plain,(
% 1.82/0.60    v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | ~spl7_10),
% 1.82/0.60    inference(avatar_component_clause,[],[f185])).
% 1.82/0.60  fof(f185,plain,(
% 1.82/0.60    spl7_10 <=> v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))),
% 1.82/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 1.82/0.60  fof(f1504,plain,(
% 1.82/0.60    ( ! [X2] : (~l1_struct_0(X2) | ~v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK6))) | sP0(sK3,sK6,sK4,sK2,X2) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X2),X2,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X2),u1_struct_0(X2),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X2))) ) | (~spl7_11 | ~spl7_12)),
% 1.82/0.60    inference(subsumption_resolution,[],[f1503,f614])).
% 1.82/0.60  fof(f614,plain,(
% 1.82/0.60    v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3) | ~spl7_11),
% 1.82/0.60    inference(backward_demodulation,[],[f190,f513])).
% 1.82/0.60  fof(f190,plain,(
% 1.82/0.60    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | ~spl7_11),
% 1.82/0.60    inference(avatar_component_clause,[],[f189])).
% 1.82/0.60  fof(f189,plain,(
% 1.82/0.60    spl7_11 <=> v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)),
% 1.82/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 1.82/0.60  fof(f1503,plain,(
% 1.82/0.60    ( ! [X2] : (~l1_struct_0(X2) | ~v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3) | ~v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK6))) | sP0(sK3,sK6,sK4,sK2,X2) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X2),X2,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X2),u1_struct_0(X2),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X2))) ) | ~spl7_12),
% 1.82/0.60    inference(subsumption_resolution,[],[f1495,f615])).
% 1.82/0.60  fof(f615,plain,(
% 1.82/0.60    m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | ~spl7_12),
% 1.82/0.60    inference(backward_demodulation,[],[f194,f513])).
% 1.82/0.60  fof(f194,plain,(
% 1.82/0.60    m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | ~spl7_12),
% 1.82/0.60    inference(avatar_component_clause,[],[f193])).
% 1.82/0.60  fof(f193,plain,(
% 1.82/0.60    spl7_12 <=> m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))),
% 1.82/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 1.82/0.60  fof(f1495,plain,(
% 1.82/0.60    ( ! [X2] : (~m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | ~l1_struct_0(X2) | ~v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3) | ~v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK6))) | sP0(sK3,sK6,sK4,sK2,X2) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X2),X2,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X2),u1_struct_0(X2),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X2))) )),
% 1.82/0.60    inference(superposition,[],[f477,f513])).
% 1.82/0.60  fof(f477,plain,(
% 1.82/0.60    ( ! [X2,X3] : (~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) | ~l1_struct_0(X2) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X3),X3,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X3),u1_struct_0(X3),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X3)) | sP0(sK3,X3,sK4,sK2,X2) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X2),X2,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X2),u1_struct_0(X2),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X2))) )),
% 1.82/0.60    inference(resolution,[],[f262,f126])).
% 1.82/0.60  fof(f126,plain,(
% 1.82/0.60    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) | ~m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) | sP0(X0,X1,X2,X3,X4) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X4))) )),
% 1.82/0.60    inference(cnf_transformation,[],[f57])).
% 1.82/0.60  fof(f57,plain,(
% 1.82/0.60    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) | ~m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X4))) & ((m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) & v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) & m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) & v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) & v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) & v1_funct_1(k2_tmap_1(X3,X0,X2,X4))) | ~sP0(X0,X1,X2,X3,X4)))),
% 1.82/0.60    inference(rectify,[],[f56])).
% 1.82/0.60  fof(f56,plain,(
% 1.82/0.60    ! [X1,X3,X4,X0,X2] : ((sP0(X1,X3,X4,X0,X2) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X2))) & ((m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2))) | ~sP0(X1,X3,X4,X0,X2)))),
% 1.82/0.60    inference(flattening,[],[f55])).
% 1.82/0.60  fof(f55,plain,(
% 1.82/0.60    ! [X1,X3,X4,X0,X2] : ((sP0(X1,X3,X4,X0,X2) | (~m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X2)))) & ((m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2))) | ~sP0(X1,X3,X4,X0,X2)))),
% 1.82/0.60    inference(nnf_transformation,[],[f41])).
% 1.82/0.60  fof(f41,plain,(
% 1.82/0.60    ! [X1,X3,X4,X0,X2] : (sP0(X1,X3,X4,X0,X2) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2))))),
% 1.82/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.82/0.60  fof(f262,plain,(
% 1.82/0.60    ( ! [X1] : (m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) | ~l1_struct_0(X1)) )),
% 1.82/0.60    inference(subsumption_resolution,[],[f261,f229])).
% 1.82/0.60  fof(f261,plain,(
% 1.82/0.60    ( ! [X1] : (~l1_struct_0(X1) | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) | ~l1_struct_0(sK2)) )),
% 1.82/0.60    inference(subsumption_resolution,[],[f260,f230])).
% 1.82/0.60  fof(f260,plain,(
% 1.82/0.60    ( ! [X1] : (~l1_struct_0(X1) | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) | ~l1_struct_0(sK3) | ~l1_struct_0(sK2)) )),
% 1.82/0.60    inference(subsumption_resolution,[],[f259,f68])).
% 1.82/0.60  fof(f259,plain,(
% 1.82/0.60    ( ! [X1] : (~l1_struct_0(X1) | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) | ~v1_funct_1(sK4) | ~l1_struct_0(sK3) | ~l1_struct_0(sK2)) )),
% 1.82/0.60    inference(subsumption_resolution,[],[f248,f69])).
% 1.82/0.60  fof(f248,plain,(
% 1.82/0.60    ( ! [X1] : (~l1_struct_0(X1) | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~l1_struct_0(sK3) | ~l1_struct_0(sK2)) )),
% 1.82/0.60    inference(resolution,[],[f70,f144])).
% 1.82/0.60  fof(f144,plain,(
% 1.82/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_struct_0(X3) | m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f38])).
% 1.82/0.60  fof(f1038,plain,(
% 1.82/0.60    spl7_3 | ~spl7_46 | ~spl7_47),
% 1.82/0.60    inference(avatar_contradiction_clause,[],[f1037])).
% 1.82/0.60  fof(f1037,plain,(
% 1.82/0.60    $false | (spl7_3 | ~spl7_46 | ~spl7_47)),
% 1.82/0.60    inference(subsumption_resolution,[],[f1036,f159])).
% 1.82/0.60  fof(f159,plain,(
% 1.82/0.60    ~v5_pre_topc(sK4,sK2,sK3) | spl7_3),
% 1.82/0.60    inference(avatar_component_clause,[],[f157])).
% 1.82/0.60  fof(f157,plain,(
% 1.82/0.60    spl7_3 <=> v5_pre_topc(sK4,sK2,sK3)),
% 1.82/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.82/0.60  fof(f1036,plain,(
% 1.82/0.60    v5_pre_topc(sK4,sK2,sK3) | (~spl7_46 | ~spl7_47)),
% 1.82/0.60    inference(subsumption_resolution,[],[f924,f901])).
% 1.82/0.60  fof(f901,plain,(
% 1.82/0.60    sP0(sK3,sK6,sK4,sK2,sK5) | ~spl7_47),
% 1.82/0.60    inference(avatar_component_clause,[],[f899])).
% 1.82/0.60  fof(f924,plain,(
% 1.82/0.60    v5_pre_topc(sK4,sK2,sK3) | ~sP0(sK3,sK6,sK4,sK2,sK5) | ~spl7_46),
% 1.82/0.60    inference(forward_demodulation,[],[f923,f516])).
% 1.82/0.60  fof(f516,plain,(
% 1.82/0.60    sK4 = k2_tmap_1(sK2,sK3,sK4,sK2)),
% 1.82/0.60    inference(forward_demodulation,[],[f511,f287])).
% 1.82/0.60  fof(f287,plain,(
% 1.82/0.60    sK4 = k7_relat_1(sK4,u1_struct_0(sK2))),
% 1.82/0.60    inference(subsumption_resolution,[],[f284,f280])).
% 1.82/0.60  fof(f280,plain,(
% 1.82/0.60    v1_relat_1(sK4)),
% 1.82/0.60    inference(subsumption_resolution,[],[f254,f129])).
% 1.82/0.60  fof(f129,plain,(
% 1.82/0.60    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.82/0.60    inference(cnf_transformation,[],[f6])).
% 1.82/0.60  fof(f6,axiom,(
% 1.82/0.60    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.82/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.82/0.60  fof(f254,plain,(
% 1.82/0.60    v1_relat_1(sK4) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))),
% 1.82/0.60    inference(resolution,[],[f70,f110])).
% 1.82/0.60  fof(f110,plain,(
% 1.82/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f22])).
% 1.82/0.60  fof(f22,plain,(
% 1.82/0.60    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.82/0.60    inference(ennf_transformation,[],[f4])).
% 1.82/0.60  fof(f4,axiom,(
% 1.82/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.82/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.82/0.60  fof(f284,plain,(
% 1.82/0.60    sK4 = k7_relat_1(sK4,u1_struct_0(sK2)) | ~v1_relat_1(sK4)),
% 1.82/0.60    inference(resolution,[],[f282,f130])).
% 1.82/0.60  fof(f130,plain,(
% 1.82/0.60    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f30])).
% 1.82/0.60  fof(f30,plain,(
% 1.82/0.60    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.82/0.60    inference(flattening,[],[f29])).
% 1.82/0.60  fof(f29,plain,(
% 1.82/0.60    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.82/0.60    inference(ennf_transformation,[],[f7])).
% 1.82/0.60  fof(f7,axiom,(
% 1.82/0.60    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 1.82/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).
% 1.82/0.60  fof(f282,plain,(
% 1.82/0.60    r1_tarski(k1_relat_1(sK4),u1_struct_0(sK2))),
% 1.82/0.60    inference(subsumption_resolution,[],[f281,f280])).
% 1.82/0.60  fof(f281,plain,(
% 1.82/0.60    r1_tarski(k1_relat_1(sK4),u1_struct_0(sK2)) | ~v1_relat_1(sK4)),
% 1.82/0.60    inference(resolution,[],[f252,f131])).
% 1.82/0.60  fof(f131,plain,(
% 1.82/0.60    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f58])).
% 1.82/0.60  fof(f58,plain,(
% 1.82/0.60    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.82/0.60    inference(nnf_transformation,[],[f31])).
% 1.82/0.60  fof(f31,plain,(
% 1.82/0.60    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.82/0.60    inference(ennf_transformation,[],[f5])).
% 1.82/0.60  fof(f5,axiom,(
% 1.82/0.60    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.82/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 1.82/0.60  fof(f252,plain,(
% 1.82/0.60    v4_relat_1(sK4,u1_struct_0(sK2))),
% 1.82/0.60    inference(resolution,[],[f70,f138])).
% 1.82/0.60  fof(f138,plain,(
% 1.82/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f32])).
% 1.82/0.60  fof(f32,plain,(
% 1.82/0.60    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.82/0.60    inference(ennf_transformation,[],[f19])).
% 1.82/0.60  fof(f19,plain,(
% 1.82/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.82/0.60    inference(pure_predicate_removal,[],[f8])).
% 1.82/0.60  fof(f8,axiom,(
% 1.82/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.82/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.82/0.60  fof(f511,plain,(
% 1.82/0.60    k7_relat_1(sK4,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK3,sK4,sK2)),
% 1.82/0.60    inference(resolution,[],[f507,f245])).
% 1.82/0.60  fof(f245,plain,(
% 1.82/0.60    m1_pre_topc(sK2,sK2)),
% 1.82/0.60    inference(subsumption_resolution,[],[f244,f62])).
% 1.82/0.60  fof(f244,plain,(
% 1.82/0.60    m1_pre_topc(sK2,sK2) | v2_struct_0(sK2)),
% 1.82/0.60    inference(subsumption_resolution,[],[f243,f64])).
% 1.82/0.60  fof(f243,plain,(
% 1.82/0.60    m1_pre_topc(sK2,sK2) | ~l1_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.82/0.60    inference(subsumption_resolution,[],[f242,f71])).
% 1.82/0.60  fof(f71,plain,(
% 1.82/0.60    ~v2_struct_0(sK5)),
% 1.82/0.60    inference(cnf_transformation,[],[f51])).
% 1.82/0.60  fof(f242,plain,(
% 1.82/0.60    m1_pre_topc(sK2,sK2) | v2_struct_0(sK5) | ~l1_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.82/0.60    inference(subsumption_resolution,[],[f241,f72])).
% 1.82/0.60  fof(f241,plain,(
% 1.82/0.60    m1_pre_topc(sK2,sK2) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~l1_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.82/0.60    inference(subsumption_resolution,[],[f240,f73])).
% 1.82/0.60  fof(f73,plain,(
% 1.82/0.60    ~v2_struct_0(sK6)),
% 1.82/0.60    inference(cnf_transformation,[],[f51])).
% 1.82/0.60  fof(f240,plain,(
% 1.82/0.60    m1_pre_topc(sK2,sK2) | v2_struct_0(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~l1_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.82/0.60    inference(subsumption_resolution,[],[f238,f74])).
% 1.82/0.60  fof(f238,plain,(
% 1.82/0.60    m1_pre_topc(sK2,sK2) | ~m1_pre_topc(sK6,sK2) | v2_struct_0(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~l1_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.82/0.60    inference(superposition,[],[f140,f75])).
% 1.82/0.60  fof(f75,plain,(
% 1.82/0.60    sK2 = k1_tsep_1(sK2,sK5,sK6)),
% 1.82/0.60    inference(cnf_transformation,[],[f51])).
% 1.82/0.60  fof(f140,plain,(
% 1.82/0.60    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f34])).
% 1.82/0.60  fof(f34,plain,(
% 1.82/0.60    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.82/0.60    inference(flattening,[],[f33])).
% 1.82/0.60  fof(f33,plain,(
% 1.82/0.60    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.82/0.60    inference(ennf_transformation,[],[f18])).
% 1.82/0.60  fof(f18,plain,(
% 1.82/0.60    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 1.82/0.60    inference(pure_predicate_removal,[],[f13])).
% 1.82/0.60  fof(f13,axiom,(
% 1.82/0.60    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 1.82/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).
% 1.82/0.60  fof(f923,plain,(
% 1.82/0.60    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) | ~sP0(sK3,sK6,sK4,sK2,sK5) | ~spl7_46),
% 1.82/0.60    inference(forward_demodulation,[],[f917,f75])).
% 1.82/0.60  fof(f917,plain,(
% 1.82/0.60    ~sP0(sK3,sK6,sK4,sK2,sK5) | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) | ~spl7_46),
% 1.82/0.60    inference(resolution,[],[f896,f116])).
% 1.82/0.60  fof(f116,plain,(
% 1.82/0.60    ( ! [X4,X2,X0,X3,X1] : (~sP1(X0,X1,X2,X3,X4) | ~sP0(X4,X3,X2,X1,X0) | v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f54])).
% 1.82/0.60  fof(f54,plain,(
% 1.82/0.60    ! [X0,X1,X2,X3,X4] : ((((m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) & v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) & v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)) & v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)))) | ~sP0(X4,X3,X2,X1,X0)) & (sP0(X4,X3,X2,X1,X0) | ~m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) | ~v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) | ~v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)) | ~v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))))) | ~sP1(X0,X1,X2,X3,X4))),
% 1.82/0.60    inference(rectify,[],[f53])).
% 1.82/0.60  fof(f53,plain,(
% 1.82/0.60    ! [X2,X0,X4,X3,X1] : ((((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) | ~sP0(X1,X3,X4,X0,X2)) & (sP0(X1,X3,X4,X0,X2) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))))) | ~sP1(X2,X0,X4,X3,X1))),
% 1.82/0.60    inference(flattening,[],[f52])).
% 1.82/0.60  fof(f52,plain,(
% 1.82/0.60    ! [X2,X0,X4,X3,X1] : ((((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) | ~sP0(X1,X3,X4,X0,X2)) & (sP0(X1,X3,X4,X0,X2) | (~m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))))) | ~sP1(X2,X0,X4,X3,X1))),
% 1.82/0.60    inference(nnf_transformation,[],[f42])).
% 1.82/0.60  fof(f42,plain,(
% 1.82/0.60    ! [X2,X0,X4,X3,X1] : (((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> sP0(X1,X3,X4,X0,X2)) | ~sP1(X2,X0,X4,X3,X1))),
% 1.82/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.82/0.60  fof(f896,plain,(
% 1.82/0.60    sP1(sK5,sK2,sK4,sK6,sK3) | ~spl7_46),
% 1.82/0.60    inference(avatar_component_clause,[],[f895])).
% 1.82/0.60  fof(f895,plain,(
% 1.82/0.60    spl7_46 <=> sP1(sK5,sK2,sK4,sK6,sK3)),
% 1.82/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).
% 1.82/0.60  fof(f1035,plain,(
% 1.82/0.60    spl7_4),
% 1.82/0.60    inference(avatar_contradiction_clause,[],[f1034])).
% 1.82/0.60  fof(f1034,plain,(
% 1.82/0.60    $false | spl7_4),
% 1.82/0.60    inference(subsumption_resolution,[],[f163,f70])).
% 1.82/0.60  fof(f163,plain,(
% 1.82/0.60    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | spl7_4),
% 1.82/0.60    inference(avatar_component_clause,[],[f161])).
% 1.82/0.60  fof(f161,plain,(
% 1.82/0.60    spl7_4 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 1.82/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.82/0.60  fof(f1033,plain,(
% 1.82/0.60    spl7_2),
% 1.82/0.60    inference(avatar_contradiction_clause,[],[f1032])).
% 1.82/0.60  fof(f1032,plain,(
% 1.82/0.60    $false | spl7_2),
% 1.82/0.60    inference(subsumption_resolution,[],[f155,f69])).
% 1.82/0.60  fof(f155,plain,(
% 1.82/0.60    ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | spl7_2),
% 1.82/0.60    inference(avatar_component_clause,[],[f153])).
% 1.82/0.60  fof(f153,plain,(
% 1.82/0.60    spl7_2 <=> v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))),
% 1.82/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.82/0.60  fof(f1031,plain,(
% 1.82/0.60    spl7_1),
% 1.82/0.60    inference(avatar_contradiction_clause,[],[f1030])).
% 1.82/0.60  fof(f1030,plain,(
% 1.82/0.60    $false | spl7_1),
% 1.82/0.60    inference(subsumption_resolution,[],[f151,f68])).
% 1.82/0.60  fof(f151,plain,(
% 1.82/0.60    ~v1_funct_1(sK4) | spl7_1),
% 1.82/0.60    inference(avatar_component_clause,[],[f149])).
% 1.82/0.60  fof(f149,plain,(
% 1.82/0.60    spl7_1 <=> v1_funct_1(sK4)),
% 1.82/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.82/0.60  fof(f1026,plain,(
% 1.82/0.60    spl7_7 | ~spl7_47),
% 1.82/0.60    inference(avatar_contradiction_clause,[],[f1025])).
% 1.82/0.60  fof(f1025,plain,(
% 1.82/0.60    $false | (spl7_7 | ~spl7_47)),
% 1.82/0.60    inference(subsumption_resolution,[],[f937,f1023])).
% 1.82/0.60  fof(f1023,plain,(
% 1.82/0.60    ~v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK5)),sK5,sK3) | spl7_7),
% 1.82/0.60    inference(forward_demodulation,[],[f175,f512])).
% 1.82/0.60  fof(f175,plain,(
% 1.82/0.60    ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | spl7_7),
% 1.82/0.60    inference(avatar_component_clause,[],[f173])).
% 1.82/0.60  fof(f937,plain,(
% 1.82/0.60    v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK5)),sK5,sK3) | ~spl7_47),
% 1.82/0.60    inference(forward_demodulation,[],[f929,f512])).
% 1.82/0.60  fof(f929,plain,(
% 1.82/0.60    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~spl7_47),
% 1.82/0.60    inference(resolution,[],[f901,f120])).
% 1.82/0.60  fof(f120,plain,(
% 1.82/0.60    ( ! [X4,X2,X0,X3,X1] : (~sP0(X0,X1,X2,X3,X4) | v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f57])).
% 1.82/0.60  fof(f1010,plain,(
% 1.82/0.60    spl7_6),
% 1.82/0.60    inference(avatar_contradiction_clause,[],[f1009])).
% 1.82/0.60  fof(f1009,plain,(
% 1.82/0.60    $false | spl7_6),
% 1.82/0.60    inference(subsumption_resolution,[],[f550,f999])).
% 1.82/0.60  fof(f999,plain,(
% 1.82/0.60    ~v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK5),u1_struct_0(sK3)) | spl7_6),
% 1.82/0.60    inference(forward_demodulation,[],[f171,f512])).
% 1.82/0.60  fof(f171,plain,(
% 1.82/0.60    ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | spl7_6),
% 1.82/0.60    inference(avatar_component_clause,[],[f169])).
% 1.82/0.60  fof(f550,plain,(
% 1.82/0.60    v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK5),u1_struct_0(sK3))),
% 1.82/0.60    inference(subsumption_resolution,[],[f549,f229])).
% 1.82/0.60  fof(f549,plain,(
% 1.82/0.60    v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK5),u1_struct_0(sK3)) | ~l1_struct_0(sK2)),
% 1.82/0.60    inference(subsumption_resolution,[],[f548,f230])).
% 1.82/0.60  fof(f548,plain,(
% 1.82/0.60    v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK5),u1_struct_0(sK3)) | ~l1_struct_0(sK3) | ~l1_struct_0(sK2)),
% 1.82/0.60    inference(subsumption_resolution,[],[f547,f68])).
% 1.82/0.60  fof(f547,plain,(
% 1.82/0.60    v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~l1_struct_0(sK3) | ~l1_struct_0(sK2)),
% 1.82/0.60    inference(subsumption_resolution,[],[f546,f69])).
% 1.82/0.60  fof(f546,plain,(
% 1.82/0.60    v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~l1_struct_0(sK3) | ~l1_struct_0(sK2)),
% 1.82/0.60    inference(subsumption_resolution,[],[f545,f70])).
% 1.82/0.60  fof(f545,plain,(
% 1.82/0.60    v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK5),u1_struct_0(sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~l1_struct_0(sK3) | ~l1_struct_0(sK2)),
% 1.82/0.60    inference(subsumption_resolution,[],[f541,f233])).
% 1.82/0.60  fof(f541,plain,(
% 1.82/0.60    v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK5),u1_struct_0(sK3)) | ~l1_struct_0(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~l1_struct_0(sK3) | ~l1_struct_0(sK2)),
% 1.82/0.60    inference(superposition,[],[f143,f512])).
% 1.82/0.60  fof(f143,plain,(
% 1.82/0.60    ( ! [X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f38])).
% 1.82/0.60  fof(f997,plain,(
% 1.82/0.60    spl7_8),
% 1.82/0.60    inference(avatar_contradiction_clause,[],[f996])).
% 1.82/0.60  fof(f996,plain,(
% 1.82/0.60    $false | spl7_8),
% 1.82/0.60    inference(subsumption_resolution,[],[f980,f986])).
% 1.82/0.60  fof(f986,plain,(
% 1.82/0.60    ~r1_tarski(k7_relat_1(sK4,u1_struct_0(sK5)),k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))) | spl7_8),
% 1.82/0.60    inference(resolution,[],[f983,f137])).
% 1.82/0.60  fof(f137,plain,(
% 1.82/0.60    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f61])).
% 1.82/0.60  fof(f61,plain,(
% 1.82/0.60    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.82/0.60    inference(nnf_transformation,[],[f3])).
% 1.82/0.60  fof(f3,axiom,(
% 1.82/0.60    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.82/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.82/0.60  fof(f983,plain,(
% 1.82/0.60    ~m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | spl7_8),
% 1.82/0.60    inference(forward_demodulation,[],[f179,f512])).
% 1.82/0.60  fof(f179,plain,(
% 1.82/0.60    ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | spl7_8),
% 1.82/0.60    inference(avatar_component_clause,[],[f177])).
% 1.82/0.60  fof(f177,plain,(
% 1.82/0.60    spl7_8 <=> m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))),
% 1.82/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 1.82/0.60  fof(f980,plain,(
% 1.82/0.60    r1_tarski(k7_relat_1(sK4,u1_struct_0(sK5)),k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))),
% 1.82/0.60    inference(subsumption_resolution,[],[f826,f233])).
% 1.82/0.60  fof(f826,plain,(
% 1.82/0.60    r1_tarski(k7_relat_1(sK4,u1_struct_0(sK5)),k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))) | ~l1_struct_0(sK5)),
% 1.82/0.60    inference(superposition,[],[f484,f512])).
% 1.82/0.60  fof(f484,plain,(
% 1.82/0.60    ( ! [X16] : (r1_tarski(k2_tmap_1(sK2,sK3,sK4,X16),k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(sK3))) | ~l1_struct_0(X16)) )),
% 1.82/0.60    inference(resolution,[],[f262,f136])).
% 1.82/0.60  fof(f136,plain,(
% 1.82/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f61])).
% 1.82/0.60  fof(f985,plain,(
% 1.82/0.60    spl7_5 | ~spl7_47),
% 1.82/0.60    inference(avatar_contradiction_clause,[],[f984])).
% 1.82/0.60  fof(f984,plain,(
% 1.82/0.60    $false | (spl7_5 | ~spl7_47)),
% 1.82/0.60    inference(subsumption_resolution,[],[f935,f979])).
% 1.82/0.60  fof(f979,plain,(
% 1.82/0.60    ~v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK5))) | spl7_5),
% 1.82/0.60    inference(forward_demodulation,[],[f167,f512])).
% 1.82/0.60  fof(f167,plain,(
% 1.82/0.60    ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | spl7_5),
% 1.82/0.60    inference(avatar_component_clause,[],[f165])).
% 1.82/0.60  fof(f165,plain,(
% 1.82/0.60    spl7_5 <=> v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))),
% 1.82/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.82/0.60  fof(f935,plain,(
% 1.82/0.60    v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK5))) | ~spl7_47),
% 1.82/0.60    inference(forward_demodulation,[],[f927,f512])).
% 1.82/0.60  fof(f927,plain,(
% 1.82/0.60    v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | ~spl7_47),
% 1.82/0.60    inference(resolution,[],[f901,f118])).
% 1.82/0.60  fof(f118,plain,(
% 1.82/0.60    ( ! [X4,X2,X0,X3,X1] : (~sP0(X0,X1,X2,X3,X4) | v1_funct_1(k2_tmap_1(X3,X0,X2,X4))) )),
% 1.82/0.60    inference(cnf_transformation,[],[f57])).
% 1.82/0.60  fof(f946,plain,(
% 1.82/0.60    spl7_11 | ~spl7_47),
% 1.82/0.60    inference(avatar_contradiction_clause,[],[f945])).
% 1.82/0.60  fof(f945,plain,(
% 1.82/0.60    $false | (spl7_11 | ~spl7_47)),
% 1.82/0.60    inference(subsumption_resolution,[],[f941,f777])).
% 1.82/0.60  fof(f777,plain,(
% 1.82/0.60    ~v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3) | spl7_11),
% 1.82/0.60    inference(forward_demodulation,[],[f191,f513])).
% 1.82/0.60  fof(f191,plain,(
% 1.82/0.60    ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | spl7_11),
% 1.82/0.60    inference(avatar_component_clause,[],[f189])).
% 1.82/0.60  fof(f941,plain,(
% 1.82/0.60    v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3) | ~spl7_47),
% 1.82/0.60    inference(forward_demodulation,[],[f933,f513])).
% 1.82/0.60  fof(f933,plain,(
% 1.82/0.60    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | ~spl7_47),
% 1.82/0.60    inference(resolution,[],[f901,f124])).
% 1.82/0.60  fof(f124,plain,(
% 1.82/0.60    ( ! [X4,X2,X0,X3,X1] : (~sP0(X0,X1,X2,X3,X4) | v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f57])).
% 1.82/0.60  fof(f914,plain,(
% 1.82/0.60    spl7_46),
% 1.82/0.60    inference(avatar_contradiction_clause,[],[f913])).
% 1.82/0.60  fof(f913,plain,(
% 1.82/0.60    $false | spl7_46),
% 1.82/0.60    inference(subsumption_resolution,[],[f912,f71])).
% 1.82/0.60  fof(f912,plain,(
% 1.82/0.60    v2_struct_0(sK5) | spl7_46),
% 1.82/0.60    inference(subsumption_resolution,[],[f911,f72])).
% 1.82/0.60  fof(f911,plain,(
% 1.82/0.60    ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | spl7_46),
% 1.82/0.60    inference(subsumption_resolution,[],[f910,f73])).
% 1.82/0.60  fof(f910,plain,(
% 1.82/0.60    v2_struct_0(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | spl7_46),
% 1.82/0.60    inference(subsumption_resolution,[],[f909,f74])).
% 1.82/0.60  fof(f909,plain,(
% 1.82/0.60    ~m1_pre_topc(sK6,sK2) | v2_struct_0(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | spl7_46),
% 1.82/0.60    inference(subsumption_resolution,[],[f908,f76])).
% 1.82/0.60  fof(f76,plain,(
% 1.82/0.60    r4_tsep_1(sK2,sK5,sK6)),
% 1.82/0.60    inference(cnf_transformation,[],[f51])).
% 1.82/0.60  fof(f908,plain,(
% 1.82/0.60    ~r4_tsep_1(sK2,sK5,sK6) | ~m1_pre_topc(sK6,sK2) | v2_struct_0(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | spl7_46),
% 1.82/0.60    inference(resolution,[],[f897,f278])).
% 1.82/0.60  fof(f278,plain,(
% 1.82/0.60    ( ! [X4,X3] : (sP1(X3,sK2,sK4,X4,sK3) | ~r4_tsep_1(sK2,X3,X4) | ~m1_pre_topc(X4,sK2) | v2_struct_0(X4) | ~m1_pre_topc(X3,sK2) | v2_struct_0(X3)) )),
% 1.82/0.60    inference(subsumption_resolution,[],[f277,f62])).
% 1.82/0.60  fof(f277,plain,(
% 1.82/0.60    ( ! [X4,X3] : (sP1(X3,sK2,sK4,X4,sK3) | ~r4_tsep_1(sK2,X3,X4) | ~m1_pre_topc(X4,sK2) | v2_struct_0(X4) | ~m1_pre_topc(X3,sK2) | v2_struct_0(X3) | v2_struct_0(sK2)) )),
% 1.82/0.60    inference(subsumption_resolution,[],[f276,f63])).
% 1.82/0.60  fof(f276,plain,(
% 1.82/0.60    ( ! [X4,X3] : (sP1(X3,sK2,sK4,X4,sK3) | ~r4_tsep_1(sK2,X3,X4) | ~m1_pre_topc(X4,sK2) | v2_struct_0(X4) | ~m1_pre_topc(X3,sK2) | v2_struct_0(X3) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.82/0.60    inference(subsumption_resolution,[],[f275,f64])).
% 1.82/0.60  fof(f275,plain,(
% 1.82/0.60    ( ! [X4,X3] : (sP1(X3,sK2,sK4,X4,sK3) | ~r4_tsep_1(sK2,X3,X4) | ~m1_pre_topc(X4,sK2) | v2_struct_0(X4) | ~m1_pre_topc(X3,sK2) | v2_struct_0(X3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.82/0.60    inference(subsumption_resolution,[],[f274,f65])).
% 1.82/0.60  fof(f274,plain,(
% 1.82/0.60    ( ! [X4,X3] : (sP1(X3,sK2,sK4,X4,sK3) | ~r4_tsep_1(sK2,X3,X4) | ~m1_pre_topc(X4,sK2) | v2_struct_0(X4) | ~m1_pre_topc(X3,sK2) | v2_struct_0(X3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.82/0.60    inference(subsumption_resolution,[],[f273,f66])).
% 1.82/0.60  fof(f273,plain,(
% 1.82/0.60    ( ! [X4,X3] : (sP1(X3,sK2,sK4,X4,sK3) | ~r4_tsep_1(sK2,X3,X4) | ~m1_pre_topc(X4,sK2) | v2_struct_0(X4) | ~m1_pre_topc(X3,sK2) | v2_struct_0(X3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.82/0.60    inference(subsumption_resolution,[],[f272,f67])).
% 1.82/0.60  fof(f272,plain,(
% 1.82/0.60    ( ! [X4,X3] : (sP1(X3,sK2,sK4,X4,sK3) | ~r4_tsep_1(sK2,X3,X4) | ~m1_pre_topc(X4,sK2) | v2_struct_0(X4) | ~m1_pre_topc(X3,sK2) | v2_struct_0(X3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.82/0.60    inference(subsumption_resolution,[],[f271,f68])).
% 1.82/0.60  fof(f271,plain,(
% 1.82/0.60    ( ! [X4,X3] : (sP1(X3,sK2,sK4,X4,sK3) | ~v1_funct_1(sK4) | ~r4_tsep_1(sK2,X3,X4) | ~m1_pre_topc(X4,sK2) | v2_struct_0(X4) | ~m1_pre_topc(X3,sK2) | v2_struct_0(X3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.82/0.60    inference(subsumption_resolution,[],[f250,f69])).
% 1.82/0.60  fof(f250,plain,(
% 1.82/0.60    ( ! [X4,X3] : (sP1(X3,sK2,sK4,X4,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~r4_tsep_1(sK2,X3,X4) | ~m1_pre_topc(X4,sK2) | v2_struct_0(X4) | ~m1_pre_topc(X3,sK2) | v2_struct_0(X3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.82/0.60    inference(resolution,[],[f70,f127])).
% 1.82/0.60  fof(f127,plain,(
% 1.82/0.60    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | sP1(X2,X0,X4,X3,X1) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f43])).
% 1.82/0.60  fof(f43,plain,(
% 1.82/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (sP1(X2,X0,X4,X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.82/0.60    inference(definition_folding,[],[f26,f42,f41])).
% 1.82/0.60  fof(f26,plain,(
% 1.82/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.82/0.60    inference(flattening,[],[f25])).
% 1.82/0.60  fof(f25,plain,(
% 1.82/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~r4_tsep_1(X0,X2,X3)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.82/0.60    inference(ennf_transformation,[],[f15])).
% 1.82/0.60  fof(f15,axiom,(
% 1.82/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (r4_tsep_1(X0,X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2))))))))))),
% 1.82/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_tmap_1)).
% 1.82/0.60  fof(f897,plain,(
% 1.82/0.60    ~sP1(sK5,sK2,sK4,sK6,sK3) | spl7_46),
% 1.82/0.60    inference(avatar_component_clause,[],[f895])).
% 1.82/0.60  fof(f907,plain,(
% 1.82/0.60    ~spl7_46 | spl7_47 | ~spl7_3),
% 1.82/0.60    inference(avatar_split_clause,[],[f906,f157,f899,f895])).
% 1.82/0.60  fof(f906,plain,(
% 1.82/0.60    sP0(sK3,sK6,sK4,sK2,sK5) | ~sP1(sK5,sK2,sK4,sK6,sK3) | ~spl7_3),
% 1.82/0.60    inference(subsumption_resolution,[],[f905,f68])).
% 1.82/0.60  fof(f905,plain,(
% 1.82/0.60    sP0(sK3,sK6,sK4,sK2,sK5) | ~v1_funct_1(sK4) | ~sP1(sK5,sK2,sK4,sK6,sK3) | ~spl7_3),
% 1.82/0.60    inference(subsumption_resolution,[],[f904,f69])).
% 1.82/0.60  fof(f904,plain,(
% 1.82/0.60    sP0(sK3,sK6,sK4,sK2,sK5) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~sP1(sK5,sK2,sK4,sK6,sK3) | ~spl7_3),
% 1.82/0.60    inference(subsumption_resolution,[],[f903,f158])).
% 1.82/0.60  fof(f158,plain,(
% 1.82/0.60    v5_pre_topc(sK4,sK2,sK3) | ~spl7_3),
% 1.82/0.60    inference(avatar_component_clause,[],[f157])).
% 1.82/0.60  fof(f903,plain,(
% 1.82/0.60    sP0(sK3,sK6,sK4,sK2,sK5) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~sP1(sK5,sK2,sK4,sK6,sK3)),
% 1.82/0.60    inference(subsumption_resolution,[],[f886,f70])).
% 1.82/0.60  fof(f886,plain,(
% 1.82/0.60    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | sP0(sK3,sK6,sK4,sK2,sK5) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~sP1(sK5,sK2,sK4,sK6,sK3)),
% 1.82/0.60    inference(superposition,[],[f239,f516])).
% 1.82/0.60  fof(f239,plain,(
% 1.82/0.60    ( ! [X0,X1] : (~m1_subset_1(k2_tmap_1(sK2,X0,X1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | sP0(X0,sK6,X1,sK2,sK5) | ~v5_pre_topc(k2_tmap_1(sK2,X0,X1,sK2),sK2,X0) | ~v1_funct_2(k2_tmap_1(sK2,X0,X1,sK2),u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(sK2,X0,X1,sK2)) | ~sP1(sK5,sK2,X1,sK6,X0)) )),
% 1.82/0.60    inference(superposition,[],[f113,f75])).
% 1.82/0.60  fof(f113,plain,(
% 1.82/0.60    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) | sP0(X4,X3,X2,X1,X0) | ~v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) | ~v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)) | ~v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) | ~sP1(X0,X1,X2,X3,X4)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f54])).
% 1.82/0.60  fof(f764,plain,(
% 1.82/0.60    spl7_10),
% 1.82/0.60    inference(avatar_contradiction_clause,[],[f763])).
% 1.82/0.60  fof(f763,plain,(
% 1.82/0.60    $false | spl7_10),
% 1.82/0.60    inference(subsumption_resolution,[],[f637,f753])).
% 1.82/0.60  fof(f753,plain,(
% 1.82/0.60    ~v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3)) | spl7_10),
% 1.82/0.60    inference(forward_demodulation,[],[f187,f513])).
% 1.82/0.60  fof(f187,plain,(
% 1.82/0.60    ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | spl7_10),
% 1.82/0.60    inference(avatar_component_clause,[],[f185])).
% 1.82/0.60  fof(f637,plain,(
% 1.82/0.60    v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3))),
% 1.82/0.60    inference(subsumption_resolution,[],[f636,f229])).
% 1.82/0.60  fof(f636,plain,(
% 1.82/0.60    v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3)) | ~l1_struct_0(sK2)),
% 1.82/0.60    inference(subsumption_resolution,[],[f635,f230])).
% 1.82/0.60  fof(f635,plain,(
% 1.82/0.60    v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3)) | ~l1_struct_0(sK3) | ~l1_struct_0(sK2)),
% 1.82/0.60    inference(subsumption_resolution,[],[f634,f68])).
% 1.82/0.60  fof(f634,plain,(
% 1.82/0.60    v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~l1_struct_0(sK3) | ~l1_struct_0(sK2)),
% 1.82/0.60    inference(subsumption_resolution,[],[f633,f69])).
% 1.82/0.60  fof(f633,plain,(
% 1.82/0.60    v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~l1_struct_0(sK3) | ~l1_struct_0(sK2)),
% 1.82/0.60    inference(subsumption_resolution,[],[f632,f70])).
% 1.82/0.60  fof(f632,plain,(
% 1.82/0.60    v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~l1_struct_0(sK3) | ~l1_struct_0(sK2)),
% 1.82/0.60    inference(subsumption_resolution,[],[f628,f236])).
% 1.82/0.60  fof(f236,plain,(
% 1.82/0.60    l1_struct_0(sK6)),
% 1.82/0.60    inference(resolution,[],[f235,f111])).
% 1.82/0.60  fof(f235,plain,(
% 1.82/0.60    l1_pre_topc(sK6)),
% 1.82/0.60    inference(subsumption_resolution,[],[f234,f64])).
% 1.82/0.60  fof(f234,plain,(
% 1.82/0.60    l1_pre_topc(sK6) | ~l1_pre_topc(sK2)),
% 1.82/0.60    inference(resolution,[],[f74,f112])).
% 1.82/0.60  fof(f628,plain,(
% 1.82/0.60    v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3)) | ~l1_struct_0(sK6) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~l1_struct_0(sK3) | ~l1_struct_0(sK2)),
% 1.82/0.60    inference(superposition,[],[f143,f513])).
% 1.82/0.60  fof(f750,plain,(
% 1.82/0.60    spl7_12),
% 1.82/0.60    inference(avatar_contradiction_clause,[],[f749])).
% 1.82/0.60  fof(f749,plain,(
% 1.82/0.60    $false | spl7_12),
% 1.82/0.60    inference(subsumption_resolution,[],[f631,f691])).
% 1.82/0.60  fof(f691,plain,(
% 1.82/0.60    ~m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | spl7_12),
% 1.82/0.60    inference(forward_demodulation,[],[f195,f513])).
% 1.82/0.60  fof(f195,plain,(
% 1.82/0.60    ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | spl7_12),
% 1.82/0.60    inference(avatar_component_clause,[],[f193])).
% 1.82/0.60  fof(f631,plain,(
% 1.82/0.60    m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))),
% 1.82/0.60    inference(subsumption_resolution,[],[f627,f236])).
% 1.82/0.60  fof(f627,plain,(
% 1.82/0.60    m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | ~l1_struct_0(sK6)),
% 1.82/0.60    inference(superposition,[],[f262,f513])).
% 1.82/0.60  fof(f687,plain,(
% 1.82/0.60    spl7_9),
% 1.82/0.60    inference(avatar_contradiction_clause,[],[f686])).
% 1.82/0.60  fof(f686,plain,(
% 1.82/0.60    $false | spl7_9),
% 1.82/0.60    inference(subsumption_resolution,[],[f684,f685])).
% 1.82/0.60  fof(f685,plain,(
% 1.82/0.60    ~v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK6))) | spl7_9),
% 1.82/0.60    inference(forward_demodulation,[],[f183,f513])).
% 1.82/0.60  fof(f183,plain,(
% 1.82/0.60    ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | spl7_9),
% 1.82/0.60    inference(avatar_component_clause,[],[f181])).
% 1.82/0.60  fof(f684,plain,(
% 1.82/0.60    v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK6)))),
% 1.82/0.60    inference(forward_demodulation,[],[f311,f513])).
% 1.82/0.60  fof(f311,plain,(
% 1.82/0.60    v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))),
% 1.82/0.60    inference(resolution,[],[f258,f236])).
% 1.82/0.60  fof(f226,plain,(
% 1.82/0.60    spl7_3 | spl7_5),
% 1.82/0.60    inference(avatar_split_clause,[],[f79,f165,f157])).
% 1.82/0.60  fof(f79,plain,(
% 1.82/0.60    v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | v5_pre_topc(sK4,sK2,sK3)),
% 1.82/0.60    inference(cnf_transformation,[],[f51])).
% 1.82/0.60  fof(f218,plain,(
% 1.82/0.60    spl7_3 | spl7_7),
% 1.82/0.60    inference(avatar_split_clause,[],[f87,f173,f157])).
% 1.82/0.60  fof(f87,plain,(
% 1.82/0.60    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | v5_pre_topc(sK4,sK2,sK3)),
% 1.82/0.60    inference(cnf_transformation,[],[f51])).
% 1.82/0.60  fof(f202,plain,(
% 1.82/0.60    spl7_3 | spl7_11),
% 1.82/0.60    inference(avatar_split_clause,[],[f103,f189,f157])).
% 1.82/0.60  fof(f103,plain,(
% 1.82/0.60    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | v5_pre_topc(sK4,sK2,sK3)),
% 1.82/0.60    inference(cnf_transformation,[],[f51])).
% 1.82/0.60  fof(f196,plain,(
% 1.82/0.60    ~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12),
% 1.82/0.60    inference(avatar_split_clause,[],[f109,f193,f189,f185,f181,f177,f173,f169,f165,f161,f157,f153,f149])).
% 1.82/0.60  fof(f109,plain,(
% 1.82/0.60    ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 1.82/0.60    inference(cnf_transformation,[],[f51])).
% 1.82/0.60  % SZS output end Proof for theBenchmark
% 1.82/0.60  % (25266)------------------------------
% 1.82/0.60  % (25266)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.82/0.60  % (25266)Termination reason: Refutation
% 1.82/0.60  
% 1.82/0.60  % (25266)Memory used [KB]: 12665
% 1.82/0.60  % (25266)Time elapsed: 0.204 s
% 1.82/0.60  % (25266)------------------------------
% 1.82/0.60  % (25266)------------------------------
% 1.82/0.62  % (25263)Success in time 0.277 s
%------------------------------------------------------------------------------
