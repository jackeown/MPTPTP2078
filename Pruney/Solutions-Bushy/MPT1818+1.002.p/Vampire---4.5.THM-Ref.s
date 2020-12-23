%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1818+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  121 (6699 expanded)
%              Number of leaves         :   10 (2855 expanded)
%              Depth                    :   28
%              Number of atoms          : 1284 (271062 expanded)
%              Number of equality atoms :   44 (8101 expanded)
%              Maximal formula depth    :   24 (   9 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f503,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f383,f398,f402,f400,f404,f399,f403,f401,f405,f301])).

fof(f301,plain,
    ( ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
    inference(subsumption_resolution,[],[f300,f35])).

fof(f35,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
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
    & sK2 = k1_tsep_1(sK2,sK5,sK6)
    & m1_pre_topc(sK6,sK2)
    & v1_tsep_1(sK6,sK2)
    & ~ v2_struct_0(sK6)
    & m1_pre_topc(sK5,sK2)
    & v1_tsep_1(sK5,sK2)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f15,f20,f19,f18,f17,f16])).

% (6414)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
fof(f16,plain,
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
                        & k1_tsep_1(X0,X3,X4) = X0
                        & m1_pre_topc(X4,X0)
                        & v1_tsep_1(X4,X0)
                        & ~ v2_struct_0(X4) )
                    & m1_pre_topc(X3,X0)
                    & v1_tsep_1(X3,X0)
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
                      & sK2 = k1_tsep_1(sK2,X3,X4)
                      & m1_pre_topc(X4,sK2)
                      & v1_tsep_1(X4,sK2)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,sK2)
                  & v1_tsep_1(X3,sK2)
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

% (6410)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
fof(f17,plain,
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
                    & sK2 = k1_tsep_1(sK2,X3,X4)
                    & m1_pre_topc(X4,sK2)
                    & v1_tsep_1(X4,sK2)
                    & ~ v2_struct_0(X4) )
                & m1_pre_topc(X3,sK2)
                & v1_tsep_1(X3,sK2)
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
                  & sK2 = k1_tsep_1(sK2,X3,X4)
                  & m1_pre_topc(X4,sK2)
                  & v1_tsep_1(X4,sK2)
                  & ~ v2_struct_0(X4) )
              & m1_pre_topc(X3,sK2)
              & v1_tsep_1(X3,sK2)
              & ~ v2_struct_0(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
          & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
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
                & sK2 = k1_tsep_1(sK2,X3,X4)
                & m1_pre_topc(X4,sK2)
                & v1_tsep_1(X4,sK2)
                & ~ v2_struct_0(X4) )
            & m1_pre_topc(X3,sK2)
            & v1_tsep_1(X3,sK2)
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
              & sK2 = k1_tsep_1(sK2,X3,X4)
              & m1_pre_topc(X4,sK2)
              & v1_tsep_1(X4,sK2)
              & ~ v2_struct_0(X4) )
          & m1_pre_topc(X3,sK2)
          & v1_tsep_1(X3,sK2)
          & ~ v2_struct_0(X3) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
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
            & sK2 = k1_tsep_1(sK2,X3,X4)
            & m1_pre_topc(X4,sK2)
            & v1_tsep_1(X4,sK2)
            & ~ v2_struct_0(X4) )
        & m1_pre_topc(X3,sK2)
        & v1_tsep_1(X3,sK2)
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
          & sK2 = k1_tsep_1(sK2,sK5,X4)
          & m1_pre_topc(X4,sK2)
          & v1_tsep_1(X4,sK2)
          & ~ v2_struct_0(X4) )
      & m1_pre_topc(sK5,sK2)
      & v1_tsep_1(sK5,sK2)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
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
        & sK2 = k1_tsep_1(sK2,sK5,X4)
        & m1_pre_topc(X4,sK2)
        & v1_tsep_1(X4,sK2)
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
      & sK2 = k1_tsep_1(sK2,sK5,sK6)
      & m1_pre_topc(sK6,sK2)
      & v1_tsep_1(sK6,sK2)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
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
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & v1_tsep_1(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_tsep_1(X3,X0)
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & v1_tsep_1(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_tsep_1(X3,X0)
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
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
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
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & v1_tsep_1(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_tsep_1(X3,X0)
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
    inference(flattening,[],[f5])).

fof(f5,plain,(
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
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & v1_tsep_1(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_tsep_1(X3,X0)
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
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
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
                      & v1_tsep_1(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_pre_topc(X4,X0)
                          & v1_tsep_1(X4,X0)
                          & ~ v2_struct_0(X4) )
                       => ( k1_tsep_1(X0,X3,X4) = X0
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
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
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
                    & v1_tsep_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & v1_tsep_1(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( k1_tsep_1(X0,X3,X4) = X0
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_tmap_1)).

fof(f300,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f299,f36])).

fof(f36,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f21])).

fof(f299,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f77,f37])).

fof(f37,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f21])).

fof(f77,plain,
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
    inference(cnf_transformation,[],[f21])).

fof(f405,plain,(
    m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
    inference(unit_resulting_resolution,[],[f379,f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP1(X0,X1,X2,X3,X4)
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
        | ~ sP1(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X1,X4,X2,X0,X3] :
      ( ( sP1(X1,X4,X2,X0,X3)
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
        | ~ sP1(X1,X4,X2,X0,X3) ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X1,X4,X2,X0,X3] :
      ( ( sP1(X1,X4,X2,X0,X3)
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
        | ~ sP1(X1,X4,X2,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X1,X4,X2,X0,X3] :
      ( sP1(X1,X4,X2,X0,X3)
    <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
        & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
        & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f379,plain,(
    sP1(sK3,sK6,sK4,sK2,sK5) ),
    inference(unit_resulting_resolution,[],[f38,f41,f40,f43,f168,f44,f378,f193])).

fof(f193,plain,(
    ! [X0,X1] :
      ( ~ sP0(sK3,sK2,sK4)
      | sP1(sK3,X0,sK4,sK2,X1)
      | ~ r4_tsep_1(sK2,X1,X0)
      | sK2 != k1_tsep_1(sK2,X1,X0)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f192,f29])).

fof(f29,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f192,plain,(
    ! [X0,X1] :
      ( sP1(sK3,X0,sK4,sK2,X1)
      | ~ sP0(sK3,sK2,sK4)
      | ~ r4_tsep_1(sK2,X1,X0)
      | sK2 != k1_tsep_1(sK2,X1,X0)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f191,f30])).

fof(f30,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f191,plain,(
    ! [X0,X1] :
      ( sP1(sK3,X0,sK4,sK2,X1)
      | ~ sP0(sK3,sK2,sK4)
      | ~ r4_tsep_1(sK2,X1,X0)
      | sK2 != k1_tsep_1(sK2,X1,X0)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f190,f31])).

fof(f31,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f190,plain,(
    ! [X0,X1] :
      ( sP1(sK3,X0,sK4,sK2,X1)
      | ~ sP0(sK3,sK2,sK4)
      | ~ r4_tsep_1(sK2,X1,X0)
      | sK2 != k1_tsep_1(sK2,X1,X0)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f189,f32])).

fof(f32,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f189,plain,(
    ! [X0,X1] :
      ( sP1(sK3,X0,sK4,sK2,X1)
      | ~ sP0(sK3,sK2,sK4)
      | ~ r4_tsep_1(sK2,X1,X0)
      | sK2 != k1_tsep_1(sK2,X1,X0)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f188,f33])).

fof(f33,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f188,plain,(
    ! [X0,X1] :
      ( sP1(sK3,X0,sK4,sK2,X1)
      | ~ sP0(sK3,sK2,sK4)
      | ~ r4_tsep_1(sK2,X1,X0)
      | sK2 != k1_tsep_1(sK2,X1,X0)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f187,f34])).

fof(f34,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f187,plain,(
    ! [X0,X1] :
      ( sP1(sK3,X0,sK4,sK2,X1)
      | ~ sP0(sK3,sK2,sK4)
      | ~ r4_tsep_1(sK2,X1,X0)
      | sK2 != k1_tsep_1(sK2,X1,X0)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f186,f35])).

fof(f186,plain,(
    ! [X0,X1] :
      ( sP1(sK3,X0,sK4,sK2,X1)
      | ~ sP0(sK3,sK2,sK4)
      | ~ r4_tsep_1(sK2,X1,X0)
      | sK2 != k1_tsep_1(sK2,X1,X0)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | ~ v1_funct_1(sK4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f183,f36])).

fof(f183,plain,(
    ! [X0,X1] :
      ( sP1(sK3,X0,sK4,sK2,X1)
      | ~ sP0(sK3,sK2,sK4)
      | ~ r4_tsep_1(sK2,X1,X0)
      | sK2 != k1_tsep_1(sK2,X1,X0)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f37,f92])).

fof(f92,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP1(X1,X4,X2,X0,X3)
      | ~ sP0(X1,X0,X2)
      | ~ r4_tsep_1(X0,X3,X4)
      | k1_tsep_1(X0,X3,X4) != X0
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
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
                  ( ! [X4] :
                      ( ( ( sP0(X1,X0,X2)
                          | ~ sP1(X1,X4,X2,X0,X3) )
                        & ( sP1(X1,X4,X2,X0,X3)
                          | ~ sP0(X1,X0,X2) ) )
                      | ~ r4_tsep_1(X0,X3,X4)
                      | k1_tsep_1(X0,X3,X4) != X0
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( sP0(X1,X0,X2)
                      <=> sP1(X1,X4,X2,X0,X3) )
                      | ~ r4_tsep_1(X0,X3,X4)
                      | k1_tsep_1(X0,X3,X4) != X0
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f8,f12,f11])).

fof(f11,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v5_pre_topc(X2,X0,X1)
        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
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
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) )
                      | ~ r4_tsep_1(X0,X3,X4)
                      | k1_tsep_1(X0,X3,X4) != X0
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
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
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) )
                      | ~ r4_tsep_1(X0,X3,X4)
                      | k1_tsep_1(X0,X3,X4) != X0
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_tmap_1)).

fof(f378,plain,(
    sP0(sK3,sK2,sK4) ),
    inference(subsumption_resolution,[],[f368,f203])).

fof(f203,plain,
    ( ~ v5_pre_topc(sK4,sK2,sK3)
    | sP0(sK3,sK2,sK4) ),
    inference(subsumption_resolution,[],[f202,f35])).

fof(f202,plain,
    ( sP0(sK3,sK2,sK4)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f185,f36])).

fof(f185,plain,
    ( sP0(sK3,sK2,sK4)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f37,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v5_pre_topc(X2,X1,X0)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | ~ v5_pre_topc(X2,X1,X0)
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
        | ~ v1_funct_1(X2) )
      & ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v5_pre_topc(X2,X1,X0)
          & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v5_pre_topc(X2,X0,X1)
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v1_funct_1(X2) )
      & ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v5_pre_topc(X2,X0,X1)
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v5_pre_topc(X2,X0,X1)
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v1_funct_1(X2) )
      & ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v5_pre_topc(X2,X0,X1)
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f368,plain,
    ( v5_pre_topc(sK4,sK2,sK3)
    | sP0(sK3,sK2,sK4) ),
    inference(resolution,[],[f330,f311])).

fof(f311,plain,
    ( ~ sP1(sK3,sK6,sK4,sK2,sK5)
    | sP0(sK3,sK2,sK4) ),
    inference(subsumption_resolution,[],[f310,f38])).

fof(f310,plain,
    ( ~ sP1(sK3,sK6,sK4,sK2,sK5)
    | sP0(sK3,sK2,sK4)
    | v2_struct_0(sK5) ),
    inference(subsumption_resolution,[],[f309,f40])).

fof(f309,plain,
    ( ~ sP1(sK3,sK6,sK4,sK2,sK5)
    | sP0(sK3,sK2,sK4)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5) ),
    inference(subsumption_resolution,[],[f308,f41])).

fof(f308,plain,
    ( ~ sP1(sK3,sK6,sK4,sK2,sK5)
    | sP0(sK3,sK2,sK4)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5) ),
    inference(subsumption_resolution,[],[f307,f43])).

fof(f307,plain,
    ( ~ sP1(sK3,sK6,sK4,sK2,sK5)
    | sP0(sK3,sK2,sK4)
    | ~ m1_pre_topc(sK6,sK2)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5) ),
    inference(subsumption_resolution,[],[f306,f168])).

fof(f306,plain,
    ( ~ sP1(sK3,sK6,sK4,sK2,sK5)
    | ~ r4_tsep_1(sK2,sK5,sK6)
    | sP0(sK3,sK2,sK4)
    | ~ m1_pre_topc(sK6,sK2)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5) ),
    inference(trivial_inequality_removal,[],[f305])).

fof(f305,plain,
    ( sK2 != sK2
    | ~ sP1(sK3,sK6,sK4,sK2,sK5)
    | ~ r4_tsep_1(sK2,sK5,sK6)
    | sP0(sK3,sK2,sK4)
    | ~ m1_pre_topc(sK6,sK2)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5) ),
    inference(superposition,[],[f201,f44])).

fof(f201,plain,(
    ! [X2,X3] :
      ( sK2 != k1_tsep_1(sK2,X3,X2)
      | ~ sP1(sK3,X2,sK4,sK2,X3)
      | ~ r4_tsep_1(sK2,X3,X2)
      | sP0(sK3,sK2,sK4)
      | ~ m1_pre_topc(X2,sK2)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X3,sK2)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f200,f29])).

fof(f200,plain,(
    ! [X2,X3] :
      ( sP0(sK3,sK2,sK4)
      | ~ sP1(sK3,X2,sK4,sK2,X3)
      | ~ r4_tsep_1(sK2,X3,X2)
      | sK2 != k1_tsep_1(sK2,X3,X2)
      | ~ m1_pre_topc(X2,sK2)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X3,sK2)
      | v2_struct_0(X3)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f199,f30])).

fof(f199,plain,(
    ! [X2,X3] :
      ( sP0(sK3,sK2,sK4)
      | ~ sP1(sK3,X2,sK4,sK2,X3)
      | ~ r4_tsep_1(sK2,X3,X2)
      | sK2 != k1_tsep_1(sK2,X3,X2)
      | ~ m1_pre_topc(X2,sK2)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X3,sK2)
      | v2_struct_0(X3)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f198,f31])).

fof(f198,plain,(
    ! [X2,X3] :
      ( sP0(sK3,sK2,sK4)
      | ~ sP1(sK3,X2,sK4,sK2,X3)
      | ~ r4_tsep_1(sK2,X3,X2)
      | sK2 != k1_tsep_1(sK2,X3,X2)
      | ~ m1_pre_topc(X2,sK2)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X3,sK2)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f197,f32])).

fof(f197,plain,(
    ! [X2,X3] :
      ( sP0(sK3,sK2,sK4)
      | ~ sP1(sK3,X2,sK4,sK2,X3)
      | ~ r4_tsep_1(sK2,X3,X2)
      | sK2 != k1_tsep_1(sK2,X3,X2)
      | ~ m1_pre_topc(X2,sK2)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X3,sK2)
      | v2_struct_0(X3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f196,f33])).

fof(f196,plain,(
    ! [X2,X3] :
      ( sP0(sK3,sK2,sK4)
      | ~ sP1(sK3,X2,sK4,sK2,X3)
      | ~ r4_tsep_1(sK2,X3,X2)
      | sK2 != k1_tsep_1(sK2,X3,X2)
      | ~ m1_pre_topc(X2,sK2)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X3,sK2)
      | v2_struct_0(X3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f195,f34])).

fof(f195,plain,(
    ! [X2,X3] :
      ( sP0(sK3,sK2,sK4)
      | ~ sP1(sK3,X2,sK4,sK2,X3)
      | ~ r4_tsep_1(sK2,X3,X2)
      | sK2 != k1_tsep_1(sK2,X3,X2)
      | ~ m1_pre_topc(X2,sK2)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X3,sK2)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f194,f35])).

fof(f194,plain,(
    ! [X2,X3] :
      ( sP0(sK3,sK2,sK4)
      | ~ sP1(sK3,X2,sK4,sK2,X3)
      | ~ r4_tsep_1(sK2,X3,X2)
      | sK2 != k1_tsep_1(sK2,X3,X2)
      | ~ m1_pre_topc(X2,sK2)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X3,sK2)
      | v2_struct_0(X3)
      | ~ v1_funct_1(sK4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f184,f36])).

fof(f184,plain,(
    ! [X2,X3] :
      ( sP0(sK3,sK2,sK4)
      | ~ sP1(sK3,X2,sK4,sK2,X3)
      | ~ r4_tsep_1(sK2,X3,X2)
      | sK2 != k1_tsep_1(sK2,X3,X2)
      | ~ m1_pre_topc(X2,sK2)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X3,sK2)
      | v2_struct_0(X3)
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f37,f93])).

fof(f93,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X1,X0,X2)
      | ~ sP1(X1,X4,X2,X0,X3)
      | ~ r4_tsep_1(X0,X3,X4)
      | k1_tsep_1(X0,X3,X4) != X0
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

% (6420)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
fof(f330,plain,
    ( sP1(sK3,sK6,sK4,sK2,sK5)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(subsumption_resolution,[],[f329,f63])).

fof(f63,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f329,plain,
    ( sP1(sK3,sK6,sK4,sK2,sK5)
    | v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    inference(subsumption_resolution,[],[f328,f67])).

fof(f67,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f328,plain,
    ( sP1(sK3,sK6,sK4,sK2,sK5)
    | v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    inference(subsumption_resolution,[],[f317,f71])).

fof(f71,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f317,plain,
    ( sP1(sK3,sK6,sK4,sK2,sK5)
    | v5_pre_topc(sK4,sK2,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    inference(duplicate_literal_removal,[],[f315])).

fof(f315,plain,
    ( sP1(sK3,sK6,sK4,sK2,sK5)
    | v5_pre_topc(sK4,sK2,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(resolution,[],[f244,f75])).

fof(f75,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f244,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
      | sP1(sK3,X0,sK4,sK2,sK5)
      | v5_pre_topc(sK4,sK2,sK3)
      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3)
      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3))
      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) ) ),
    inference(subsumption_resolution,[],[f243,f47])).

fof(f47,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f243,plain,(
    ! [X0] :
      ( v5_pre_topc(sK4,sK2,sK3)
      | sP1(sK3,X0,sK4,sK2,sK5)
      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3)
      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3))
      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0))
      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) ) ),
    inference(subsumption_resolution,[],[f242,f51])).

fof(f51,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f242,plain,(
    ! [X0] :
      ( v5_pre_topc(sK4,sK2,sK3)
      | sP1(sK3,X0,sK4,sK2,sK5)
      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3)
      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3))
      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0))
      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) ) ),
    inference(subsumption_resolution,[],[f237,f55])).

fof(f55,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f237,plain,(
    ! [X0] :
      ( v5_pre_topc(sK4,sK2,sK3)
      | sP1(sK3,X0,sK4,sK2,sK5)
      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3)
      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3))
      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0))
      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) ) ),
    inference(resolution,[],[f59,f86])).

fof(f86,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
      | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
      | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
      | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
      | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f59,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f44,plain,(
    sK2 = k1_tsep_1(sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f21])).

fof(f168,plain,(
    r4_tsep_1(sK2,sK5,sK6) ),
    inference(unit_resulting_resolution,[],[f29,f30,f31,f39,f40,f42,f43,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( r4_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_tsep_1(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_tsep_1(X0,X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_tsep_1(X2,X0) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_tsep_1(X0,X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_tsep_1(X2,X0) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v1_tsep_1(X1,X0) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_tsep_1(X2,X0) )
             => r4_tsep_1(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tsep_1)).

fof(f42,plain,(
    v1_tsep_1(sK6,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f39,plain,(
    v1_tsep_1(sK5,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f43,plain,(
    m1_pre_topc(sK6,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f40,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f41,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f21])).

fof(f38,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f21])).

fof(f401,plain,(
    m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(unit_resulting_resolution,[],[f379,f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f403,plain,(
    v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) ),
    inference(unit_resulting_resolution,[],[f379,f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f399,plain,(
    v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(unit_resulting_resolution,[],[f379,f79])).

fof(f79,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f404,plain,(
    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) ),
    inference(unit_resulting_resolution,[],[f379,f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f400,plain,(
    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) ),
    inference(unit_resulting_resolution,[],[f379,f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f402,plain,(
    v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    inference(unit_resulting_resolution,[],[f379,f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f398,plain,(
    v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) ),
    inference(unit_resulting_resolution,[],[f379,f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X3,X0,X2,X4))
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f383,plain,(
    v5_pre_topc(sK4,sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f378,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X1,X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

%------------------------------------------------------------------------------
