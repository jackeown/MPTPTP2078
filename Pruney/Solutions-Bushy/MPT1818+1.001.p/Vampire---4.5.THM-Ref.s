%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1818+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:39 EST 2020

% Result     : Theorem 0.16s
% Output     : Refutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :  207 (1273 expanded)
%              Number of leaves         :   25 ( 511 expanded)
%              Depth                    :   23
%              Number of atoms          : 1547 (42920 expanded)
%              Number of equality atoms :   24 (1233 expanded)
%              Maximal formula depth    :   24 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (20853)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
fof(f428,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f155,f170,f179,f216,f226,f230,f241,f251,f255,f285,f410,f427])).

fof(f427,plain,(
    spl8_2 ),
    inference(avatar_contradiction_clause,[],[f426])).

fof(f426,plain,
    ( $false
    | spl8_2 ),
    inference(subsumption_resolution,[],[f425,f119])).

fof(f119,plain,(
    l1_struct_0(sK5) ),
    inference(resolution,[],[f118,f87])).

fof(f87,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f118,plain,(
    l1_pre_topc(sK5) ),
    inference(subsumption_resolution,[],[f117,f40])).

fof(f40,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f25,f30,f29,f28,f27,f26])).

fof(f26,plain,
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

fof(f27,plain,
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

fof(f28,plain,
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

fof(f29,plain,
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

% (20848)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
fof(f30,plain,
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

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
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
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
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

fof(f117,plain,
    ( l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f49,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f49,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f425,plain,
    ( ~ l1_struct_0(sK5)
    | spl8_2 ),
    inference(resolution,[],[f148,f131])).

fof(f131,plain,(
    ! [X0] :
      ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0))
      | ~ l1_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f130,f115])).

fof(f115,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f40,f87])).

fof(f130,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0))
      | ~ l1_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f129,f116])).

fof(f116,plain,(
    l1_struct_0(sK3) ),
    inference(resolution,[],[f43,f87])).

fof(f43,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f129,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0))
      | ~ l1_struct_0(sK3)
      | ~ l1_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f128,f44])).

fof(f44,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f31])).

fof(f128,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0))
      | ~ v1_funct_1(sK4)
      | ~ l1_struct_0(sK3)
      | ~ l1_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f125,f45])).

fof(f45,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f31])).

fof(f125,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0))
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK4)
      | ~ l1_struct_0(sK3)
      | ~ l1_struct_0(sK2) ) ),
    inference(resolution,[],[f46,f106])).

fof(f106,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tmap_1)).

fof(f46,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f31])).

fof(f148,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | spl8_2 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl8_2
  <=> v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f410,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_11 ),
    inference(avatar_contradiction_clause,[],[f409])).

fof(f409,plain,
    ( $false
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f408,f293])).

fof(f293,plain,
    ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
    | spl8_1
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f183,f144])).

fof(f144,plain,
    ( ~ v5_pre_topc(sK4,sK2,sK3)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl8_1
  <=> v5_pre_topc(sK4,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f183,plain,
    ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
    | v5_pre_topc(sK4,sK2,sK3)
    | ~ spl8_4 ),
    inference(resolution,[],[f165,f92])).

fof(f92,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3,X4)
      | ~ sP0(X4,X3,X2,X1,X0)
      | v5_pre_topc(X2,X1,X4) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
            & v5_pre_topc(X2,X1,X4)
            & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
            & v1_funct_1(X2) )
          | ~ sP0(X4,X3,X2,X1,X0) )
        & ( sP0(X4,X3,X2,X1,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
          | ~ v5_pre_topc(X2,X1,X4)
          | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
          | ~ v1_funct_1(X2) ) )
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X3,X0,X2,X4,X1] :
      ( ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            & v5_pre_topc(X2,X0,X1)
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
            & v1_funct_1(X2) )
          | ~ sP0(X1,X4,X2,X0,X3) )
        & ( sP0(X1,X4,X2,X0,X3)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          | ~ v5_pre_topc(X2,X0,X1)
          | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          | ~ v1_funct_1(X2) ) )
      | ~ sP1(X3,X0,X2,X4,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X3,X0,X2,X4,X1] :
      ( ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            & v5_pre_topc(X2,X0,X1)
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
            & v1_funct_1(X2) )
          | ~ sP0(X1,X4,X2,X0,X3) )
        & ( sP0(X1,X4,X2,X0,X3)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          | ~ v5_pre_topc(X2,X0,X1)
          | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          | ~ v1_funct_1(X2) ) )
      | ~ sP1(X3,X0,X2,X4,X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X3,X0,X2,X4,X1] :
      ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v5_pre_topc(X2,X0,X1)
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
      <=> sP0(X1,X4,X2,X0,X3) )
      | ~ sP1(X3,X0,X2,X4,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f165,plain,
    ( sP1(sK5,sK2,sK4,sK6,sK3)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl8_4
  <=> sP1(sK5,sK2,sK4,sK6,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f408,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f407,f154])).

fof(f154,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl8_3
  <=> v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f407,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | sP0(sK3,sK6,sK4,sK2,sK5)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f406,f206])).

fof(f206,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl8_9
  <=> v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f406,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | sP0(sK3,sK6,sK4,sK2,sK5)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f389,f295])).

fof(f295,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f80,f144])).

fof(f80,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f389,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | sP0(sK3,sK6,sK4,sK2,sK5)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_11 ),
    inference(resolution,[],[f384,f214])).

fof(f214,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f213])).

fof(f213,plain,
    ( spl8_11
  <=> m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f384,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
        | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3)
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0))
        | sP0(sK3,X0,sK4,sK2,sK5) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f261,f294])).

fof(f294,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f64,f144])).

fof(f64,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f261,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
        | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3)
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0))
        | sP0(sK3,X0,sK4,sK2,sK5)
        | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) )
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f260,f149])).

fof(f149,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f147])).

fof(f260,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
        | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3)
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0))
        | sP0(sK3,X0,sK4,sK2,sK5)
        | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) )
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f256,f194])).

fof(f194,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl8_6
  <=> v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f256,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
        | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3)
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0))
        | sP0(sK3,X0,sK4,sK2,sK5)
        | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) )
    | ~ spl8_8 ),
    inference(resolution,[],[f202,f102])).

fof(f102,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X1,X4,X2,X0,X3] :
      ( ( sP0(X1,X4,X2,X0,X3)
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
        | ~ sP0(X1,X4,X2,X0,X3) ) ) ),
    inference(flattening,[],[f35])).

% (20846)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
fof(f35,plain,(
    ! [X1,X4,X2,X0,X3] :
      ( ( sP0(X1,X4,X2,X0,X3)
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
        | ~ sP0(X1,X4,X2,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X1,X4,X2,X0,X3] :
      ( sP0(X1,X4,X2,X0,X3)
    <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
        & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
        & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f202,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl8_8
  <=> m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f285,plain,(
    spl8_11 ),
    inference(avatar_contradiction_clause,[],[f284])).

fof(f284,plain,
    ( $false
    | spl8_11 ),
    inference(subsumption_resolution,[],[f283,f115])).

fof(f283,plain,
    ( ~ l1_struct_0(sK2)
    | spl8_11 ),
    inference(subsumption_resolution,[],[f282,f116])).

fof(f282,plain,
    ( ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | spl8_11 ),
    inference(subsumption_resolution,[],[f281,f44])).

fof(f281,plain,
    ( ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | spl8_11 ),
    inference(subsumption_resolution,[],[f280,f45])).

fof(f280,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | spl8_11 ),
    inference(subsumption_resolution,[],[f279,f46])).

fof(f279,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | spl8_11 ),
    inference(subsumption_resolution,[],[f275,f122])).

fof(f122,plain,(
    l1_struct_0(sK6) ),
    inference(resolution,[],[f121,f87])).

fof(f121,plain,(
    l1_pre_topc(sK6) ),
    inference(subsumption_resolution,[],[f120,f40])).

fof(f120,plain,
    ( l1_pre_topc(sK6)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f52,f88])).

fof(f52,plain,(
    m1_pre_topc(sK6,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f275,plain,
    ( ~ l1_struct_0(sK6)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | spl8_11 ),
    inference(resolution,[],[f215,f108])).

fof(f108,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f215,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | spl8_11 ),
    inference(avatar_component_clause,[],[f213])).

fof(f255,plain,
    ( ~ spl8_1
    | ~ spl8_4
    | spl8_10 ),
    inference(avatar_contradiction_clause,[],[f254])).

fof(f254,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_4
    | spl8_10 ),
    inference(resolution,[],[f253,f180])).

fof(f180,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5)
    | ~ spl8_1
    | ~ spl8_4 ),
    inference(resolution,[],[f165,f156])).

fof(f156,plain,
    ( ! [X4,X3] :
        ( ~ sP1(X4,sK2,sK4,X3,sK3)
        | sP0(sK3,X3,sK4,sK2,X4) )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f141,f145])).

fof(f145,plain,
    ( v5_pre_topc(sK4,sK2,sK3)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f143])).

fof(f141,plain,(
    ! [X4,X3] :
      ( sP0(sK3,X3,sK4,sK2,X4)
      | ~ v5_pre_topc(sK4,sK2,sK3)
      | ~ sP1(X4,sK2,sK4,X3,sK3) ) ),
    inference(subsumption_resolution,[],[f140,f44])).

fof(f140,plain,(
    ! [X4,X3] :
      ( sP0(sK3,X3,sK4,sK2,X4)
      | ~ v5_pre_topc(sK4,sK2,sK3)
      | ~ v1_funct_1(sK4)
      | ~ sP1(X4,sK2,sK4,X3,sK3) ) ),
    inference(subsumption_resolution,[],[f127,f45])).

fof(f127,plain,(
    ! [X4,X3] :
      ( sP0(sK3,X3,sK4,sK2,X4)
      | ~ v5_pre_topc(sK4,sK2,sK3)
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK4)
      | ~ sP1(X4,sK2,sK4,X3,sK3) ) ),
    inference(resolution,[],[f46,f89])).

fof(f89,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
      | sP0(X4,X3,X2,X1,X0)
      | ~ v5_pre_topc(X2,X1,X4)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
      | ~ v1_funct_1(X2)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f253,plain,
    ( ! [X1] : ~ sP0(sK3,sK6,sK4,sK2,X1)
    | spl8_10 ),
    inference(resolution,[],[f211,f100])).

fof(f100,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f211,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | spl8_10 ),
    inference(avatar_component_clause,[],[f209])).

fof(f209,plain,
    ( spl8_10
  <=> v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f251,plain,(
    spl8_9 ),
    inference(avatar_contradiction_clause,[],[f250])).

fof(f250,plain,
    ( $false
    | spl8_9 ),
    inference(subsumption_resolution,[],[f249,f115])).

fof(f249,plain,
    ( ~ l1_struct_0(sK2)
    | spl8_9 ),
    inference(subsumption_resolution,[],[f248,f116])).

fof(f248,plain,
    ( ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | spl8_9 ),
    inference(subsumption_resolution,[],[f247,f44])).

fof(f247,plain,
    ( ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | spl8_9 ),
    inference(subsumption_resolution,[],[f246,f45])).

fof(f246,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | spl8_9 ),
    inference(subsumption_resolution,[],[f245,f46])).

fof(f245,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | spl8_9 ),
    inference(subsumption_resolution,[],[f242,f122])).

fof(f242,plain,
    ( ~ l1_struct_0(sK6)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | spl8_9 ),
    inference(resolution,[],[f207,f107])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f207,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | spl8_9 ),
    inference(avatar_component_clause,[],[f205])).

fof(f241,plain,(
    spl8_8 ),
    inference(avatar_contradiction_clause,[],[f240])).

fof(f240,plain,
    ( $false
    | spl8_8 ),
    inference(subsumption_resolution,[],[f239,f115])).

fof(f239,plain,
    ( ~ l1_struct_0(sK2)
    | spl8_8 ),
    inference(subsumption_resolution,[],[f238,f116])).

fof(f238,plain,
    ( ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | spl8_8 ),
    inference(subsumption_resolution,[],[f237,f44])).

fof(f237,plain,
    ( ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | spl8_8 ),
    inference(subsumption_resolution,[],[f236,f45])).

fof(f236,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | spl8_8 ),
    inference(subsumption_resolution,[],[f235,f46])).

fof(f235,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | spl8_8 ),
    inference(subsumption_resolution,[],[f231,f119])).

fof(f231,plain,
    ( ~ l1_struct_0(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | spl8_8 ),
    inference(resolution,[],[f203,f108])).

fof(f203,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | spl8_8 ),
    inference(avatar_component_clause,[],[f201])).

fof(f230,plain,
    ( ~ spl8_1
    | ~ spl8_4
    | spl8_7 ),
    inference(avatar_contradiction_clause,[],[f229])).

fof(f229,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_4
    | spl8_7 ),
    inference(resolution,[],[f227,f180])).

fof(f227,plain,
    ( ! [X0] : ~ sP0(sK3,X0,sK4,sK2,sK5)
    | spl8_7 ),
    inference(resolution,[],[f199,f96])).

fof(f96,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f199,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | spl8_7 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl8_7
  <=> v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f226,plain,(
    spl8_6 ),
    inference(avatar_contradiction_clause,[],[f225])).

fof(f225,plain,
    ( $false
    | spl8_6 ),
    inference(subsumption_resolution,[],[f224,f115])).

fof(f224,plain,
    ( ~ l1_struct_0(sK2)
    | spl8_6 ),
    inference(subsumption_resolution,[],[f223,f116])).

fof(f223,plain,
    ( ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | spl8_6 ),
    inference(subsumption_resolution,[],[f222,f44])).

fof(f222,plain,
    ( ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | spl8_6 ),
    inference(subsumption_resolution,[],[f221,f45])).

fof(f221,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | spl8_6 ),
    inference(subsumption_resolution,[],[f220,f46])).

fof(f220,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | spl8_6 ),
    inference(subsumption_resolution,[],[f217,f119])).

fof(f217,plain,
    ( ~ l1_struct_0(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | spl8_6 ),
    inference(resolution,[],[f195,f107])).

fof(f195,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | spl8_6 ),
    inference(avatar_component_clause,[],[f193])).

fof(f216,plain,
    ( ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f191,f163,f147,f143,f213,f209,f205,f201,f197,f193])).

fof(f191,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f190,f44])).

fof(f190,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f189,f45])).

fof(f189,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f188,f145])).

fof(f188,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f187,f46])).

fof(f187,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f186,f149])).

fof(f186,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ spl8_1
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f86,f185])).

fof(f185,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | ~ spl8_1
    | ~ spl8_4 ),
    inference(resolution,[],[f180,f98])).

fof(f98,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3,X4)
      | v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f86,plain,
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
    inference(cnf_transformation,[],[f31])).

fof(f179,plain,(
    spl8_5 ),
    inference(avatar_contradiction_clause,[],[f178])).

fof(f178,plain,
    ( $false
    | spl8_5 ),
    inference(subsumption_resolution,[],[f177,f38])).

fof(f38,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f177,plain,
    ( v2_struct_0(sK2)
    | spl8_5 ),
    inference(subsumption_resolution,[],[f176,f39])).

fof(f39,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f176,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_5 ),
    inference(subsumption_resolution,[],[f175,f40])).

fof(f175,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_5 ),
    inference(subsumption_resolution,[],[f174,f48])).

fof(f48,plain,(
    v1_tsep_1(sK5,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f174,plain,
    ( ~ v1_tsep_1(sK5,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_5 ),
    inference(subsumption_resolution,[],[f173,f49])).

fof(f173,plain,
    ( ~ m1_pre_topc(sK5,sK2)
    | ~ v1_tsep_1(sK5,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_5 ),
    inference(subsumption_resolution,[],[f172,f51])).

fof(f51,plain,(
    v1_tsep_1(sK6,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f172,plain,
    ( ~ v1_tsep_1(sK6,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ v1_tsep_1(sK5,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_5 ),
    inference(subsumption_resolution,[],[f171,f52])).

fof(f171,plain,
    ( ~ m1_pre_topc(sK6,sK2)
    | ~ v1_tsep_1(sK6,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ v1_tsep_1(sK5,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_5 ),
    inference(resolution,[],[f169,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( r4_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_tsep_1(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f169,plain,
    ( ~ r4_tsep_1(sK2,sK5,sK6)
    | spl8_5 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl8_5
  <=> r4_tsep_1(sK2,sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f170,plain,
    ( spl8_4
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f161,f167,f163])).

fof(f161,plain,
    ( ~ r4_tsep_1(sK2,sK5,sK6)
    | sP1(sK5,sK2,sK4,sK6,sK3) ),
    inference(subsumption_resolution,[],[f160,f47])).

fof(f47,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f31])).

fof(f160,plain,
    ( ~ r4_tsep_1(sK2,sK5,sK6)
    | v2_struct_0(sK5)
    | sP1(sK5,sK2,sK4,sK6,sK3) ),
    inference(subsumption_resolution,[],[f159,f49])).

fof(f159,plain,
    ( ~ r4_tsep_1(sK2,sK5,sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | sP1(sK5,sK2,sK4,sK6,sK3) ),
    inference(subsumption_resolution,[],[f158,f50])).

fof(f50,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f31])).

fof(f158,plain,
    ( ~ r4_tsep_1(sK2,sK5,sK6)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | sP1(sK5,sK2,sK4,sK6,sK3) ),
    inference(subsumption_resolution,[],[f157,f52])).

fof(f157,plain,
    ( ~ r4_tsep_1(sK2,sK5,sK6)
    | ~ m1_pre_topc(sK6,sK2)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | sP1(sK5,sK2,sK4,sK6,sK3) ),
    inference(resolution,[],[f139,f123])).

fof(f123,plain,(
    sQ7_eqProxy(k1_tsep_1(sK2,sK5,sK6),sK2) ),
    inference(resolution,[],[f110,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ sQ7_eqProxy(X0,X1)
      | sQ7_eqProxy(X1,X0) ) ),
    inference(equality_proxy_axiom,[],[f109])).

fof(f109,plain,(
    ! [X1,X0] :
      ( sQ7_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ7_eqProxy])])).

fof(f110,plain,(
    sQ7_eqProxy(sK2,k1_tsep_1(sK2,sK5,sK6)) ),
    inference(equality_proxy_replacement,[],[f53,f109])).

fof(f53,plain,(
    sK2 = k1_tsep_1(sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f31])).

fof(f139,plain,(
    ! [X2,X1] :
      ( ~ sQ7_eqProxy(k1_tsep_1(sK2,X1,X2),sK2)
      | ~ r4_tsep_1(sK2,X1,X2)
      | ~ m1_pre_topc(X2,sK2)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | sP1(X1,sK2,sK4,X2,sK3) ) ),
    inference(subsumption_resolution,[],[f138,f38])).

fof(f138,plain,(
    ! [X2,X1] :
      ( ~ r4_tsep_1(sK2,X1,X2)
      | ~ sQ7_eqProxy(k1_tsep_1(sK2,X1,X2),sK2)
      | ~ m1_pre_topc(X2,sK2)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | sP1(X1,sK2,sK4,X2,sK3)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f137,f39])).

fof(f137,plain,(
    ! [X2,X1] :
      ( ~ r4_tsep_1(sK2,X1,X2)
      | ~ sQ7_eqProxy(k1_tsep_1(sK2,X1,X2),sK2)
      | ~ m1_pre_topc(X2,sK2)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | sP1(X1,sK2,sK4,X2,sK3)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f136,f40])).

fof(f136,plain,(
    ! [X2,X1] :
      ( ~ r4_tsep_1(sK2,X1,X2)
      | ~ sQ7_eqProxy(k1_tsep_1(sK2,X1,X2),sK2)
      | ~ m1_pre_topc(X2,sK2)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | sP1(X1,sK2,sK4,X2,sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f135,f41])).

fof(f41,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f135,plain,(
    ! [X2,X1] :
      ( ~ r4_tsep_1(sK2,X1,X2)
      | ~ sQ7_eqProxy(k1_tsep_1(sK2,X1,X2),sK2)
      | ~ m1_pre_topc(X2,sK2)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | sP1(X1,sK2,sK4,X2,sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f134,f42])).

fof(f42,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f134,plain,(
    ! [X2,X1] :
      ( ~ r4_tsep_1(sK2,X1,X2)
      | ~ sQ7_eqProxy(k1_tsep_1(sK2,X1,X2),sK2)
      | ~ m1_pre_topc(X2,sK2)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | sP1(X1,sK2,sK4,X2,sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f133,f43])).

fof(f133,plain,(
    ! [X2,X1] :
      ( ~ r4_tsep_1(sK2,X1,X2)
      | ~ sQ7_eqProxy(k1_tsep_1(sK2,X1,X2),sK2)
      | ~ m1_pre_topc(X2,sK2)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | sP1(X1,sK2,sK4,X2,sK3)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f132,f44])).

fof(f132,plain,(
    ! [X2,X1] :
      ( ~ r4_tsep_1(sK2,X1,X2)
      | ~ sQ7_eqProxy(k1_tsep_1(sK2,X1,X2),sK2)
      | ~ m1_pre_topc(X2,sK2)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | sP1(X1,sK2,sK4,X2,sK3)
      | ~ v1_funct_1(sK4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f126,f45])).

fof(f126,plain,(
    ! [X2,X1] :
      ( ~ r4_tsep_1(sK2,X1,X2)
      | ~ sQ7_eqProxy(k1_tsep_1(sK2,X1,X2),sK2)
      | ~ m1_pre_topc(X2,sK2)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | sP1(X1,sK2,sK4,X2,sK3)
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f46,f111])).

fof(f111,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ r4_tsep_1(X0,X3,X4)
      | ~ sQ7_eqProxy(k1_tsep_1(X0,X3,X4),X0)
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | sP1(X3,X0,X2,X4,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f103,f109])).

fof(f103,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP1(X3,X0,X2,X4,X1)
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
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( sP1(X3,X0,X2,X4,X1)
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
    inference(definition_folding,[],[f14,f22,f21])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f155,plain,
    ( spl8_1
    | spl8_3 ),
    inference(avatar_split_clause,[],[f72,f152,f143])).

fof(f72,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f31])).

%------------------------------------------------------------------------------
