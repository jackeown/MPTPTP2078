%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1767+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:31 EST 2020

% Result     : Theorem 6.63s
% Output     : Refutation 6.63s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 410 expanded)
%              Number of leaves         :   17 ( 196 expanded)
%              Depth                    :   23
%              Number of atoms          :  639 (5367 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   26 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f25835,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f25678,f25800,f25806,f25812,f25819,f25833,f25834])).

fof(f25834,plain,
    ( spl1387_6
    | ~ spl1387_7
    | ~ spl1387_8
    | ~ spl1387_9 ),
    inference(avatar_contradiction_clause,[],[f25832])).

fof(f25832,plain,
    ( $false
    | spl1387_6
    | ~ spl1387_7
    | ~ spl1387_8
    | ~ spl1387_9 ),
    inference(unit_resulting_resolution,[],[f25790,f25794,f11850,f11851,f11852,f25677,f25798,f19020])).

fof(f19020,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f8080])).

fof(f8080,plain,(
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
    inference(flattening,[],[f8079])).

fof(f8079,plain,(
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
    inference(ennf_transformation,[],[f3335])).

fof(f3335,axiom,(
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

fof(f25798,plain,
    ( l1_struct_0(sK58)
    | ~ spl1387_9 ),
    inference(avatar_component_clause,[],[f25797])).

fof(f25797,plain,
    ( spl1387_9
  <=> l1_struct_0(sK58) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1387_9])])).

fof(f25677,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK55,sK56,sK59,sK58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK58),u1_struct_0(sK56))))
    | spl1387_6 ),
    inference(avatar_component_clause,[],[f25675])).

fof(f25675,plain,
    ( spl1387_6
  <=> m1_subset_1(k2_tmap_1(sK55,sK56,sK59,sK58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK58),u1_struct_0(sK56)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1387_6])])).

fof(f11852,plain,(
    m1_subset_1(sK59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK55),u1_struct_0(sK56)))) ),
    inference(cnf_transformation,[],[f8426])).

fof(f8426,plain,
    ( ~ r2_funct_2(u1_struct_0(sK57),u1_struct_0(sK56),k3_tmap_1(sK55,sK56,sK58,sK57,k2_tmap_1(sK55,sK56,sK59,sK58)),k2_tmap_1(sK55,sK56,sK59,sK57))
    & m1_pre_topc(sK57,sK58)
    & m1_subset_1(sK59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK55),u1_struct_0(sK56))))
    & v1_funct_2(sK59,u1_struct_0(sK55),u1_struct_0(sK56))
    & v1_funct_1(sK59)
    & m1_pre_topc(sK58,sK55)
    & ~ v2_struct_0(sK58)
    & m1_pre_topc(sK57,sK55)
    & ~ v2_struct_0(sK57)
    & l1_pre_topc(sK56)
    & v2_pre_topc(sK56)
    & ~ v2_struct_0(sK56)
    & l1_pre_topc(sK55)
    & v2_pre_topc(sK55)
    & ~ v2_struct_0(sK55) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK55,sK56,sK57,sK58,sK59])],[f3555,f8425,f8424,f8423,f8422,f8421])).

fof(f8421,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
                        & m1_pre_topc(X2,X3)
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
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
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK55,X1,X3,X2,k2_tmap_1(sK55,X1,X4,X3)),k2_tmap_1(sK55,X1,X4,X2))
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK55),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(sK55),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK55)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK55)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK55)
      & v2_pre_topc(sK55)
      & ~ v2_struct_0(sK55) ) ),
    introduced(choice_axiom,[])).

fof(f8422,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK55,X1,X3,X2,k2_tmap_1(sK55,X1,X4,X3)),k2_tmap_1(sK55,X1,X4,X2))
                    & m1_pre_topc(X2,X3)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK55),u1_struct_0(X1))))
                    & v1_funct_2(X4,u1_struct_0(sK55),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,sK55)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK55)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK56),k3_tmap_1(sK55,sK56,X3,X2,k2_tmap_1(sK55,sK56,X4,X3)),k2_tmap_1(sK55,sK56,X4,X2))
                  & m1_pre_topc(X2,X3)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK55),u1_struct_0(sK56))))
                  & v1_funct_2(X4,u1_struct_0(sK55),u1_struct_0(sK56))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,sK55)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK55)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK56)
      & v2_pre_topc(sK56)
      & ~ v2_struct_0(sK56) ) ),
    introduced(choice_axiom,[])).

fof(f8423,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK56),k3_tmap_1(sK55,sK56,X3,X2,k2_tmap_1(sK55,sK56,X4,X3)),k2_tmap_1(sK55,sK56,X4,X2))
                & m1_pre_topc(X2,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK55),u1_struct_0(sK56))))
                & v1_funct_2(X4,u1_struct_0(sK55),u1_struct_0(sK56))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,sK55)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK55)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ~ r2_funct_2(u1_struct_0(sK57),u1_struct_0(sK56),k3_tmap_1(sK55,sK56,X3,sK57,k2_tmap_1(sK55,sK56,X4,X3)),k2_tmap_1(sK55,sK56,X4,sK57))
              & m1_pre_topc(sK57,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK55),u1_struct_0(sK56))))
              & v1_funct_2(X4,u1_struct_0(sK55),u1_struct_0(sK56))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK55)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK57,sK55)
      & ~ v2_struct_0(sK57) ) ),
    introduced(choice_axiom,[])).

fof(f8424,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ~ r2_funct_2(u1_struct_0(sK57),u1_struct_0(sK56),k3_tmap_1(sK55,sK56,X3,sK57,k2_tmap_1(sK55,sK56,X4,X3)),k2_tmap_1(sK55,sK56,X4,sK57))
            & m1_pre_topc(sK57,X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK55),u1_struct_0(sK56))))
            & v1_funct_2(X4,u1_struct_0(sK55),u1_struct_0(sK56))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK55)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ~ r2_funct_2(u1_struct_0(sK57),u1_struct_0(sK56),k3_tmap_1(sK55,sK56,sK58,sK57,k2_tmap_1(sK55,sK56,X4,sK58)),k2_tmap_1(sK55,sK56,X4,sK57))
          & m1_pre_topc(sK57,sK58)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK55),u1_struct_0(sK56))))
          & v1_funct_2(X4,u1_struct_0(sK55),u1_struct_0(sK56))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK58,sK55)
      & ~ v2_struct_0(sK58) ) ),
    introduced(choice_axiom,[])).

fof(f8425,plain,
    ( ? [X4] :
        ( ~ r2_funct_2(u1_struct_0(sK57),u1_struct_0(sK56),k3_tmap_1(sK55,sK56,sK58,sK57,k2_tmap_1(sK55,sK56,X4,sK58)),k2_tmap_1(sK55,sK56,X4,sK57))
        & m1_pre_topc(sK57,sK58)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK55),u1_struct_0(sK56))))
        & v1_funct_2(X4,u1_struct_0(sK55),u1_struct_0(sK56))
        & v1_funct_1(X4) )
   => ( ~ r2_funct_2(u1_struct_0(sK57),u1_struct_0(sK56),k3_tmap_1(sK55,sK56,sK58,sK57,k2_tmap_1(sK55,sK56,sK59,sK58)),k2_tmap_1(sK55,sK56,sK59,sK57))
      & m1_pre_topc(sK57,sK58)
      & m1_subset_1(sK59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK55),u1_struct_0(sK56))))
      & v1_funct_2(sK59,u1_struct_0(sK55),u1_struct_0(sK56))
      & v1_funct_1(sK59) ) ),
    introduced(choice_axiom,[])).

fof(f3555,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3554])).

fof(f3554,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3430])).

fof(f3430,negated_conjecture,(
    ~ ! [X0] :
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
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( m1_pre_topc(X2,X3)
                         => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3429])).

fof(f3429,conjecture,(
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
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_tmap_1)).

fof(f11851,plain,(
    v1_funct_2(sK59,u1_struct_0(sK55),u1_struct_0(sK56)) ),
    inference(cnf_transformation,[],[f8426])).

fof(f11850,plain,(
    v1_funct_1(sK59) ),
    inference(cnf_transformation,[],[f8426])).

fof(f25794,plain,
    ( l1_struct_0(sK56)
    | ~ spl1387_8 ),
    inference(avatar_component_clause,[],[f25793])).

fof(f25793,plain,
    ( spl1387_8
  <=> l1_struct_0(sK56) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1387_8])])).

fof(f25790,plain,
    ( l1_struct_0(sK55)
    | ~ spl1387_7 ),
    inference(avatar_component_clause,[],[f25789])).

fof(f25789,plain,
    ( spl1387_7
  <=> l1_struct_0(sK55) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1387_7])])).

fof(f25833,plain,
    ( spl1387_5
    | ~ spl1387_7
    | ~ spl1387_8
    | ~ spl1387_9 ),
    inference(avatar_contradiction_clause,[],[f25831])).

fof(f25831,plain,
    ( $false
    | spl1387_5
    | ~ spl1387_7
    | ~ spl1387_8
    | ~ spl1387_9 ),
    inference(unit_resulting_resolution,[],[f25790,f25794,f11850,f11851,f11852,f25673,f25798,f19019])).

fof(f19019,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f8080])).

fof(f25673,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK55,sK56,sK59,sK58),u1_struct_0(sK58),u1_struct_0(sK56))
    | spl1387_5 ),
    inference(avatar_component_clause,[],[f25671])).

fof(f25671,plain,
    ( spl1387_5
  <=> v1_funct_2(k2_tmap_1(sK55,sK56,sK59,sK58),u1_struct_0(sK58),u1_struct_0(sK56)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1387_5])])).

fof(f25819,plain,(
    spl1387_9 ),
    inference(avatar_contradiction_clause,[],[f25817])).

fof(f25817,plain,
    ( $false
    | spl1387_9 ),
    inference(unit_resulting_resolution,[],[f11842,f11849,f25814,f12561])).

fof(f12561,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3895])).

fof(f3895,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1784])).

fof(f1784,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f25814,plain,
    ( ~ l1_pre_topc(sK58)
    | spl1387_9 ),
    inference(resolution,[],[f25799,f12466])).

fof(f12466,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3848])).

fof(f3848,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1782])).

fof(f1782,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f25799,plain,
    ( ~ l1_struct_0(sK58)
    | spl1387_9 ),
    inference(avatar_component_clause,[],[f25797])).

fof(f11849,plain,(
    m1_pre_topc(sK58,sK55) ),
    inference(cnf_transformation,[],[f8426])).

fof(f11842,plain,(
    l1_pre_topc(sK55) ),
    inference(cnf_transformation,[],[f8426])).

fof(f25812,plain,(
    spl1387_8 ),
    inference(avatar_contradiction_clause,[],[f25811])).

fof(f25811,plain,
    ( $false
    | spl1387_8 ),
    inference(subsumption_resolution,[],[f25809,f11845])).

fof(f11845,plain,(
    l1_pre_topc(sK56) ),
    inference(cnf_transformation,[],[f8426])).

fof(f25809,plain,
    ( ~ l1_pre_topc(sK56)
    | spl1387_8 ),
    inference(resolution,[],[f25795,f12466])).

fof(f25795,plain,
    ( ~ l1_struct_0(sK56)
    | spl1387_8 ),
    inference(avatar_component_clause,[],[f25793])).

fof(f25806,plain,(
    spl1387_7 ),
    inference(avatar_contradiction_clause,[],[f25805])).

fof(f25805,plain,
    ( $false
    | spl1387_7 ),
    inference(subsumption_resolution,[],[f25803,f11842])).

fof(f25803,plain,
    ( ~ l1_pre_topc(sK55)
    | spl1387_7 ),
    inference(resolution,[],[f25791,f12466])).

fof(f25791,plain,
    ( ~ l1_struct_0(sK55)
    | spl1387_7 ),
    inference(avatar_component_clause,[],[f25789])).

fof(f25800,plain,
    ( ~ spl1387_7
    | ~ spl1387_8
    | ~ spl1387_9
    | spl1387_4 ),
    inference(avatar_split_clause,[],[f25696,f25667,f25797,f25793,f25789])).

fof(f25667,plain,
    ( spl1387_4
  <=> v1_funct_1(k2_tmap_1(sK55,sK56,sK59,sK58)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1387_4])])).

fof(f25696,plain,
    ( ~ l1_struct_0(sK58)
    | ~ l1_struct_0(sK56)
    | ~ l1_struct_0(sK55)
    | spl1387_4 ),
    inference(subsumption_resolution,[],[f25695,f11850])).

fof(f25695,plain,
    ( ~ l1_struct_0(sK58)
    | ~ v1_funct_1(sK59)
    | ~ l1_struct_0(sK56)
    | ~ l1_struct_0(sK55)
    | spl1387_4 ),
    inference(subsumption_resolution,[],[f25694,f11851])).

fof(f25694,plain,
    ( ~ l1_struct_0(sK58)
    | ~ v1_funct_2(sK59,u1_struct_0(sK55),u1_struct_0(sK56))
    | ~ v1_funct_1(sK59)
    | ~ l1_struct_0(sK56)
    | ~ l1_struct_0(sK55)
    | spl1387_4 ),
    inference(subsumption_resolution,[],[f25680,f11852])).

fof(f25680,plain,
    ( ~ l1_struct_0(sK58)
    | ~ m1_subset_1(sK59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK55),u1_struct_0(sK56))))
    | ~ v1_funct_2(sK59,u1_struct_0(sK55),u1_struct_0(sK56))
    | ~ v1_funct_1(sK59)
    | ~ l1_struct_0(sK56)
    | ~ l1_struct_0(sK55)
    | spl1387_4 ),
    inference(resolution,[],[f25669,f19018])).

fof(f19018,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f8080])).

fof(f25669,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK55,sK56,sK59,sK58))
    | spl1387_4 ),
    inference(avatar_component_clause,[],[f25667])).

fof(f25678,plain,
    ( ~ spl1387_4
    | ~ spl1387_5
    | ~ spl1387_6 ),
    inference(avatar_split_clause,[],[f25532,f25675,f25671,f25667])).

fof(f25532,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK55,sK56,sK59,sK58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK58),u1_struct_0(sK56))))
    | ~ v1_funct_2(k2_tmap_1(sK55,sK56,sK59,sK58),u1_struct_0(sK58),u1_struct_0(sK56))
    | ~ v1_funct_1(k2_tmap_1(sK55,sK56,sK59,sK58)) ),
    inference(subsumption_resolution,[],[f25531,f25378])).

fof(f25378,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f20551])).

fof(f20551,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f19034])).

fof(f19034,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f11518])).

fof(f11518,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_funct_2(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_funct_2(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f8092])).

fof(f8092,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f8091])).

fof(f8091,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1561])).

fof(f1561,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(f25531,plain,
    ( ~ r2_funct_2(u1_struct_0(sK58),u1_struct_0(sK56),k2_tmap_1(sK55,sK56,sK59,sK58),k2_tmap_1(sK55,sK56,sK59,sK58))
    | ~ m1_subset_1(k2_tmap_1(sK55,sK56,sK59,sK58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK58),u1_struct_0(sK56))))
    | ~ v1_funct_2(k2_tmap_1(sK55,sK56,sK59,sK58),u1_struct_0(sK58),u1_struct_0(sK56))
    | ~ v1_funct_1(k2_tmap_1(sK55,sK56,sK59,sK58)) ),
    inference(subsumption_resolution,[],[f25530,f11840])).

fof(f11840,plain,(
    ~ v2_struct_0(sK55) ),
    inference(cnf_transformation,[],[f8426])).

fof(f25530,plain,
    ( ~ r2_funct_2(u1_struct_0(sK58),u1_struct_0(sK56),k2_tmap_1(sK55,sK56,sK59,sK58),k2_tmap_1(sK55,sK56,sK59,sK58))
    | ~ m1_subset_1(k2_tmap_1(sK55,sK56,sK59,sK58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK58),u1_struct_0(sK56))))
    | ~ v1_funct_2(k2_tmap_1(sK55,sK56,sK59,sK58),u1_struct_0(sK58),u1_struct_0(sK56))
    | ~ v1_funct_1(k2_tmap_1(sK55,sK56,sK59,sK58))
    | v2_struct_0(sK55) ),
    inference(subsumption_resolution,[],[f25529,f11841])).

fof(f11841,plain,(
    v2_pre_topc(sK55) ),
    inference(cnf_transformation,[],[f8426])).

fof(f25529,plain,
    ( ~ r2_funct_2(u1_struct_0(sK58),u1_struct_0(sK56),k2_tmap_1(sK55,sK56,sK59,sK58),k2_tmap_1(sK55,sK56,sK59,sK58))
    | ~ m1_subset_1(k2_tmap_1(sK55,sK56,sK59,sK58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK58),u1_struct_0(sK56))))
    | ~ v1_funct_2(k2_tmap_1(sK55,sK56,sK59,sK58),u1_struct_0(sK58),u1_struct_0(sK56))
    | ~ v1_funct_1(k2_tmap_1(sK55,sK56,sK59,sK58))
    | ~ v2_pre_topc(sK55)
    | v2_struct_0(sK55) ),
    inference(subsumption_resolution,[],[f25528,f11842])).

fof(f25528,plain,
    ( ~ r2_funct_2(u1_struct_0(sK58),u1_struct_0(sK56),k2_tmap_1(sK55,sK56,sK59,sK58),k2_tmap_1(sK55,sK56,sK59,sK58))
    | ~ m1_subset_1(k2_tmap_1(sK55,sK56,sK59,sK58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK58),u1_struct_0(sK56))))
    | ~ v1_funct_2(k2_tmap_1(sK55,sK56,sK59,sK58),u1_struct_0(sK58),u1_struct_0(sK56))
    | ~ v1_funct_1(k2_tmap_1(sK55,sK56,sK59,sK58))
    | ~ l1_pre_topc(sK55)
    | ~ v2_pre_topc(sK55)
    | v2_struct_0(sK55) ),
    inference(subsumption_resolution,[],[f25527,f11843])).

fof(f11843,plain,(
    ~ v2_struct_0(sK56) ),
    inference(cnf_transformation,[],[f8426])).

fof(f25527,plain,
    ( ~ r2_funct_2(u1_struct_0(sK58),u1_struct_0(sK56),k2_tmap_1(sK55,sK56,sK59,sK58),k2_tmap_1(sK55,sK56,sK59,sK58))
    | ~ m1_subset_1(k2_tmap_1(sK55,sK56,sK59,sK58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK58),u1_struct_0(sK56))))
    | ~ v1_funct_2(k2_tmap_1(sK55,sK56,sK59,sK58),u1_struct_0(sK58),u1_struct_0(sK56))
    | ~ v1_funct_1(k2_tmap_1(sK55,sK56,sK59,sK58))
    | v2_struct_0(sK56)
    | ~ l1_pre_topc(sK55)
    | ~ v2_pre_topc(sK55)
    | v2_struct_0(sK55) ),
    inference(subsumption_resolution,[],[f25526,f11844])).

fof(f11844,plain,(
    v2_pre_topc(sK56) ),
    inference(cnf_transformation,[],[f8426])).

fof(f25526,plain,
    ( ~ r2_funct_2(u1_struct_0(sK58),u1_struct_0(sK56),k2_tmap_1(sK55,sK56,sK59,sK58),k2_tmap_1(sK55,sK56,sK59,sK58))
    | ~ m1_subset_1(k2_tmap_1(sK55,sK56,sK59,sK58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK58),u1_struct_0(sK56))))
    | ~ v1_funct_2(k2_tmap_1(sK55,sK56,sK59,sK58),u1_struct_0(sK58),u1_struct_0(sK56))
    | ~ v1_funct_1(k2_tmap_1(sK55,sK56,sK59,sK58))
    | ~ v2_pre_topc(sK56)
    | v2_struct_0(sK56)
    | ~ l1_pre_topc(sK55)
    | ~ v2_pre_topc(sK55)
    | v2_struct_0(sK55) ),
    inference(subsumption_resolution,[],[f25525,f11845])).

fof(f25525,plain,
    ( ~ r2_funct_2(u1_struct_0(sK58),u1_struct_0(sK56),k2_tmap_1(sK55,sK56,sK59,sK58),k2_tmap_1(sK55,sK56,sK59,sK58))
    | ~ m1_subset_1(k2_tmap_1(sK55,sK56,sK59,sK58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK58),u1_struct_0(sK56))))
    | ~ v1_funct_2(k2_tmap_1(sK55,sK56,sK59,sK58),u1_struct_0(sK58),u1_struct_0(sK56))
    | ~ v1_funct_1(k2_tmap_1(sK55,sK56,sK59,sK58))
    | ~ l1_pre_topc(sK56)
    | ~ v2_pre_topc(sK56)
    | v2_struct_0(sK56)
    | ~ l1_pre_topc(sK55)
    | ~ v2_pre_topc(sK55)
    | v2_struct_0(sK55) ),
    inference(subsumption_resolution,[],[f25524,f11848])).

fof(f11848,plain,(
    ~ v2_struct_0(sK58) ),
    inference(cnf_transformation,[],[f8426])).

fof(f25524,plain,
    ( ~ r2_funct_2(u1_struct_0(sK58),u1_struct_0(sK56),k2_tmap_1(sK55,sK56,sK59,sK58),k2_tmap_1(sK55,sK56,sK59,sK58))
    | ~ m1_subset_1(k2_tmap_1(sK55,sK56,sK59,sK58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK58),u1_struct_0(sK56))))
    | ~ v1_funct_2(k2_tmap_1(sK55,sK56,sK59,sK58),u1_struct_0(sK58),u1_struct_0(sK56))
    | ~ v1_funct_1(k2_tmap_1(sK55,sK56,sK59,sK58))
    | v2_struct_0(sK58)
    | ~ l1_pre_topc(sK56)
    | ~ v2_pre_topc(sK56)
    | v2_struct_0(sK56)
    | ~ l1_pre_topc(sK55)
    | ~ v2_pre_topc(sK55)
    | v2_struct_0(sK55) ),
    inference(subsumption_resolution,[],[f25523,f11849])).

fof(f25523,plain,
    ( ~ r2_funct_2(u1_struct_0(sK58),u1_struct_0(sK56),k2_tmap_1(sK55,sK56,sK59,sK58),k2_tmap_1(sK55,sK56,sK59,sK58))
    | ~ m1_subset_1(k2_tmap_1(sK55,sK56,sK59,sK58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK58),u1_struct_0(sK56))))
    | ~ v1_funct_2(k2_tmap_1(sK55,sK56,sK59,sK58),u1_struct_0(sK58),u1_struct_0(sK56))
    | ~ v1_funct_1(k2_tmap_1(sK55,sK56,sK59,sK58))
    | ~ m1_pre_topc(sK58,sK55)
    | v2_struct_0(sK58)
    | ~ l1_pre_topc(sK56)
    | ~ v2_pre_topc(sK56)
    | v2_struct_0(sK56)
    | ~ l1_pre_topc(sK55)
    | ~ v2_pre_topc(sK55)
    | v2_struct_0(sK55) ),
    inference(subsumption_resolution,[],[f25522,f11846])).

fof(f11846,plain,(
    ~ v2_struct_0(sK57) ),
    inference(cnf_transformation,[],[f8426])).

fof(f25522,plain,
    ( ~ r2_funct_2(u1_struct_0(sK58),u1_struct_0(sK56),k2_tmap_1(sK55,sK56,sK59,sK58),k2_tmap_1(sK55,sK56,sK59,sK58))
    | ~ m1_subset_1(k2_tmap_1(sK55,sK56,sK59,sK58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK58),u1_struct_0(sK56))))
    | ~ v1_funct_2(k2_tmap_1(sK55,sK56,sK59,sK58),u1_struct_0(sK58),u1_struct_0(sK56))
    | ~ v1_funct_1(k2_tmap_1(sK55,sK56,sK59,sK58))
    | v2_struct_0(sK57)
    | ~ m1_pre_topc(sK58,sK55)
    | v2_struct_0(sK58)
    | ~ l1_pre_topc(sK56)
    | ~ v2_pre_topc(sK56)
    | v2_struct_0(sK56)
    | ~ l1_pre_topc(sK55)
    | ~ v2_pre_topc(sK55)
    | v2_struct_0(sK55) ),
    inference(subsumption_resolution,[],[f25521,f11847])).

fof(f11847,plain,(
    m1_pre_topc(sK57,sK55) ),
    inference(cnf_transformation,[],[f8426])).

fof(f25521,plain,
    ( ~ r2_funct_2(u1_struct_0(sK58),u1_struct_0(sK56),k2_tmap_1(sK55,sK56,sK59,sK58),k2_tmap_1(sK55,sK56,sK59,sK58))
    | ~ m1_subset_1(k2_tmap_1(sK55,sK56,sK59,sK58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK58),u1_struct_0(sK56))))
    | ~ v1_funct_2(k2_tmap_1(sK55,sK56,sK59,sK58),u1_struct_0(sK58),u1_struct_0(sK56))
    | ~ v1_funct_1(k2_tmap_1(sK55,sK56,sK59,sK58))
    | ~ m1_pre_topc(sK57,sK55)
    | v2_struct_0(sK57)
    | ~ m1_pre_topc(sK58,sK55)
    | v2_struct_0(sK58)
    | ~ l1_pre_topc(sK56)
    | ~ v2_pre_topc(sK56)
    | v2_struct_0(sK56)
    | ~ l1_pre_topc(sK55)
    | ~ v2_pre_topc(sK55)
    | v2_struct_0(sK55) ),
    inference(subsumption_resolution,[],[f25520,f11850])).

fof(f25520,plain,
    ( ~ r2_funct_2(u1_struct_0(sK58),u1_struct_0(sK56),k2_tmap_1(sK55,sK56,sK59,sK58),k2_tmap_1(sK55,sK56,sK59,sK58))
    | ~ m1_subset_1(k2_tmap_1(sK55,sK56,sK59,sK58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK58),u1_struct_0(sK56))))
    | ~ v1_funct_2(k2_tmap_1(sK55,sK56,sK59,sK58),u1_struct_0(sK58),u1_struct_0(sK56))
    | ~ v1_funct_1(k2_tmap_1(sK55,sK56,sK59,sK58))
    | ~ v1_funct_1(sK59)
    | ~ m1_pre_topc(sK57,sK55)
    | v2_struct_0(sK57)
    | ~ m1_pre_topc(sK58,sK55)
    | v2_struct_0(sK58)
    | ~ l1_pre_topc(sK56)
    | ~ v2_pre_topc(sK56)
    | v2_struct_0(sK56)
    | ~ l1_pre_topc(sK55)
    | ~ v2_pre_topc(sK55)
    | v2_struct_0(sK55) ),
    inference(subsumption_resolution,[],[f25519,f11851])).

fof(f25519,plain,
    ( ~ r2_funct_2(u1_struct_0(sK58),u1_struct_0(sK56),k2_tmap_1(sK55,sK56,sK59,sK58),k2_tmap_1(sK55,sK56,sK59,sK58))
    | ~ m1_subset_1(k2_tmap_1(sK55,sK56,sK59,sK58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK58),u1_struct_0(sK56))))
    | ~ v1_funct_2(k2_tmap_1(sK55,sK56,sK59,sK58),u1_struct_0(sK58),u1_struct_0(sK56))
    | ~ v1_funct_1(k2_tmap_1(sK55,sK56,sK59,sK58))
    | ~ v1_funct_2(sK59,u1_struct_0(sK55),u1_struct_0(sK56))
    | ~ v1_funct_1(sK59)
    | ~ m1_pre_topc(sK57,sK55)
    | v2_struct_0(sK57)
    | ~ m1_pre_topc(sK58,sK55)
    | v2_struct_0(sK58)
    | ~ l1_pre_topc(sK56)
    | ~ v2_pre_topc(sK56)
    | v2_struct_0(sK56)
    | ~ l1_pre_topc(sK55)
    | ~ v2_pre_topc(sK55)
    | v2_struct_0(sK55) ),
    inference(subsumption_resolution,[],[f25518,f11852])).

fof(f25518,plain,
    ( ~ r2_funct_2(u1_struct_0(sK58),u1_struct_0(sK56),k2_tmap_1(sK55,sK56,sK59,sK58),k2_tmap_1(sK55,sK56,sK59,sK58))
    | ~ m1_subset_1(k2_tmap_1(sK55,sK56,sK59,sK58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK58),u1_struct_0(sK56))))
    | ~ v1_funct_2(k2_tmap_1(sK55,sK56,sK59,sK58),u1_struct_0(sK58),u1_struct_0(sK56))
    | ~ v1_funct_1(k2_tmap_1(sK55,sK56,sK59,sK58))
    | ~ m1_subset_1(sK59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK55),u1_struct_0(sK56))))
    | ~ v1_funct_2(sK59,u1_struct_0(sK55),u1_struct_0(sK56))
    | ~ v1_funct_1(sK59)
    | ~ m1_pre_topc(sK57,sK55)
    | v2_struct_0(sK57)
    | ~ m1_pre_topc(sK58,sK55)
    | v2_struct_0(sK58)
    | ~ l1_pre_topc(sK56)
    | ~ v2_pre_topc(sK56)
    | v2_struct_0(sK56)
    | ~ l1_pre_topc(sK55)
    | ~ v2_pre_topc(sK55)
    | v2_struct_0(sK55) ),
    inference(subsumption_resolution,[],[f25517,f11853])).

fof(f11853,plain,(
    m1_pre_topc(sK57,sK58) ),
    inference(cnf_transformation,[],[f8426])).

fof(f25517,plain,
    ( ~ m1_pre_topc(sK57,sK58)
    | ~ r2_funct_2(u1_struct_0(sK58),u1_struct_0(sK56),k2_tmap_1(sK55,sK56,sK59,sK58),k2_tmap_1(sK55,sK56,sK59,sK58))
    | ~ m1_subset_1(k2_tmap_1(sK55,sK56,sK59,sK58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK58),u1_struct_0(sK56))))
    | ~ v1_funct_2(k2_tmap_1(sK55,sK56,sK59,sK58),u1_struct_0(sK58),u1_struct_0(sK56))
    | ~ v1_funct_1(k2_tmap_1(sK55,sK56,sK59,sK58))
    | ~ m1_subset_1(sK59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK55),u1_struct_0(sK56))))
    | ~ v1_funct_2(sK59,u1_struct_0(sK55),u1_struct_0(sK56))
    | ~ v1_funct_1(sK59)
    | ~ m1_pre_topc(sK57,sK55)
    | v2_struct_0(sK57)
    | ~ m1_pre_topc(sK58,sK55)
    | v2_struct_0(sK58)
    | ~ l1_pre_topc(sK56)
    | ~ v2_pre_topc(sK56)
    | v2_struct_0(sK56)
    | ~ l1_pre_topc(sK55)
    | ~ v2_pre_topc(sK55)
    | v2_struct_0(sK55) ),
    inference(resolution,[],[f14072,f11854])).

fof(f11854,plain,(
    ~ r2_funct_2(u1_struct_0(sK57),u1_struct_0(sK56),k3_tmap_1(sK55,sK56,sK58,sK57,k2_tmap_1(sK55,sK56,sK59,sK58)),k2_tmap_1(sK55,sK56,sK59,sK57)) ),
    inference(cnf_transformation,[],[f8426])).

fof(f14072,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3))
      | ~ m1_pre_topc(X3,X2)
      | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
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
    inference(cnf_transformation,[],[f4841])).

fof(f4841,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3))
                          | ~ m1_pre_topc(X3,X2)
                          | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
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
    inference(flattening,[],[f4840])).

fof(f4840,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3))
                          | ~ m1_pre_topc(X3,X2)
                          | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
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
    inference(ennf_transformation,[],[f3428])).

fof(f3428,axiom,(
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
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                         => ( ( m1_pre_topc(X3,X2)
                              & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)) )
                           => r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tmap_1)).
%------------------------------------------------------------------------------
