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
% DateTime   : Thu Dec  3 13:19:50 EST 2020

% Result     : Theorem 2.16s
% Output     : Refutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :  497 (669997 expanded)
%              Number of leaves         :   18 (236972 expanded)
%              Depth                    :  343
%              Number of atoms          : 4998 (11194056 expanded)
%              Number of equality atoms :  188 (12572 expanded)
%              Maximal formula depth    :   28 (  11 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f728,plain,(
    $false ),
    inference(subsumption_resolution,[],[f727,f134])).

fof(f134,plain,(
    r1_tsep_1(sK7,sK8) ),
    inference(subsumption_resolution,[],[f133,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2)))))
            | ~ v5_pre_topc(sK10(X0,X1,X2),k1_tsep_1(X2,X1,X0),sK9(X0,X1,X2))
            | ~ v1_funct_2(sK10(X0,X1,X2),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2)))
            | ~ v1_funct_1(sK10(X0,X1,X2)) )
          & m1_subset_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK9(X0,X1,X2)))))
          & v5_pre_topc(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)),X0,sK9(X0,X1,X2))
          & v1_funct_2(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)),u1_struct_0(X0),u1_struct_0(sK9(X0,X1,X2)))
          & v1_funct_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)))
          & m1_subset_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK9(X0,X1,X2)))))
          & v5_pre_topc(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)),X1,sK9(X0,X1,X2))
          & v1_funct_2(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)),u1_struct_0(X1),u1_struct_0(sK9(X0,X1,X2)))
          & v1_funct_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)))
          & m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2)))))
          & v1_funct_2(sK10(X0,X1,X2),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2)))
          & v1_funct_1(sK10(X0,X1,X2))
          & l1_pre_topc(sK9(X0,X1,X2))
          & v2_pre_topc(sK9(X0,X1,X2))
          & ~ v2_struct_0(sK9(X0,X1,X2)) )
        | ~ r1_tsep_1(X1,X0) )
      & ( ( ! [X5] :
              ( ! [X6] :
                  ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X5))))
                    & v5_pre_topc(X6,k1_tsep_1(X2,X1,X0),X5)
                    & v1_funct_2(X6,u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X5))
                    & v1_funct_1(X6) )
                  | ~ m1_subset_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X0,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X5))))
                  | ~ v5_pre_topc(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X0,X6),X0,X5)
                  | ~ v1_funct_2(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X0,X6),u1_struct_0(X0),u1_struct_0(X5))
                  | ~ v1_funct_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X0,X6))
                  | ~ m1_subset_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X1,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X5))))
                  | ~ v5_pre_topc(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X1,X6),X1,X5)
                  | ~ v1_funct_2(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X1,X6),u1_struct_0(X1),u1_struct_0(X5))
                  | ~ v1_funct_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X1,X6))
                  | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X5))))
                  | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X5))
                  | ~ v1_funct_1(X6) )
              | ~ l1_pre_topc(X5)
              | ~ v2_pre_topc(X5)
              | v2_struct_0(X5) )
          & r1_tsep_1(X1,X0) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f44,f46,f45])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ? [X4] :
              ( ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X3))))
                | ~ v5_pre_topc(X4,k1_tsep_1(X2,X1,X0),X3)
                | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X3))
                | ~ v1_funct_1(X4) )
              & m1_subset_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X0,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
              & v5_pre_topc(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X0,X4),X0,X3)
              & v1_funct_2(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X0,X4),u1_struct_0(X0),u1_struct_0(X3))
              & v1_funct_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X0,X4))
              & m1_subset_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
              & v5_pre_topc(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X1,X4),X1,X3)
              & v1_funct_2(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X1,X4),u1_struct_0(X1),u1_struct_0(X3))
              & v1_funct_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X1,X4))
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X3))))
              & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X3))
              & v1_funct_1(X4) )
          & l1_pre_topc(X3)
          & v2_pre_topc(X3)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2)))))
              | ~ v5_pre_topc(X4,k1_tsep_1(X2,X1,X0),sK9(X0,X1,X2))
              | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2)))
              | ~ v1_funct_1(X4) )
            & m1_subset_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK9(X0,X1,X2)))))
            & v5_pre_topc(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,X4),X0,sK9(X0,X1,X2))
            & v1_funct_2(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,X4),u1_struct_0(X0),u1_struct_0(sK9(X0,X1,X2)))
            & v1_funct_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,X4))
            & m1_subset_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK9(X0,X1,X2)))))
            & v5_pre_topc(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,X4),X1,sK9(X0,X1,X2))
            & v1_funct_2(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,X4),u1_struct_0(X1),u1_struct_0(sK9(X0,X1,X2)))
            & v1_funct_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,X4))
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2)))))
            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2)))
            & v1_funct_1(X4) )
        & l1_pre_topc(sK9(X0,X1,X2))
        & v2_pre_topc(sK9(X0,X1,X2))
        & ~ v2_struct_0(sK9(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2)))))
            | ~ v5_pre_topc(X4,k1_tsep_1(X2,X1,X0),sK9(X0,X1,X2))
            | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2)))
            | ~ v1_funct_1(X4) )
          & m1_subset_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK9(X0,X1,X2)))))
          & v5_pre_topc(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,X4),X0,sK9(X0,X1,X2))
          & v1_funct_2(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,X4),u1_struct_0(X0),u1_struct_0(sK9(X0,X1,X2)))
          & v1_funct_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,X4))
          & m1_subset_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK9(X0,X1,X2)))))
          & v5_pre_topc(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,X4),X1,sK9(X0,X1,X2))
          & v1_funct_2(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,X4),u1_struct_0(X1),u1_struct_0(sK9(X0,X1,X2)))
          & v1_funct_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,X4))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2)))))
          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2)))
          & v1_funct_1(X4) )
     => ( ( ~ m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2)))))
          | ~ v5_pre_topc(sK10(X0,X1,X2),k1_tsep_1(X2,X1,X0),sK9(X0,X1,X2))
          | ~ v1_funct_2(sK10(X0,X1,X2),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2)))
          | ~ v1_funct_1(sK10(X0,X1,X2)) )
        & m1_subset_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK9(X0,X1,X2)))))
        & v5_pre_topc(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)),X0,sK9(X0,X1,X2))
        & v1_funct_2(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)),u1_struct_0(X0),u1_struct_0(sK9(X0,X1,X2)))
        & v1_funct_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)))
        & m1_subset_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK9(X0,X1,X2)))))
        & v5_pre_topc(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)),X1,sK9(X0,X1,X2))
        & v1_funct_2(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)),u1_struct_0(X1),u1_struct_0(sK9(X0,X1,X2)))
        & v1_funct_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)))
        & m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2)))))
        & v1_funct_2(sK10(X0,X1,X2),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2)))
        & v1_funct_1(sK10(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ? [X4] :
                ( ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X3))))
                  | ~ v5_pre_topc(X4,k1_tsep_1(X2,X1,X0),X3)
                  | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X3))
                  | ~ v1_funct_1(X4) )
                & m1_subset_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X0,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                & v5_pre_topc(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X0,X4),X0,X3)
                & v1_funct_2(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X0,X4),u1_struct_0(X0),u1_struct_0(X3))
                & v1_funct_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X0,X4))
                & m1_subset_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                & v5_pre_topc(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X1,X4),X1,X3)
                & v1_funct_2(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X1,X4),u1_struct_0(X1),u1_struct_0(X3))
                & v1_funct_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X1,X4))
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X3))))
                & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X3))
                & v1_funct_1(X4) )
            & l1_pre_topc(X3)
            & v2_pre_topc(X3)
            & ~ v2_struct_0(X3) )
        | ~ r1_tsep_1(X1,X0) )
      & ( ( ! [X5] :
              ( ! [X6] :
                  ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X5))))
                    & v5_pre_topc(X6,k1_tsep_1(X2,X1,X0),X5)
                    & v1_funct_2(X6,u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X5))
                    & v1_funct_1(X6) )
                  | ~ m1_subset_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X0,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X5))))
                  | ~ v5_pre_topc(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X0,X6),X0,X5)
                  | ~ v1_funct_2(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X0,X6),u1_struct_0(X0),u1_struct_0(X5))
                  | ~ v1_funct_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X0,X6))
                  | ~ m1_subset_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X1,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X5))))
                  | ~ v5_pre_topc(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X1,X6),X1,X5)
                  | ~ v1_funct_2(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X1,X6),u1_struct_0(X1),u1_struct_0(X5))
                  | ~ v1_funct_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X1,X6))
                  | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X5))))
                  | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X5))
                  | ~ v1_funct_1(X6) )
              | ~ l1_pre_topc(X5)
              | ~ v2_pre_topc(X5)
              | v2_struct_0(X5) )
          & r1_tsep_1(X1,X0) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ( sP1(X2,X1,X0)
        | ? [X3] :
            ( ? [X4] :
                ( ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                  | ~ v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3)
                  | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                  | ~ v1_funct_1(X4) )
                & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3)
                & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3))
                & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4))
                & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3)
                & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3))
                & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4))
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                & v1_funct_1(X4) )
            & l1_pre_topc(X3)
            & v2_pre_topc(X3)
            & ~ v2_struct_0(X3) )
        | ~ r1_tsep_1(X1,X2) )
      & ( ( ! [X3] :
              ( ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                    & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3)
                    & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                    & v1_funct_1(X4) )
                  | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                  | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3)
                  | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3))
                  | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4))
                  | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                  | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3)
                  | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3))
                  | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4))
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                  | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                  | ~ v1_funct_1(X4) )
              | ~ l1_pre_topc(X3)
              | ~ v2_pre_topc(X3)
              | v2_struct_0(X3) )
          & r1_tsep_1(X1,X2) )
        | ~ sP1(X2,X1,X0) ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ( sP1(X2,X1,X0)
        | ? [X3] :
            ( ? [X4] :
                ( ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                  | ~ v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3)
                  | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                  | ~ v1_funct_1(X4) )
                & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3)
                & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3))
                & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4))
                & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3)
                & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3))
                & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4))
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                & v1_funct_1(X4) )
            & l1_pre_topc(X3)
            & v2_pre_topc(X3)
            & ~ v2_struct_0(X3) )
        | ~ r1_tsep_1(X1,X2) )
      & ( ( ! [X3] :
              ( ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                    & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3)
                    & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                    & v1_funct_1(X4) )
                  | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                  | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3)
                  | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3))
                  | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4))
                  | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                  | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3)
                  | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3))
                  | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4))
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                  | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                  | ~ v1_funct_1(X4) )
              | ~ l1_pre_topc(X3)
              | ~ v2_pre_topc(X3)
              | v2_struct_0(X3) )
          & r1_tsep_1(X1,X2) )
        | ~ sP1(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( sP1(X2,X1,X0)
    <=> ( ! [X3] :
            ( ! [X4] :
                ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                  & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3)
                  & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                  & v1_funct_1(X4) )
                | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3)
                | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3))
                | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4))
                | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3)
                | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3))
                | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4))
                | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                | ~ v1_funct_1(X4) )
            | ~ l1_pre_topc(X3)
            | ~ v2_pre_topc(X3)
            | v2_struct_0(X3) )
        & r1_tsep_1(X1,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f133,plain,
    ( sP1(sK8,sK7,sK6)
    | r1_tsep_1(sK7,sK8) ),
    inference(subsumption_resolution,[],[f132,f73])).

fof(f73,plain,(
    ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ( ~ sP0(sK8,sK7,sK6)
      | ~ r3_tsep_1(sK6,sK7,sK8) )
    & ( sP0(sK8,sK7,sK6)
      | r3_tsep_1(sK6,sK7,sK8) )
    & m1_pre_topc(sK8,sK6)
    & ~ v2_struct_0(sK8)
    & m1_pre_topc(sK7,sK6)
    & ~ v2_struct_0(sK7)
    & l1_pre_topc(sK6)
    & v2_pre_topc(sK6)
    & ~ v2_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f36,f39,f38,f37])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ sP0(X2,X1,X0)
                  | ~ r3_tsep_1(X0,X1,X2) )
                & ( sP0(X2,X1,X0)
                  | r3_tsep_1(X0,X1,X2) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ sP0(X2,X1,sK6)
                | ~ r3_tsep_1(sK6,X1,X2) )
              & ( sP0(X2,X1,sK6)
                | r3_tsep_1(sK6,X1,X2) )
              & m1_pre_topc(X2,sK6)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK6)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK6)
      & v2_pre_topc(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ sP0(X2,X1,sK6)
              | ~ r3_tsep_1(sK6,X1,X2) )
            & ( sP0(X2,X1,sK6)
              | r3_tsep_1(sK6,X1,X2) )
            & m1_pre_topc(X2,sK6)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK6)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( ~ sP0(X2,sK7,sK6)
            | ~ r3_tsep_1(sK6,sK7,X2) )
          & ( sP0(X2,sK7,sK6)
            | r3_tsep_1(sK6,sK7,X2) )
          & m1_pre_topc(X2,sK6)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK7,sK6)
      & ~ v2_struct_0(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X2] :
        ( ( ~ sP0(X2,sK7,sK6)
          | ~ r3_tsep_1(sK6,sK7,X2) )
        & ( sP0(X2,sK7,sK6)
          | r3_tsep_1(sK6,sK7,X2) )
        & m1_pre_topc(X2,sK6)
        & ~ v2_struct_0(X2) )
   => ( ( ~ sP0(sK8,sK7,sK6)
        | ~ r3_tsep_1(sK6,sK7,sK8) )
      & ( sP0(sK8,sK7,sK6)
        | r3_tsep_1(sK6,sK7,sK8) )
      & m1_pre_topc(sK8,sK6)
      & ~ v2_struct_0(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ sP0(X2,X1,X0)
                | ~ r3_tsep_1(X0,X1,X2) )
              & ( sP0(X2,X1,X0)
                | r3_tsep_1(X0,X1,X2) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ sP0(X2,X1,X0)
                | ~ r3_tsep_1(X0,X1,X2) )
              & ( sP0(X2,X1,X0)
                | r3_tsep_1(X0,X1,X2) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_tsep_1(X0,X1,X2)
              <~> sP0(X2,X1,X0) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f10,f23])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( sP0(X2,X1,X0)
    <=> ( ! [X3] :
            ( ! [X4] :
                ( ! [X5] :
                    ( ( m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                      & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3)
                      & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                      & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)) )
                    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                    | ~ v5_pre_topc(X5,X2,X3)
                    | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                    | ~ v1_funct_1(X5) )
                | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                | ~ v5_pre_topc(X4,X1,X3)
                | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                | ~ v1_funct_1(X4) )
            | ~ l1_pre_topc(X3)
            | ~ v2_pre_topc(X3)
            | v2_struct_0(X3) )
        & r1_tsep_1(X1,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_tsep_1(X0,X1,X2)
              <~> ( ! [X3] :
                      ( ! [X4] :
                          ( ! [X5] :
                              ( ( m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                                & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3)
                                & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                                & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)) )
                              | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                              | ~ v5_pre_topc(X5,X2,X3)
                              | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                              | ~ v1_funct_1(X5) )
                          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          | ~ v5_pre_topc(X4,X1,X3)
                          | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                          | ~ v1_funct_1(X4) )
                      | ~ l1_pre_topc(X3)
                      | ~ v2_pre_topc(X3)
                      | v2_struct_0(X3) )
                  & r1_tsep_1(X1,X2) ) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_tsep_1(X0,X1,X2)
              <~> ( ! [X3] :
                      ( ! [X4] :
                          ( ! [X5] :
                              ( ( m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                                & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3)
                                & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                                & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)) )
                              | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                              | ~ v5_pre_topc(X5,X2,X3)
                              | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                              | ~ v1_funct_1(X5) )
                          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          | ~ v5_pre_topc(X4,X1,X3)
                          | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                          | ~ v1_funct_1(X4) )
                      | ~ l1_pre_topc(X3)
                      | ~ v2_pre_topc(X3)
                      | v2_struct_0(X3) )
                  & r1_tsep_1(X1,X2) ) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
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
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( r3_tsep_1(X0,X1,X2)
                <=> ( ! [X3] :
                        ( ( l1_pre_topc(X3)
                          & v2_pre_topc(X3)
                          & ~ v2_struct_0(X3) )
                       => ! [X4] :
                            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                              & v5_pre_topc(X4,X1,X3)
                              & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                              & v1_funct_1(X4) )
                           => ! [X5] :
                                ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                                  & v5_pre_topc(X5,X2,X3)
                                  & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                                  & v1_funct_1(X5) )
                               => ( m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                                  & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3)
                                  & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                                  & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)) ) ) ) )
                    & r1_tsep_1(X1,X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
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
             => ( r3_tsep_1(X0,X1,X2)
              <=> ( ! [X3] :
                      ( ( l1_pre_topc(X3)
                        & v2_pre_topc(X3)
                        & ~ v2_struct_0(X3) )
                     => ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                            & v5_pre_topc(X4,X1,X3)
                            & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                            & v1_funct_1(X4) )
                         => ! [X5] :
                              ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                                & v5_pre_topc(X5,X2,X3)
                                & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                                & v1_funct_1(X5) )
                             => ( m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                                & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3)
                                & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                                & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)) ) ) ) )
                  & r1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_tmap_1)).

fof(f132,plain,
    ( v2_struct_0(sK8)
    | sP1(sK8,sK7,sK6)
    | r1_tsep_1(sK7,sK8) ),
    inference(subsumption_resolution,[],[f131,f74])).

fof(f74,plain,(
    m1_pre_topc(sK8,sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f131,plain,
    ( ~ m1_pre_topc(sK8,sK6)
    | v2_struct_0(sK8)
    | sP1(sK8,sK7,sK6)
    | r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f128,f115])).

fof(f115,plain,
    ( r3_tsep_1(sK6,sK7,sK8)
    | r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f75,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ~ m1_subset_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),sK5(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2)))))
            | ~ v5_pre_topc(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),sK5(X0,X1,X2)),k1_tsep_1(X2,X1,X0),sK3(X0,X1,X2))
            | ~ v1_funct_2(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),sK5(X0,X1,X2)),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2)))
            | ~ v1_funct_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),sK5(X0,X1,X2))) )
          & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2)))))
          & v5_pre_topc(sK5(X0,X1,X2),X0,sK3(X0,X1,X2))
          & v1_funct_2(sK5(X0,X1,X2),u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2)))
          & v1_funct_1(sK5(X0,X1,X2))
          & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3(X0,X1,X2)))))
          & v5_pre_topc(sK4(X0,X1,X2),X1,sK3(X0,X1,X2))
          & v1_funct_2(sK4(X0,X1,X2),u1_struct_0(X1),u1_struct_0(sK3(X0,X1,X2)))
          & v1_funct_1(sK4(X0,X1,X2))
          & l1_pre_topc(sK3(X0,X1,X2))
          & v2_pre_topc(sK3(X0,X1,X2))
          & ~ v2_struct_0(sK3(X0,X1,X2)) )
        | ~ r1_tsep_1(X1,X0) )
      & ( ( ! [X6] :
              ( ! [X7] :
                  ( ! [X8] :
                      ( ( m1_subset_1(k10_tmap_1(X2,X6,X1,X0,X7,X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X6))))
                        & v5_pre_topc(k10_tmap_1(X2,X6,X1,X0,X7,X8),k1_tsep_1(X2,X1,X0),X6)
                        & v1_funct_2(k10_tmap_1(X2,X6,X1,X0,X7,X8),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X6))
                        & v1_funct_1(k10_tmap_1(X2,X6,X1,X0,X7,X8)) )
                      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X6))))
                      | ~ v5_pre_topc(X8,X0,X6)
                      | ~ v1_funct_2(X8,u1_struct_0(X0),u1_struct_0(X6))
                      | ~ v1_funct_1(X8) )
                  | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X6))))
                  | ~ v5_pre_topc(X7,X1,X6)
                  | ~ v1_funct_2(X7,u1_struct_0(X1),u1_struct_0(X6))
                  | ~ v1_funct_1(X7) )
              | ~ l1_pre_topc(X6)
              | ~ v2_pre_topc(X6)
              | v2_struct_0(X6) )
          & r1_tsep_1(X1,X0) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f30,f33,f32,f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ~ m1_subset_1(k10_tmap_1(X2,X3,X1,X0,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X3))))
                    | ~ v5_pre_topc(k10_tmap_1(X2,X3,X1,X0,X4,X5),k1_tsep_1(X2,X1,X0),X3)
                    | ~ v1_funct_2(k10_tmap_1(X2,X3,X1,X0,X4,X5),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X3))
                    | ~ v1_funct_1(k10_tmap_1(X2,X3,X1,X0,X4,X5)) )
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                  & v5_pre_topc(X5,X0,X3)
                  & v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X3))
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
              & v5_pre_topc(X4,X1,X3)
              & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
              & v1_funct_1(X4) )
          & l1_pre_topc(X3)
          & v2_pre_topc(X3)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ( ~ m1_subset_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2)))))
                  | ~ v5_pre_topc(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,X4,X5),k1_tsep_1(X2,X1,X0),sK3(X0,X1,X2))
                  | ~ v1_funct_2(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,X4,X5),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2)))
                  | ~ v1_funct_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,X4,X5)) )
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2)))))
                & v5_pre_topc(X5,X0,sK3(X0,X1,X2))
                & v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2)))
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3(X0,X1,X2)))))
            & v5_pre_topc(X4,X1,sK3(X0,X1,X2))
            & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(sK3(X0,X1,X2)))
            & v1_funct_1(X4) )
        & l1_pre_topc(sK3(X0,X1,X2))
        & v2_pre_topc(sK3(X0,X1,X2))
        & ~ v2_struct_0(sK3(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( ? [X5] :
              ( ( ~ m1_subset_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2)))))
                | ~ v5_pre_topc(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,X4,X5),k1_tsep_1(X2,X1,X0),sK3(X0,X1,X2))
                | ~ v1_funct_2(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,X4,X5),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2)))
                | ~ v1_funct_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,X4,X5)) )
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2)))))
              & v5_pre_topc(X5,X0,sK3(X0,X1,X2))
              & v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2)))
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3(X0,X1,X2)))))
          & v5_pre_topc(X4,X1,sK3(X0,X1,X2))
          & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(sK3(X0,X1,X2)))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ( ~ m1_subset_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2)))))
              | ~ v5_pre_topc(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),X5),k1_tsep_1(X2,X1,X0),sK3(X0,X1,X2))
              | ~ v1_funct_2(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),X5),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2)))
              | ~ v1_funct_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),X5)) )
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2)))))
            & v5_pre_topc(X5,X0,sK3(X0,X1,X2))
            & v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2)))
            & v1_funct_1(X5) )
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3(X0,X1,X2)))))
        & v5_pre_topc(sK4(X0,X1,X2),X1,sK3(X0,X1,X2))
        & v1_funct_2(sK4(X0,X1,X2),u1_struct_0(X1),u1_struct_0(sK3(X0,X1,X2)))
        & v1_funct_1(sK4(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ( ~ m1_subset_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2)))))
            | ~ v5_pre_topc(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),X5),k1_tsep_1(X2,X1,X0),sK3(X0,X1,X2))
            | ~ v1_funct_2(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),X5),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2)))
            | ~ v1_funct_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),X5)) )
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2)))))
          & v5_pre_topc(X5,X0,sK3(X0,X1,X2))
          & v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2)))
          & v1_funct_1(X5) )
     => ( ( ~ m1_subset_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),sK5(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2)))))
          | ~ v5_pre_topc(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),sK5(X0,X1,X2)),k1_tsep_1(X2,X1,X0),sK3(X0,X1,X2))
          | ~ v1_funct_2(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),sK5(X0,X1,X2)),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2)))
          | ~ v1_funct_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),sK5(X0,X1,X2))) )
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2)))))
        & v5_pre_topc(sK5(X0,X1,X2),X0,sK3(X0,X1,X2))
        & v1_funct_2(sK5(X0,X1,X2),u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2)))
        & v1_funct_1(sK5(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ~ m1_subset_1(k10_tmap_1(X2,X3,X1,X0,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X3))))
                      | ~ v5_pre_topc(k10_tmap_1(X2,X3,X1,X0,X4,X5),k1_tsep_1(X2,X1,X0),X3)
                      | ~ v1_funct_2(k10_tmap_1(X2,X3,X1,X0,X4,X5),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X3))
                      | ~ v1_funct_1(k10_tmap_1(X2,X3,X1,X0,X4,X5)) )
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                    & v5_pre_topc(X5,X0,X3)
                    & v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X3))
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                & v5_pre_topc(X4,X1,X3)
                & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                & v1_funct_1(X4) )
            & l1_pre_topc(X3)
            & v2_pre_topc(X3)
            & ~ v2_struct_0(X3) )
        | ~ r1_tsep_1(X1,X0) )
      & ( ( ! [X6] :
              ( ! [X7] :
                  ( ! [X8] :
                      ( ( m1_subset_1(k10_tmap_1(X2,X6,X1,X0,X7,X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X6))))
                        & v5_pre_topc(k10_tmap_1(X2,X6,X1,X0,X7,X8),k1_tsep_1(X2,X1,X0),X6)
                        & v1_funct_2(k10_tmap_1(X2,X6,X1,X0,X7,X8),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X6))
                        & v1_funct_1(k10_tmap_1(X2,X6,X1,X0,X7,X8)) )
                      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X6))))
                      | ~ v5_pre_topc(X8,X0,X6)
                      | ~ v1_funct_2(X8,u1_struct_0(X0),u1_struct_0(X6))
                      | ~ v1_funct_1(X8) )
                  | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X6))))
                  | ~ v5_pre_topc(X7,X1,X6)
                  | ~ v1_funct_2(X7,u1_struct_0(X1),u1_struct_0(X6))
                  | ~ v1_funct_1(X7) )
              | ~ l1_pre_topc(X6)
              | ~ v2_pre_topc(X6)
              | v2_struct_0(X6) )
          & r1_tsep_1(X1,X0) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ( sP0(X2,X1,X0)
        | ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ~ m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                      | ~ v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3)
                      | ~ v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                      | ~ v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)) )
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                    & v5_pre_topc(X5,X2,X3)
                    & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                & v5_pre_topc(X4,X1,X3)
                & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                & v1_funct_1(X4) )
            & l1_pre_topc(X3)
            & v2_pre_topc(X3)
            & ~ v2_struct_0(X3) )
        | ~ r1_tsep_1(X1,X2) )
      & ( ( ! [X3] :
              ( ! [X4] :
                  ( ! [X5] :
                      ( ( m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                        & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3)
                        & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                        & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)) )
                      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                      | ~ v5_pre_topc(X5,X2,X3)
                      | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                      | ~ v1_funct_1(X5) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                  | ~ v5_pre_topc(X4,X1,X3)
                  | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                  | ~ v1_funct_1(X4) )
              | ~ l1_pre_topc(X3)
              | ~ v2_pre_topc(X3)
              | v2_struct_0(X3) )
          & r1_tsep_1(X1,X2) )
        | ~ sP0(X2,X1,X0) ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ( sP0(X2,X1,X0)
        | ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ~ m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                      | ~ v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3)
                      | ~ v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                      | ~ v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)) )
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                    & v5_pre_topc(X5,X2,X3)
                    & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                & v5_pre_topc(X4,X1,X3)
                & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                & v1_funct_1(X4) )
            & l1_pre_topc(X3)
            & v2_pre_topc(X3)
            & ~ v2_struct_0(X3) )
        | ~ r1_tsep_1(X1,X2) )
      & ( ( ! [X3] :
              ( ! [X4] :
                  ( ! [X5] :
                      ( ( m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                        & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3)
                        & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                        & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)) )
                      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                      | ~ v5_pre_topc(X5,X2,X3)
                      | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                      | ~ v1_funct_1(X5) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                  | ~ v5_pre_topc(X4,X1,X3)
                  | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                  | ~ v1_funct_1(X4) )
              | ~ l1_pre_topc(X3)
              | ~ v2_pre_topc(X3)
              | v2_struct_0(X3) )
          & r1_tsep_1(X1,X2) )
        | ~ sP0(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f75,plain,
    ( sP0(sK8,sK7,sK6)
    | r3_tsep_1(sK6,sK7,sK8) ),
    inference(cnf_transformation,[],[f40])).

fof(f128,plain,(
    ! [X1] :
      ( ~ r3_tsep_1(sK6,sK7,X1)
      | ~ m1_pre_topc(X1,sK6)
      | v2_struct_0(X1)
      | sP1(X1,sK7,sK6) ) ),
    inference(resolution,[],[f122,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | ~ r3_tsep_1(X0,X1,X2)
      | sP1(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_tsep_1(X0,X1,X2)
          | ~ sP1(X2,X1,X0) )
        & ( sP1(X2,X1,X0)
          | ~ r3_tsep_1(X0,X1,X2) ) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r3_tsep_1(X0,X1,X2)
      <=> sP1(X2,X1,X0) )
      | ~ sP2(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f122,plain,(
    ! [X0] :
      ( sP2(sK6,sK7,X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK6) ) ),
    inference(subsumption_resolution,[],[f121,f68])).

fof(f68,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f121,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK6)
      | v2_struct_0(X0)
      | sP2(sK6,sK7,X0)
      | v2_struct_0(sK6) ) ),
    inference(subsumption_resolution,[],[f120,f69])).

fof(f69,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f120,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK6)
      | v2_struct_0(X0)
      | sP2(sK6,sK7,X0)
      | ~ v2_pre_topc(sK6)
      | v2_struct_0(sK6) ) ),
    inference(subsumption_resolution,[],[f119,f70])).

fof(f70,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f119,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK6)
      | v2_struct_0(X0)
      | sP2(sK6,sK7,X0)
      | ~ l1_pre_topc(sK6)
      | ~ v2_pre_topc(sK6)
      | v2_struct_0(sK6) ) ),
    inference(subsumption_resolution,[],[f117,f71])).

fof(f71,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f40])).

fof(f117,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK6)
      | v2_struct_0(X0)
      | sP2(sK6,sK7,X0)
      | v2_struct_0(sK7)
      | ~ l1_pre_topc(sK6)
      | ~ v2_pre_topc(sK6)
      | v2_struct_0(sK6) ) ),
    inference(resolution,[],[f104,f72])).

fof(f72,plain,(
    m1_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | sP2(X0,X1,X2)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP2(X0,X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f16,f26,f25])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_tsep_1(X0,X1,X2)
              <=> ( ! [X3] :
                      ( ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                            & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3)
                            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                            & v1_funct_1(X4) )
                          | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3)
                          | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3))
                          | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4))
                          | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3)
                          | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3))
                          | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4))
                          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                          | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                          | ~ v1_funct_1(X4) )
                      | ~ l1_pre_topc(X3)
                      | ~ v2_pre_topc(X3)
                      | v2_struct_0(X3) )
                  & r1_tsep_1(X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_tsep_1(X0,X1,X2)
              <=> ( ! [X3] :
                      ( ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                            & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3)
                            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                            & v1_funct_1(X4) )
                          | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3)
                          | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3))
                          | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4))
                          | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3)
                          | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3))
                          | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4))
                          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                          | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                          | ~ v1_funct_1(X4) )
                      | ~ l1_pre_topc(X3)
                      | ~ v2_pre_topc(X3)
                      | v2_struct_0(X3) )
                  & r1_tsep_1(X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
             => ( r3_tsep_1(X0,X1,X2)
              <=> ( ! [X3] :
                      ( ( l1_pre_topc(X3)
                        & v2_pre_topc(X3)
                        & ~ v2_struct_0(X3) )
                     => ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                            & v1_funct_1(X4) )
                         => ( ( m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                              & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3)
                              & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3))
                              & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4))
                              & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                              & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3)
                              & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3))
                              & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4)) )
                           => ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                              & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3)
                              & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                              & v1_funct_1(X4) ) ) ) )
                  & r1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_tmap_1)).

fof(f727,plain,(
    ~ r1_tsep_1(sK7,sK8) ),
    inference(subsumption_resolution,[],[f726,f666])).

fof(f666,plain,(
    ~ sP0(sK8,sK7,sK6) ),
    inference(global_subsumption,[],[f76,f613])).

fof(f613,plain,(
    r3_tsep_1(sK6,sK7,sK8) ),
    inference(subsumption_resolution,[],[f612,f73])).

fof(f612,plain,
    ( r3_tsep_1(sK6,sK7,sK8)
    | v2_struct_0(sK8) ),
    inference(subsumption_resolution,[],[f611,f74])).

fof(f611,plain,
    ( r3_tsep_1(sK6,sK7,sK8)
    | ~ m1_pre_topc(sK8,sK6)
    | v2_struct_0(sK8) ),
    inference(duplicate_literal_removal,[],[f608])).

fof(f608,plain,
    ( r3_tsep_1(sK6,sK7,sK8)
    | ~ m1_pre_topc(sK8,sK6)
    | v2_struct_0(sK8)
    | r3_tsep_1(sK6,sK7,sK8) ),
    inference(resolution,[],[f607,f127])).

fof(f127,plain,(
    ! [X0] :
      ( ~ sP1(X0,sK7,sK6)
      | ~ m1_pre_topc(X0,sK6)
      | v2_struct_0(X0)
      | r3_tsep_1(sK6,sK7,X0) ) ),
    inference(resolution,[],[f122,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | ~ sP1(X2,X1,X0)
      | r3_tsep_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f607,plain,
    ( sP1(sK8,sK7,sK6)
    | r3_tsep_1(sK6,sK7,sK8) ),
    inference(subsumption_resolution,[],[f606,f134])).

fof(f606,plain,
    ( r3_tsep_1(sK6,sK7,sK8)
    | sP1(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f605])).

fof(f605,plain,
    ( r3_tsep_1(sK6,sK7,sK8)
    | sP1(sK8,sK7,sK6)
    | sP1(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f604,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(sK9(X0,X1,X2))
      | sP1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f604,plain,
    ( v2_struct_0(sK9(sK8,sK7,sK6))
    | r3_tsep_1(sK6,sK7,sK8)
    | sP1(sK8,sK7,sK6) ),
    inference(subsumption_resolution,[],[f603,f134])).

fof(f603,plain,
    ( v2_struct_0(sK9(sK8,sK7,sK6))
    | r3_tsep_1(sK6,sK7,sK8)
    | sP1(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f602])).

fof(f602,plain,
    ( v2_struct_0(sK9(sK8,sK7,sK6))
    | r3_tsep_1(sK6,sK7,sK8)
    | sP1(sK8,sK7,sK6)
    | sP1(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f601,f167])).

fof(f167,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_pre_topc(sK10(X0,X1,X2),k1_tsep_1(X2,X1,X0),sK9(X0,X1,X2))
      | sP1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f166,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(sK10(X0,X1,X2))
      | sP1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f166,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | ~ v5_pre_topc(sK10(X0,X1,X2),k1_tsep_1(X2,X1,X0),sK9(X0,X1,X2))
      | ~ v1_funct_1(sK10(X0,X1,X2))
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f165,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(sK10(X0,X1,X2),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2)))
      | sP1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f165,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | ~ v5_pre_topc(sK10(X0,X1,X2),k1_tsep_1(X2,X1,X0),sK9(X0,X1,X2))
      | ~ v1_funct_2(sK10(X0,X1,X2),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2)))
      | ~ v1_funct_1(sK10(X0,X1,X2))
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f103,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2)))))
      | sP1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | ~ m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2)))))
      | ~ v5_pre_topc(sK10(X0,X1,X2),k1_tsep_1(X2,X1,X0),sK9(X0,X1,X2))
      | ~ v1_funct_2(sK10(X0,X1,X2),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2)))
      | ~ v1_funct_1(sK10(X0,X1,X2))
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f601,plain,
    ( v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | r3_tsep_1(sK6,sK7,sK8)
    | sP1(sK8,sK7,sK6) ),
    inference(subsumption_resolution,[],[f600,f134])).

fof(f600,plain,
    ( v2_struct_0(sK9(sK8,sK7,sK6))
    | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6))
    | r3_tsep_1(sK6,sK7,sK8)
    | sP1(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f599])).

fof(f599,plain,
    ( v2_struct_0(sK9(sK8,sK7,sK6))
    | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6))
    | r3_tsep_1(sK6,sK7,sK8)
    | sP1(sK8,sK7,sK6)
    | sP1(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f598,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)))
      | sP1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f598,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6))
    | r3_tsep_1(sK6,sK7,sK8)
    | sP1(sK8,sK7,sK6) ),
    inference(subsumption_resolution,[],[f597,f134])).

fof(f597,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6))
    | r3_tsep_1(sK6,sK7,sK8)
    | sP1(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f596])).

fof(f596,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6))
    | r3_tsep_1(sK6,sK7,sK8)
    | sP1(sK8,sK7,sK6)
    | sP1(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f595,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)))
      | sP1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f595,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6))
    | r3_tsep_1(sK6,sK7,sK8)
    | sP1(sK8,sK7,sK6) ),
    inference(subsumption_resolution,[],[f594,f134])).

fof(f594,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6))
    | r3_tsep_1(sK6,sK7,sK8)
    | sP1(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f593])).

fof(f593,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6))
    | r3_tsep_1(sK6,sK7,sK8)
    | sP1(sK8,sK7,sK6)
    | sP1(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f592,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)),u1_struct_0(X1),u1_struct_0(sK9(X0,X1,X2)))
      | sP1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f592,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6))
    | r3_tsep_1(sK6,sK7,sK8)
    | sP1(sK8,sK7,sK6) ),
    inference(subsumption_resolution,[],[f591,f134])).

fof(f591,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6))
    | r3_tsep_1(sK6,sK7,sK8)
    | sP1(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f590])).

fof(f590,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6))
    | r3_tsep_1(sK6,sK7,sK8)
    | sP1(sK8,sK7,sK6)
    | sP1(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f589,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)),u1_struct_0(X0),u1_struct_0(sK9(X0,X1,X2)))
      | sP1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f589,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6))
    | r3_tsep_1(sK6,sK7,sK8)
    | sP1(sK8,sK7,sK6) ),
    inference(subsumption_resolution,[],[f588,f134])).

fof(f588,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6))
    | r3_tsep_1(sK6,sK7,sK8)
    | sP1(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f587])).

fof(f587,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6))
    | r3_tsep_1(sK6,sK7,sK8)
    | sP1(sK8,sK7,sK6)
    | sP1(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f586,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK9(X0,X1,X2)))))
      | sP1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f586,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6))
    | r3_tsep_1(sK6,sK7,sK8)
    | sP1(sK8,sK7,sK6) ),
    inference(subsumption_resolution,[],[f585,f134])).

fof(f585,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6))
    | r3_tsep_1(sK6,sK7,sK8)
    | sP1(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f584])).

fof(f584,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6))
    | r3_tsep_1(sK6,sK7,sK8)
    | sP1(sK8,sK7,sK6)
    | sP1(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f583,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK9(X0,X1,X2)))))
      | sP1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f583,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6))
    | r3_tsep_1(sK6,sK7,sK8)
    | sP1(sK8,sK7,sK6) ),
    inference(subsumption_resolution,[],[f582,f134])).

fof(f582,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6))
    | r3_tsep_1(sK6,sK7,sK8)
    | sP1(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f581])).

fof(f581,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6))
    | r3_tsep_1(sK6,sK7,sK8)
    | sP1(sK8,sK7,sK6)
    | sP1(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f580,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( v2_pre_topc(sK9(X0,X1,X2))
      | sP1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f580,plain,
    ( ~ v2_pre_topc(sK9(sK8,sK7,sK6))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6))
    | r3_tsep_1(sK6,sK7,sK8)
    | sP1(sK8,sK7,sK6) ),
    inference(subsumption_resolution,[],[f579,f134])).

fof(f579,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v2_pre_topc(sK9(sK8,sK7,sK6))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6))
    | r3_tsep_1(sK6,sK7,sK8)
    | sP1(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f578])).

fof(f578,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v2_pre_topc(sK9(sK8,sK7,sK6))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6))
    | r3_tsep_1(sK6,sK7,sK8)
    | sP1(sK8,sK7,sK6)
    | sP1(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f577,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( l1_pre_topc(sK9(X0,X1,X2))
      | sP1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f577,plain,
    ( ~ l1_pre_topc(sK9(sK8,sK7,sK6))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v2_pre_topc(sK9(sK8,sK7,sK6))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6))
    | r3_tsep_1(sK6,sK7,sK8)
    | sP1(sK8,sK7,sK6) ),
    inference(subsumption_resolution,[],[f576,f134])).

fof(f576,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ l1_pre_topc(sK9(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK9(sK8,sK7,sK6))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6))
    | r3_tsep_1(sK6,sK7,sK8)
    | sP1(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f575])).

fof(f575,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ l1_pre_topc(sK9(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK9(sK8,sK7,sK6))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6))
    | r3_tsep_1(sK6,sK7,sK8)
    | sP1(sK8,sK7,sK6)
    | sP1(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f574,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)),X1,sK9(X0,X1,X2))
      | sP1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f574,plain,
    ( ~ v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),sK7,sK9(sK8,sK7,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ l1_pre_topc(sK9(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK9(sK8,sK7,sK6))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6))
    | r3_tsep_1(sK6,sK7,sK8)
    | sP1(sK8,sK7,sK6) ),
    inference(subsumption_resolution,[],[f573,f134])).

fof(f573,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),sK7,sK9(sK8,sK7,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ l1_pre_topc(sK9(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK9(sK8,sK7,sK6))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6))
    | r3_tsep_1(sK6,sK7,sK8)
    | sP1(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f564,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)),X0,sK9(X0,X1,X2))
      | sP1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f564,plain,
    ( ~ v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),sK8,sK9(sK8,sK7,sK6))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),sK7,sK9(sK8,sK7,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ l1_pre_topc(sK9(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK9(sK8,sK7,sK6))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6))
    | r3_tsep_1(sK6,sK7,sK8) ),
    inference(resolution,[],[f523,f75])).

fof(f523,plain,
    ( ~ sP0(sK8,sK7,sK6)
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),sK8,sK9(sK8,sK7,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),sK7,sK9(sK8,sK7,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ l1_pre_topc(sK9(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK9(sK8,sK7,sK6))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6)) ),
    inference(superposition,[],[f54,f518])).

fof(f518,plain,(
    sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) ),
    inference(subsumption_resolution,[],[f515,f402])).

fof(f402,plain,
    ( r3_tsep_1(sK6,sK7,sK8)
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) ),
    inference(subsumption_resolution,[],[f401,f73])).

fof(f401,plain,
    ( sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | r3_tsep_1(sK6,sK7,sK8)
    | v2_struct_0(sK8) ),
    inference(subsumption_resolution,[],[f400,f74])).

fof(f400,plain,
    ( sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | r3_tsep_1(sK6,sK7,sK8)
    | ~ m1_pre_topc(sK8,sK6)
    | v2_struct_0(sK8) ),
    inference(duplicate_literal_removal,[],[f397])).

fof(f397,plain,
    ( sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | r3_tsep_1(sK6,sK7,sK8)
    | ~ m1_pre_topc(sK8,sK6)
    | v2_struct_0(sK8)
    | r3_tsep_1(sK6,sK7,sK8) ),
    inference(resolution,[],[f396,f127])).

fof(f396,plain,
    ( sP1(sK8,sK7,sK6)
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | r3_tsep_1(sK6,sK7,sK8) ),
    inference(subsumption_resolution,[],[f395,f134])).

fof(f395,plain,
    ( sP1(sK8,sK7,sK6)
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | r3_tsep_1(sK6,sK7,sK8)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f394])).

fof(f394,plain,
    ( sP1(sK8,sK7,sK6)
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | r3_tsep_1(sK6,sK7,sK8)
    | sP1(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f393,f89])).

fof(f393,plain,
    ( v2_struct_0(sK9(sK8,sK7,sK6))
    | sP1(sK8,sK7,sK6)
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | r3_tsep_1(sK6,sK7,sK8) ),
    inference(subsumption_resolution,[],[f392,f134])).

fof(f392,plain,
    ( v2_struct_0(sK9(sK8,sK7,sK6))
    | sP1(sK8,sK7,sK6)
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | r3_tsep_1(sK6,sK7,sK8)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f391])).

fof(f391,plain,
    ( v2_struct_0(sK9(sK8,sK7,sK6))
    | sP1(sK8,sK7,sK6)
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | r3_tsep_1(sK6,sK7,sK8)
    | sP1(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f390,f95])).

fof(f390,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | sP1(sK8,sK7,sK6)
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | r3_tsep_1(sK6,sK7,sK8) ),
    inference(subsumption_resolution,[],[f389,f134])).

fof(f389,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | sP1(sK8,sK7,sK6)
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | r3_tsep_1(sK6,sK7,sK8)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f388])).

fof(f388,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | sP1(sK8,sK7,sK6)
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | r3_tsep_1(sK6,sK7,sK8)
    | sP1(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f387,f99])).

fof(f387,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | sP1(sK8,sK7,sK6)
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | r3_tsep_1(sK6,sK7,sK8) ),
    inference(subsumption_resolution,[],[f386,f134])).

fof(f386,plain,
    ( v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | r3_tsep_1(sK6,sK7,sK8)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f385])).

fof(f385,plain,
    ( v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | r3_tsep_1(sK6,sK7,sK8)
    | sP1(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f384,f96])).

fof(f384,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | r3_tsep_1(sK6,sK7,sK8) ),
    inference(subsumption_resolution,[],[f383,f134])).

fof(f383,plain,
    ( v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | r3_tsep_1(sK6,sK7,sK8)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f382])).

fof(f382,plain,
    ( v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | r3_tsep_1(sK6,sK7,sK8)
    | sP1(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f381,f100])).

fof(f381,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | r3_tsep_1(sK6,sK7,sK8) ),
    inference(subsumption_resolution,[],[f380,f134])).

fof(f380,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | r3_tsep_1(sK6,sK7,sK8)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f379])).

fof(f379,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | r3_tsep_1(sK6,sK7,sK8)
    | sP1(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f378,f98])).

fof(f378,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | r3_tsep_1(sK6,sK7,sK8) ),
    inference(subsumption_resolution,[],[f377,f134])).

fof(f377,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | r3_tsep_1(sK6,sK7,sK8)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f376])).

fof(f376,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | r3_tsep_1(sK6,sK7,sK8)
    | sP1(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f375,f102])).

fof(f375,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | r3_tsep_1(sK6,sK7,sK8) ),
    inference(subsumption_resolution,[],[f374,f134])).

fof(f374,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | sP1(sK8,sK7,sK6)
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | r3_tsep_1(sK6,sK7,sK8)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f373])).

fof(f373,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | sP1(sK8,sK7,sK6)
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | r3_tsep_1(sK6,sK7,sK8)
    | sP1(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f372,f90])).

fof(f372,plain,
    ( ~ v2_pre_topc(sK9(sK8,sK7,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | sP1(sK8,sK7,sK6)
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | r3_tsep_1(sK6,sK7,sK8) ),
    inference(subsumption_resolution,[],[f371,f134])).

fof(f371,plain,
    ( sP1(sK8,sK7,sK6)
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v2_pre_topc(sK9(sK8,sK7,sK6))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | r3_tsep_1(sK6,sK7,sK8)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f370])).

fof(f370,plain,
    ( sP1(sK8,sK7,sK6)
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v2_pre_topc(sK9(sK8,sK7,sK6))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | r3_tsep_1(sK6,sK7,sK8)
    | sP1(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f369,f91])).

fof(f369,plain,
    ( ~ l1_pre_topc(sK9(sK8,sK7,sK6))
    | sP1(sK8,sK7,sK6)
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v2_pre_topc(sK9(sK8,sK7,sK6))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | r3_tsep_1(sK6,sK7,sK8) ),
    inference(subsumption_resolution,[],[f368,f134])).

fof(f368,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | sP1(sK8,sK7,sK6)
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ l1_pre_topc(sK9(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK9(sK8,sK7,sK6))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | r3_tsep_1(sK6,sK7,sK8)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f367])).

fof(f367,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | sP1(sK8,sK7,sK6)
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ l1_pre_topc(sK9(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK9(sK8,sK7,sK6))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | r3_tsep_1(sK6,sK7,sK8)
    | sP1(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f366,f97])).

fof(f366,plain,
    ( ~ v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),sK7,sK9(sK8,sK7,sK6))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | sP1(sK8,sK7,sK6)
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ l1_pre_topc(sK9(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK9(sK8,sK7,sK6))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | r3_tsep_1(sK6,sK7,sK8) ),
    inference(subsumption_resolution,[],[f365,f134])).

fof(f365,plain,
    ( v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | sP1(sK8,sK7,sK6)
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),sK7,sK9(sK8,sK7,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ l1_pre_topc(sK9(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK9(sK8,sK7,sK6))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | r3_tsep_1(sK6,sK7,sK8)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f364])).

fof(f364,plain,
    ( v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | sP1(sK8,sK7,sK6)
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),sK7,sK9(sK8,sK7,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ l1_pre_topc(sK9(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK9(sK8,sK7,sK6))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | r3_tsep_1(sK6,sK7,sK8)
    | sP1(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f363,f101])).

fof(f363,plain,
    ( ~ v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),sK8,sK9(sK8,sK7,sK6))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | sP1(sK8,sK7,sK6)
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),sK7,sK9(sK8,sK7,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ l1_pre_topc(sK9(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK9(sK8,sK7,sK6))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | r3_tsep_1(sK6,sK7,sK8) ),
    inference(resolution,[],[f362,f75])).

fof(f362,plain,
    ( ~ sP0(sK8,sK7,sK6)
    | sP1(sK8,sK7,sK6)
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),sK8,sK9(sK8,sK7,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),sK7,sK9(sK8,sK7,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ l1_pre_topc(sK9(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK9(sK8,sK7,sK6))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) ),
    inference(subsumption_resolution,[],[f353,f53])).

fof(f53,plain,(
    ! [X6,X2,X0,X8,X7,X1] :
      ( v1_funct_2(k10_tmap_1(X2,X6,X1,X0,X7,X8),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X6))
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X6))))
      | ~ v5_pre_topc(X8,X0,X6)
      | ~ v1_funct_2(X8,u1_struct_0(X0),u1_struct_0(X6))
      | ~ v1_funct_1(X8)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X6))))
      | ~ v5_pre_topc(X7,X1,X6)
      | ~ v1_funct_2(X7,u1_struct_0(X1),u1_struct_0(X6))
      | ~ v1_funct_1(X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f353,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),sK8,sK9(sK8,sK7,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),sK7,sK9(sK8,sK7,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ l1_pre_topc(sK9(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK9(sK8,sK7,sK6))
    | ~ sP0(sK8,sK7,sK6) ),
    inference(duplicate_literal_removal,[],[f352])).

fof(f352,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),sK8,sK9(sK8,sK7,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),sK7,sK9(sK8,sK7,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ l1_pre_topc(sK9(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK9(sK8,sK7,sK6))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ sP0(sK8,sK7,sK6) ),
    inference(resolution,[],[f350,f55])).

fof(f55,plain,(
    ! [X6,X2,X0,X8,X7,X1] :
      ( m1_subset_1(k10_tmap_1(X2,X6,X1,X0,X7,X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X6))))
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X6))))
      | ~ v5_pre_topc(X8,X0,X6)
      | ~ v1_funct_2(X8,u1_struct_0(X0),u1_struct_0(X6))
      | ~ v1_funct_1(X8)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X6))))
      | ~ v5_pre_topc(X7,X1,X6)
      | ~ v1_funct_2(X7,u1_struct_0(X1),u1_struct_0(X6))
      | ~ v1_funct_1(X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f350,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | v2_struct_0(sK9(sK8,sK7,sK6)) ),
    inference(subsumption_resolution,[],[f349,f134])).

fof(f349,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f348])).

fof(f348,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | sP1(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f347,f95])).

fof(f347,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | v2_struct_0(sK9(sK8,sK7,sK6)) ),
    inference(subsumption_resolution,[],[f346,f134])).

fof(f346,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f345])).

fof(f345,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | sP1(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f344,f99])).

fof(f344,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | v2_struct_0(sK9(sK8,sK7,sK6)) ),
    inference(subsumption_resolution,[],[f343,f134])).

fof(f343,plain,
    ( v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f342])).

fof(f342,plain,
    ( v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f341,f92])).

fof(f341,plain,
    ( ~ v1_funct_1(sK10(sK8,sK7,sK6))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) ),
    inference(subsumption_resolution,[],[f340,f134])).

fof(f340,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK10(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f339])).

fof(f339,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK10(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f338,f96])).

fof(f338,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK10(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) ),
    inference(subsumption_resolution,[],[f337,f134])).

fof(f337,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK10(sK8,sK7,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f336])).

fof(f336,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK10(sK8,sK7,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f335,f100])).

fof(f335,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK10(sK8,sK7,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) ),
    inference(subsumption_resolution,[],[f334,f134])).

fof(f334,plain,
    ( sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK10(sK8,sK7,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f333])).

fof(f333,plain,
    ( sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK10(sK8,sK7,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f332,f93])).

fof(f332,plain,
    ( ~ v1_funct_2(sK10(sK8,sK7,sK6),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK10(sK8,sK7,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) ),
    inference(subsumption_resolution,[],[f331,f134])).

fof(f331,plain,
    ( v2_struct_0(sK9(sK8,sK7,sK6))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK10(sK8,sK7,sK6),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK10(sK8,sK7,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f330])).

fof(f330,plain,
    ( v2_struct_0(sK9(sK8,sK7,sK6))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK10(sK8,sK7,sK6),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK10(sK8,sK7,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f329,f98])).

fof(f329,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK10(sK8,sK7,sK6),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK10(sK8,sK7,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) ),
    inference(subsumption_resolution,[],[f328,f134])).

fof(f328,plain,
    ( ~ v1_funct_1(sK10(sK8,sK7,sK6))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK10(sK8,sK7,sK6),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f327])).

fof(f327,plain,
    ( ~ v1_funct_1(sK10(sK8,sK7,sK6))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK10(sK8,sK7,sK6),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f326,f94])).

fof(f326,plain,
    ( ~ m1_subset_1(sK10(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_1(sK10(sK8,sK7,sK6))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK10(sK8,sK7,sK6),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) ),
    inference(subsumption_resolution,[],[f325,f134])).

fof(f325,plain,
    ( ~ v1_funct_2(sK10(sK8,sK7,sK6),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK10(sK8,sK7,sK6))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ m1_subset_1(sK10(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f324])).

fof(f324,plain,
    ( ~ v1_funct_2(sK10(sK8,sK7,sK6),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK10(sK8,sK7,sK6))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ m1_subset_1(sK10(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f323,f90])).

fof(f323,plain,
    ( ~ v2_pre_topc(sK9(sK8,sK7,sK6))
    | ~ v1_funct_2(sK10(sK8,sK7,sK6),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK10(sK8,sK7,sK6))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ m1_subset_1(sK10(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) ),
    inference(subsumption_resolution,[],[f322,f134])).

fof(f322,plain,
    ( ~ v1_funct_1(sK10(sK8,sK7,sK6))
    | ~ v1_funct_2(sK10(sK8,sK7,sK6),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v2_pre_topc(sK9(sK8,sK7,sK6))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ m1_subset_1(sK10(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f321])).

fof(f321,plain,
    ( ~ v1_funct_1(sK10(sK8,sK7,sK6))
    | ~ v1_funct_2(sK10(sK8,sK7,sK6),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v2_pre_topc(sK9(sK8,sK7,sK6))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ m1_subset_1(sK10(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f311,f91])).

fof(f311,plain,
    ( ~ l1_pre_topc(sK9(sK8,sK7,sK6))
    | ~ v1_funct_1(sK10(sK8,sK7,sK6))
    | ~ v1_funct_2(sK10(sK8,sK7,sK6),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v2_pre_topc(sK9(sK8,sK7,sK6))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ m1_subset_1(sK10(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) ),
    inference(subsumption_resolution,[],[f310,f68])).

fof(f310,plain,
    ( ~ v1_funct_2(sK10(sK8,sK7,sK6),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK10(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK9(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK9(sK8,sK7,sK6))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | v2_struct_0(sK6)
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ m1_subset_1(sK10(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) ),
    inference(subsumption_resolution,[],[f309,f69])).

fof(f309,plain,
    ( ~ v1_funct_2(sK10(sK8,sK7,sK6),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK10(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK9(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK9(sK8,sK7,sK6))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ m1_subset_1(sK10(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) ),
    inference(subsumption_resolution,[],[f308,f70])).

fof(f308,plain,
    ( ~ v1_funct_2(sK10(sK8,sK7,sK6),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK10(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK9(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK9(sK8,sK7,sK6))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ m1_subset_1(sK10(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) ),
    inference(subsumption_resolution,[],[f307,f71])).

fof(f307,plain,
    ( ~ v1_funct_2(sK10(sK8,sK7,sK6),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK10(sK8,sK7,sK6))
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK9(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK9(sK8,sK7,sK6))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ m1_subset_1(sK10(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) ),
    inference(subsumption_resolution,[],[f306,f72])).

fof(f306,plain,
    ( ~ v1_funct_2(sK10(sK8,sK7,sK6),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK10(sK8,sK7,sK6))
    | ~ m1_pre_topc(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK9(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK9(sK8,sK7,sK6))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ m1_subset_1(sK10(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) ),
    inference(subsumption_resolution,[],[f305,f73])).

fof(f305,plain,
    ( ~ v1_funct_2(sK10(sK8,sK7,sK6),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK10(sK8,sK7,sK6))
    | v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK9(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK9(sK8,sK7,sK6))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ m1_subset_1(sK10(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) ),
    inference(subsumption_resolution,[],[f304,f74])).

fof(f304,plain,
    ( ~ v1_funct_2(sK10(sK8,sK7,sK6),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK10(sK8,sK7,sK6))
    | ~ m1_pre_topc(sK8,sK6)
    | v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK9(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK9(sK8,sK7,sK6))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ m1_subset_1(sK10(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | sP1(sK8,sK7,sK6)
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) ),
    inference(resolution,[],[f273,f247])).

fof(f247,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k10_tmap_1(sK6,sK9(sK8,sK7,X1),sK7,sK8,X0,k3_tmap_1(X1,sK9(sK8,sK7,X1),k1_tsep_1(X1,sK7,sK8),sK8,sK10(sK8,sK7,X1))))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,X1)))))
      | ~ v1_funct_2(X0,u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,X1)))
      | ~ v1_funct_2(k3_tmap_1(X1,sK9(sK8,sK7,X1),k1_tsep_1(X1,sK7,sK8),sK8,sK10(sK8,sK7,X1)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,X1)))
      | sP1(sK8,sK7,X1)
      | ~ v1_funct_1(k3_tmap_1(X1,sK9(sK8,sK7,X1),k1_tsep_1(X1,sK7,sK8),sK8,sK10(sK8,sK7,X1))) ) ),
    inference(subsumption_resolution,[],[f246,f134])).

fof(f246,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X0,u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,X1)))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,X1)))))
      | v1_funct_1(k10_tmap_1(sK6,sK9(sK8,sK7,X1),sK7,sK8,X0,k3_tmap_1(X1,sK9(sK8,sK7,X1),k1_tsep_1(X1,sK7,sK8),sK8,sK10(sK8,sK7,X1))))
      | ~ v1_funct_2(k3_tmap_1(X1,sK9(sK8,sK7,X1),k1_tsep_1(X1,sK7,sK8),sK8,sK10(sK8,sK7,X1)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,X1)))
      | sP1(sK8,sK7,X1)
      | ~ v1_funct_1(k3_tmap_1(X1,sK9(sK8,sK7,X1),k1_tsep_1(X1,sK7,sK8),sK8,sK10(sK8,sK7,X1)))
      | ~ r1_tsep_1(sK7,sK8) ) ),
    inference(duplicate_literal_removal,[],[f245])).

fof(f245,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X0,u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,X1)))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,X1)))))
      | v1_funct_1(k10_tmap_1(sK6,sK9(sK8,sK7,X1),sK7,sK8,X0,k3_tmap_1(X1,sK9(sK8,sK7,X1),k1_tsep_1(X1,sK7,sK8),sK8,sK10(sK8,sK7,X1))))
      | ~ v1_funct_2(k3_tmap_1(X1,sK9(sK8,sK7,X1),k1_tsep_1(X1,sK7,sK8),sK8,sK10(sK8,sK7,X1)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,X1)))
      | sP1(sK8,sK7,X1)
      | ~ v1_funct_1(k3_tmap_1(X1,sK9(sK8,sK7,X1),k1_tsep_1(X1,sK7,sK8),sK8,sK10(sK8,sK7,X1)))
      | sP1(sK8,sK7,X1)
      | ~ r1_tsep_1(sK7,sK8) ) ),
    inference(resolution,[],[f244,f102])).

fof(f244,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,X1)))))
      | ~ v1_funct_2(X0,u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,X1)))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,X1)))))
      | v1_funct_1(k10_tmap_1(sK6,sK9(sK8,sK7,X1),sK7,sK8,X0,X2))
      | ~ v1_funct_2(X2,u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,X1)))
      | sP1(sK8,sK7,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(resolution,[],[f209,f134])).

fof(f209,plain,(
    ! [X10,X8,X7,X11,X9] :
      ( ~ r1_tsep_1(X10,X9)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(X9,X10,X11)))))
      | ~ v1_funct_2(X8,u1_struct_0(sK7),u1_struct_0(sK9(X9,X10,X11)))
      | ~ v1_funct_1(X8)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(X9,X10,X11)))))
      | v1_funct_1(k10_tmap_1(sK6,sK9(X9,X10,X11),sK7,sK8,X8,X7))
      | ~ v1_funct_2(X7,u1_struct_0(sK8),u1_struct_0(sK9(X9,X10,X11)))
      | sP1(X9,X10,X11)
      | ~ v1_funct_1(X7) ) ),
    inference(subsumption_resolution,[],[f208,f89])).

fof(f208,plain,(
    ! [X10,X8,X7,X11,X9] :
      ( ~ v1_funct_1(X7)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(X9,X10,X11)))))
      | ~ v1_funct_2(X8,u1_struct_0(sK7),u1_struct_0(sK9(X9,X10,X11)))
      | ~ v1_funct_1(X8)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(X9,X10,X11)))))
      | v1_funct_1(k10_tmap_1(sK6,sK9(X9,X10,X11),sK7,sK8,X8,X7))
      | ~ v1_funct_2(X7,u1_struct_0(sK8),u1_struct_0(sK9(X9,X10,X11)))
      | v2_struct_0(sK9(X9,X10,X11))
      | sP1(X9,X10,X11)
      | ~ r1_tsep_1(X10,X9) ) ),
    inference(subsumption_resolution,[],[f203,f90])).

fof(f203,plain,(
    ! [X10,X8,X7,X11,X9] :
      ( ~ v1_funct_1(X7)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(X9,X10,X11)))))
      | ~ v1_funct_2(X8,u1_struct_0(sK7),u1_struct_0(sK9(X9,X10,X11)))
      | ~ v1_funct_1(X8)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(X9,X10,X11)))))
      | v1_funct_1(k10_tmap_1(sK6,sK9(X9,X10,X11),sK7,sK8,X8,X7))
      | ~ v1_funct_2(X7,u1_struct_0(sK8),u1_struct_0(sK9(X9,X10,X11)))
      | ~ v2_pre_topc(sK9(X9,X10,X11))
      | v2_struct_0(sK9(X9,X10,X11))
      | sP1(X9,X10,X11)
      | ~ r1_tsep_1(X10,X9) ) ),
    inference(resolution,[],[f191,f91])).

fof(f191,plain,(
    ! [X4,X5,X3] :
      ( ~ l1_pre_topc(X4)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X4))))
      | ~ v1_funct_2(X5,u1_struct_0(sK7),u1_struct_0(X4))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(X4))))
      | v1_funct_1(k10_tmap_1(sK6,X4,sK7,sK8,X5,X3))
      | ~ v1_funct_2(X3,u1_struct_0(sK8),u1_struct_0(X4))
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f189,f73])).

fof(f189,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_funct_2(X3,u1_struct_0(sK8),u1_struct_0(X4))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X4))))
      | ~ v1_funct_2(X5,u1_struct_0(sK7),u1_struct_0(X4))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(X4))))
      | v2_struct_0(sK8)
      | v1_funct_1(k10_tmap_1(sK6,X4,sK7,sK8,X5,X3))
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(resolution,[],[f183,f74])).

fof(f183,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_pre_topc(X1,sK6)
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X2))))
      | ~ v1_funct_2(X3,u1_struct_0(sK7),u1_struct_0(X2))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | v2_struct_0(X1)
      | v1_funct_1(k10_tmap_1(sK6,X2,sK7,X1,X3,X0))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f182,f68])).

fof(f182,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X2))))
      | ~ v1_funct_2(X3,u1_struct_0(sK7),u1_struct_0(X2))
      | ~ v1_funct_1(X3)
      | ~ m1_pre_topc(X1,sK6)
      | v2_struct_0(X1)
      | v1_funct_1(k10_tmap_1(sK6,X2,sK7,X1,X3,X0))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | v2_struct_0(sK6) ) ),
    inference(subsumption_resolution,[],[f181,f69])).

fof(f181,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X2))))
      | ~ v1_funct_2(X3,u1_struct_0(sK7),u1_struct_0(X2))
      | ~ v1_funct_1(X3)
      | ~ m1_pre_topc(X1,sK6)
      | v2_struct_0(X1)
      | v1_funct_1(k10_tmap_1(sK6,X2,sK7,X1,X3,X0))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ v2_pre_topc(sK6)
      | v2_struct_0(sK6) ) ),
    inference(subsumption_resolution,[],[f180,f70])).

fof(f180,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X2))))
      | ~ v1_funct_2(X3,u1_struct_0(sK7),u1_struct_0(X2))
      | ~ v1_funct_1(X3)
      | ~ m1_pre_topc(X1,sK6)
      | v2_struct_0(X1)
      | v1_funct_1(k10_tmap_1(sK6,X2,sK7,X1,X3,X0))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(sK6)
      | ~ v2_pre_topc(sK6)
      | v2_struct_0(sK6) ) ),
    inference(subsumption_resolution,[],[f178,f71])).

fof(f178,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X2))))
      | ~ v1_funct_2(X3,u1_struct_0(sK7),u1_struct_0(X2))
      | ~ v1_funct_1(X3)
      | ~ m1_pre_topc(X1,sK6)
      | v2_struct_0(X1)
      | v1_funct_1(k10_tmap_1(sK6,X2,sK7,X1,X3,X0))
      | v2_struct_0(sK7)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(sK6)
      | ~ v2_pre_topc(sK6)
      | v2_struct_0(sK6) ) ),
    inference(resolution,[],[f110,f72])).

fof(f110,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(X4)
        & m1_pre_topc(X3,X0)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_tmap_1)).

fof(f273,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(k10_tmap_1(X1,X4,X2,X3,k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X2,X0),k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X3,X0)))
      | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | k10_tmap_1(X1,X4,X2,X3,k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X2,X0),k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X3,X0)) = X0
      | ~ m1_subset_1(k10_tmap_1(X1,X4,X2,X3,k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X2,X0),k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X3,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4))))
      | ~ v1_funct_2(k10_tmap_1(X1,X4,X2,X3,k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X2,X0),k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X3,X0)),u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4)))) ) ),
    inference(duplicate_literal_removal,[],[f272])).

fof(f272,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4))))
      | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | k10_tmap_1(X1,X4,X2,X3,k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X2,X0),k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X3,X0)) = X0
      | ~ m1_subset_1(k10_tmap_1(X1,X4,X2,X3,k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X2,X0),k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X3,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4))))
      | ~ v1_funct_2(k10_tmap_1(X1,X4,X2,X3,k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X2,X0),k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X3,X0)),u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4))
      | ~ v1_funct_1(k10_tmap_1(X1,X4,X2,X3,k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X2,X0),k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X3,X0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4))))
      | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4))
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f81,f108])).

fof(f108,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_funct_2(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f81,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_tmap_1)).

fof(f515,plain,
    ( sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ r3_tsep_1(sK6,sK7,sK8) ),
    inference(resolution,[],[f514,f76])).

fof(f514,plain,
    ( sP0(sK8,sK7,sK6)
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) ),
    inference(subsumption_resolution,[],[f513,f134])).

fof(f513,plain,
    ( sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f512])).

fof(f512,plain,
    ( sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | sP0(sK8,sK7,sK6)
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f511,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(sK4(X0,X1,X2))
      | sP0(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f511,plain,
    ( ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | sP0(sK8,sK7,sK6) ),
    inference(subsumption_resolution,[],[f510,f134])).

fof(f510,plain,
    ( sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f509])).

fof(f509,plain,
    ( sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f508,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(sK5(X0,X1,X2))
      | sP0(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f508,plain,
    ( ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6) ),
    inference(subsumption_resolution,[],[f507,f134])).

fof(f507,plain,
    ( ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f506])).

fof(f506,plain,
    ( ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f505,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(sK3(X0,X1,X2))
      | sP0(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f505,plain,
    ( v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6) ),
    inference(subsumption_resolution,[],[f504,f134])).

fof(f504,plain,
    ( ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f503])).

fof(f503,plain,
    ( ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f502,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(sK4(X0,X1,X2),u1_struct_0(X1),u1_struct_0(sK3(X0,X1,X2)))
      | sP0(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f502,plain,
    ( ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6) ),
    inference(subsumption_resolution,[],[f501,f134])).

fof(f501,plain,
    ( v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f500])).

fof(f500,plain,
    ( v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f499,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(sK5(X0,X1,X2),u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2)))
      | sP0(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f499,plain,
    ( ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6) ),
    inference(subsumption_resolution,[],[f498,f134])).

fof(f498,plain,
    ( v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f497])).

fof(f497,plain,
    ( v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f496,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3(X0,X1,X2)))))
      | sP0(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f496,plain,
    ( ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6) ),
    inference(subsumption_resolution,[],[f495,f134])).

fof(f495,plain,
    ( ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f494])).

fof(f494,plain,
    ( ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f493,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2)))))
      | sP0(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f493,plain,
    ( ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6) ),
    inference(subsumption_resolution,[],[f492,f134])).

fof(f492,plain,
    ( ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f491,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v2_pre_topc(sK3(X0,X1,X2))
      | sP0(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f491,plain,
    ( ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) ),
    inference(global_subsumption,[],[f76,f402,f490])).

fof(f490,plain,
    ( v2_struct_0(sK3(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6)) ),
    inference(subsumption_resolution,[],[f489,f134])).

fof(f489,plain,
    ( v2_struct_0(sK3(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f488])).

fof(f488,plain,
    ( v2_struct_0(sK3(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f487,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( l1_pre_topc(sK3(X0,X1,X2))
      | sP0(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f487,plain,
    ( ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6)) ),
    inference(subsumption_resolution,[],[f486,f68])).

fof(f486,plain,
    ( sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | v2_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f485,f69])).

fof(f485,plain,
    ( sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f484,f70])).

fof(f484,plain,
    ( sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f483,f71])).

fof(f483,plain,
    ( sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f482,f72])).

fof(f482,plain,
    ( sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ m1_pre_topc(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f481,f73])).

fof(f481,plain,
    ( sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f480,f74])).

fof(f480,plain,
    ( sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ m1_pre_topc(sK8,sK6)
    | v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(duplicate_literal_removal,[],[f477])).

fof(f477,plain,
    ( sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ m1_pre_topc(sK8,sK6)
    | v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(resolution,[],[f476,f111])).

fof(f111,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f22])).

fof(f476,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6) ),
    inference(subsumption_resolution,[],[f475,f134])).

fof(f475,plain,
    ( sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f474])).

fof(f474,plain,
    ( sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f473,f59])).

fof(f473,plain,
    ( ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6) ),
    inference(subsumption_resolution,[],[f472,f134])).

fof(f472,plain,
    ( v2_struct_0(sK3(sK8,sK7,sK6))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f471])).

fof(f471,plain,
    ( v2_struct_0(sK3(sK8,sK7,sK6))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f470,f63])).

fof(f470,plain,
    ( ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6) ),
    inference(subsumption_resolution,[],[f469,f134])).

fof(f469,plain,
    ( ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f468])).

fof(f468,plain,
    ( ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f467,f60])).

fof(f467,plain,
    ( ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6) ),
    inference(subsumption_resolution,[],[f466,f134])).

fof(f466,plain,
    ( v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f465])).

fof(f465,plain,
    ( v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f464,f64])).

fof(f464,plain,
    ( ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6) ),
    inference(subsumption_resolution,[],[f463,f134])).

fof(f463,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f462])).

fof(f462,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f461,f62])).

fof(f461,plain,
    ( ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6) ),
    inference(subsumption_resolution,[],[f460,f134])).

fof(f460,plain,
    ( ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f459])).

fof(f459,plain,
    ( ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f458,f66])).

fof(f458,plain,
    ( ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6) ),
    inference(subsumption_resolution,[],[f457,f134])).

fof(f457,plain,
    ( ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f456,f57])).

fof(f456,plain,
    ( ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) ),
    inference(global_subsumption,[],[f76,f402,f455])).

fof(f455,plain,
    ( v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sP0(sK8,sK7,sK6)
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6)) ),
    inference(subsumption_resolution,[],[f454,f134])).

fof(f454,plain,
    ( v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sP0(sK8,sK7,sK6)
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f453])).

fof(f453,plain,
    ( v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sP0(sK8,sK7,sK6)
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f452,f58])).

fof(f452,plain,
    ( ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sP0(sK8,sK7,sK6)
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6)) ),
    inference(subsumption_resolution,[],[f451,f68])).

fof(f451,plain,
    ( sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sP0(sK8,sK7,sK6)
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | v2_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f450,f69])).

fof(f450,plain,
    ( sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sP0(sK8,sK7,sK6)
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f449,f70])).

fof(f449,plain,
    ( sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sP0(sK8,sK7,sK6)
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f448,f71])).

fof(f448,plain,
    ( sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sP0(sK8,sK7,sK6)
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f447,f72])).

fof(f447,plain,
    ( sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sP0(sK8,sK7,sK6)
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ m1_pre_topc(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f446,f73])).

fof(f446,plain,
    ( sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sP0(sK8,sK7,sK6)
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f445,f74])).

fof(f445,plain,
    ( sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sP0(sK8,sK7,sK6)
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ m1_pre_topc(sK8,sK6)
    | v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(duplicate_literal_removal,[],[f442])).

fof(f442,plain,
    ( sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sP0(sK8,sK7,sK6)
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ m1_pre_topc(sK8,sK6)
    | v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(resolution,[],[f441,f112])).

fof(f112,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f22])).

fof(f441,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sP0(sK8,sK7,sK6) ),
    inference(subsumption_resolution,[],[f440,f134])).

fof(f440,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f439])).

fof(f439,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6)
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f438,f59])).

fof(f438,plain,
    ( ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6) ),
    inference(subsumption_resolution,[],[f437,f134])).

fof(f437,plain,
    ( ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f436])).

fof(f436,plain,
    ( ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6)
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f435,f63])).

fof(f435,plain,
    ( ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6) ),
    inference(subsumption_resolution,[],[f434,f134])).

fof(f434,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f433])).

fof(f433,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6)
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f432,f60])).

fof(f432,plain,
    ( ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6) ),
    inference(subsumption_resolution,[],[f431,f134])).

fof(f431,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f430])).

fof(f430,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6)
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f429,f64])).

fof(f429,plain,
    ( ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6) ),
    inference(subsumption_resolution,[],[f428,f134])).

fof(f428,plain,
    ( ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f427])).

fof(f427,plain,
    ( ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6)
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f426,f62])).

fof(f426,plain,
    ( ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6) ),
    inference(subsumption_resolution,[],[f425,f134])).

fof(f425,plain,
    ( ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f424])).

fof(f424,plain,
    ( ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6)
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f423,f66])).

fof(f423,plain,
    ( ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6) ),
    inference(subsumption_resolution,[],[f422,f134])).

fof(f422,plain,
    ( ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f421])).

fof(f421,plain,
    ( ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6)
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f420,f57])).

fof(f420,plain,
    ( ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6) ),
    inference(subsumption_resolution,[],[f419,f134])).

fof(f419,plain,
    ( sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f418])).

fof(f418,plain,
    ( sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6)
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f417,f58])).

fof(f417,plain,
    ( ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6) ),
    inference(subsumption_resolution,[],[f416,f134])).

fof(f416,plain,
    ( ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f415])).

fof(f415,plain,
    ( ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6)
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f414,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(sK4(X0,X1,X2),X1,sK3(X0,X1,X2))
      | sP0(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f414,plain,
    ( ~ v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6) ),
    inference(subsumption_resolution,[],[f413,f134])).

fof(f413,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f404,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(sK5(X0,X1,X2),X0,sK3(X0,X1,X2))
      | sP0(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f404,plain,
    ( ~ v5_pre_topc(sK5(sK8,sK7,sK6),sK8,sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) ),
    inference(resolution,[],[f402,f320])).

fof(f320,plain,
    ( ~ r3_tsep_1(sK6,sK7,sK8)
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(sK5(sK8,sK7,sK6),sK8,sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) ),
    inference(subsumption_resolution,[],[f319,f76])).

fof(f319,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6)
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(sK5(sK8,sK7,sK6),sK8,sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ r3_tsep_1(sK6,sK7,sK8) ),
    inference(subsumption_resolution,[],[f318,f68])).

fof(f318,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6)
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(sK5(sK8,sK7,sK6),sK8,sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ r3_tsep_1(sK6,sK7,sK8)
    | v2_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f317,f69])).

fof(f317,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6)
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(sK5(sK8,sK7,sK6),sK8,sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ r3_tsep_1(sK6,sK7,sK8)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f316,f70])).

fof(f316,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6)
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(sK5(sK8,sK7,sK6),sK8,sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ r3_tsep_1(sK6,sK7,sK8)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f315,f71])).

fof(f315,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6)
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(sK5(sK8,sK7,sK6),sK8,sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ r3_tsep_1(sK6,sK7,sK8)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f314,f72])).

fof(f314,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6)
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(sK5(sK8,sK7,sK6),sK8,sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ r3_tsep_1(sK6,sK7,sK8)
    | ~ m1_pre_topc(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f313,f73])).

fof(f313,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6)
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(sK5(sK8,sK7,sK6),sK8,sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ r3_tsep_1(sK6,sK7,sK8)
    | v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f312,f74])).

fof(f312,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6)
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(sK5(sK8,sK7,sK6),sK8,sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ r3_tsep_1(sK6,sK7,sK8)
    | ~ m1_pre_topc(sK8,sK6)
    | v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(resolution,[],[f303,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( r4_tsep_1(X0,X1,X2)
      | ~ r3_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( r4_tsep_1(X0,X1,X2)
                    & r1_tsep_1(X1,X2) )
                  | ~ r3_tsep_1(X0,X1,X2) )
                & ( r3_tsep_1(X0,X1,X2)
                  | ~ r4_tsep_1(X0,X1,X2)
                  | ~ r1_tsep_1(X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( r4_tsep_1(X0,X1,X2)
                    & r1_tsep_1(X1,X2) )
                  | ~ r3_tsep_1(X0,X1,X2) )
                & ( r3_tsep_1(X0,X1,X2)
                  | ~ r4_tsep_1(X0,X1,X2)
                  | ~ r1_tsep_1(X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r4_tsep_1(X0,X1,X2)
                  & r1_tsep_1(X1,X2) )
              <=> r3_tsep_1(X0,X1,X2) )
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
              ( ( ( r4_tsep_1(X0,X1,X2)
                  & r1_tsep_1(X1,X2) )
              <=> r3_tsep_1(X0,X1,X2) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
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
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ( r4_tsep_1(X0,X1,X2)
                  & r1_tsep_1(X1,X2) )
              <=> r3_tsep_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_tsep_1)).

fof(f303,plain,
    ( ~ r4_tsep_1(sK6,sK7,sK8)
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6)
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(sK5(sK8,sK7,sK6),sK8,sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6)) ),
    inference(subsumption_resolution,[],[f302,f68])).

fof(f302,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6)
    | ~ r4_tsep_1(sK6,sK7,sK8)
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(sK5(sK8,sK7,sK6),sK8,sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | v2_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f301,f69])).

fof(f301,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6)
    | ~ r4_tsep_1(sK6,sK7,sK8)
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(sK5(sK8,sK7,sK6),sK8,sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f300,f70])).

fof(f300,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6)
    | ~ r4_tsep_1(sK6,sK7,sK8)
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(sK5(sK8,sK7,sK6),sK8,sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f299,f71])).

fof(f299,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6)
    | ~ r4_tsep_1(sK6,sK7,sK8)
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(sK5(sK8,sK7,sK6),sK8,sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f298,f72])).

fof(f298,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6)
    | ~ r4_tsep_1(sK6,sK7,sK8)
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(sK5(sK8,sK7,sK6),sK8,sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ m1_pre_topc(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f297,f73])).

fof(f297,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6)
    | ~ r4_tsep_1(sK6,sK7,sK8)
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(sK5(sK8,sK7,sK6),sK8,sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f296,f74])).

fof(f296,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6)
    | ~ r4_tsep_1(sK6,sK7,sK8)
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(sK5(sK8,sK7,sK6),sK8,sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ m1_pre_topc(sK8,sK6)
    | v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f294,f134])).

fof(f294,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6)
    | ~ r4_tsep_1(sK6,sK7,sK8)
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(sK5(sK8,sK7,sK6),sK8,sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ r1_tsep_1(sK7,sK8)
    | ~ m1_pre_topc(sK8,sK6)
    | v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(resolution,[],[f293,f79])).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
      | ~ r4_tsep_1(X0,X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v5_pre_topc(X5,X3,X1)
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v5_pre_topc(X4,X2,X1)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ r1_tsep_1(X2,X3)
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
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          | ~ r4_tsep_1(X0,X2,X3)
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(X5,X3,X1)
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v5_pre_topc(X4,X2,X1)
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r1_tsep_1(X2,X3)
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          | ~ r4_tsep_1(X0,X2,X3)
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(X5,X3,X1)
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v5_pre_topc(X4,X2,X1)
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r1_tsep_1(X2,X3)
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
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( r1_tsep_1(X2,X3)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(X4,X2,X1)
                          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v5_pre_topc(X5,X3,X1)
                              & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ( r4_tsep_1(X0,X2,X3)
                             => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                                & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                                & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                                & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_tmap_1)).

fof(f293,plain,
    ( ~ v5_pre_topc(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_tsep_1(sK6,sK7,sK8),sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6) ),
    inference(subsumption_resolution,[],[f292,f134])).

fof(f292,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v5_pre_topc(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_tsep_1(sK6,sK7,sK8),sK3(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f291])).

fof(f291,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v5_pre_topc(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_tsep_1(sK6,sK7,sK8),sK3(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f290,f59])).

fof(f290,plain,
    ( ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v5_pre_topc(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_tsep_1(sK6,sK7,sK8),sK3(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6) ),
    inference(subsumption_resolution,[],[f289,f134])).

fof(f289,plain,
    ( ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v5_pre_topc(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_tsep_1(sK6,sK7,sK8),sK3(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f288])).

fof(f288,plain,
    ( ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v5_pre_topc(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_tsep_1(sK6,sK7,sK8),sK3(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f287,f63])).

fof(f287,plain,
    ( ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v5_pre_topc(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_tsep_1(sK6,sK7,sK8),sK3(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6) ),
    inference(subsumption_resolution,[],[f286,f134])).

fof(f286,plain,
    ( sP0(sK8,sK7,sK6)
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v5_pre_topc(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_tsep_1(sK6,sK7,sK8),sK3(sK8,sK7,sK6))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f285])).

fof(f285,plain,
    ( sP0(sK8,sK7,sK6)
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v5_pre_topc(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_tsep_1(sK6,sK7,sK8),sK3(sK8,sK7,sK6))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f284,f60])).

fof(f284,plain,
    ( ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sP0(sK8,sK7,sK6)
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v5_pre_topc(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_tsep_1(sK6,sK7,sK8),sK3(sK8,sK7,sK6))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6)) ),
    inference(subsumption_resolution,[],[f283,f134])).

fof(f283,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sP0(sK8,sK7,sK6)
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v5_pre_topc(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_tsep_1(sK6,sK7,sK8),sK3(sK8,sK7,sK6))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f282])).

fof(f282,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sP0(sK8,sK7,sK6)
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v5_pre_topc(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_tsep_1(sK6,sK7,sK8),sK3(sK8,sK7,sK6))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f281,f64])).

fof(f281,plain,
    ( ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sP0(sK8,sK7,sK6)
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v5_pre_topc(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_tsep_1(sK6,sK7,sK8),sK3(sK8,sK7,sK6))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6)) ),
    inference(subsumption_resolution,[],[f280,f134])).

fof(f280,plain,
    ( ~ v5_pre_topc(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_tsep_1(sK6,sK7,sK8),sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sP0(sK8,sK7,sK6)
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(duplicate_literal_removal,[],[f279])).

fof(f279,plain,
    ( ~ v5_pre_topc(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_tsep_1(sK6,sK7,sK8),sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sP0(sK8,sK7,sK6)
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f278,f62])).

fof(f278,plain,
    ( ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_tsep_1(sK6,sK7,sK8),sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sP0(sK8,sK7,sK6)
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6)) ),
    inference(subsumption_resolution,[],[f277,f134])).

fof(f277,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_tsep_1(sK6,sK7,sK8),sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8)
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6)) ),
    inference(duplicate_literal_removal,[],[f276])).

fof(f276,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_tsep_1(sK6,sK7,sK8),sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8)
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sP0(sK8,sK7,sK6)
    | ~ v1_funct_1(sK5(sK8,sK7,sK6)) ),
    inference(resolution,[],[f67,f243])).

fof(f243,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k10_tmap_1(sK6,sK3(sK8,sK7,X1),sK7,sK8,X0,sK5(sK8,sK7,X1)))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,X1)))))
      | ~ v1_funct_2(X0,u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,X1)))
      | ~ v1_funct_2(sK5(sK8,sK7,X1),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,X1)))
      | sP0(sK8,sK7,X1)
      | ~ v1_funct_1(sK5(sK8,sK7,X1)) ) ),
    inference(subsumption_resolution,[],[f242,f134])).

fof(f242,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X0,u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,X1)))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,X1)))))
      | v1_funct_1(k10_tmap_1(sK6,sK3(sK8,sK7,X1),sK7,sK8,X0,sK5(sK8,sK7,X1)))
      | ~ v1_funct_2(sK5(sK8,sK7,X1),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,X1)))
      | sP0(sK8,sK7,X1)
      | ~ v1_funct_1(sK5(sK8,sK7,X1))
      | ~ r1_tsep_1(sK7,sK8) ) ),
    inference(duplicate_literal_removal,[],[f241])).

fof(f241,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X0,u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,X1)))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,X1)))))
      | v1_funct_1(k10_tmap_1(sK6,sK3(sK8,sK7,X1),sK7,sK8,X0,sK5(sK8,sK7,X1)))
      | ~ v1_funct_2(sK5(sK8,sK7,X1),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,X1)))
      | sP0(sK8,sK7,X1)
      | ~ v1_funct_1(sK5(sK8,sK7,X1))
      | sP0(sK8,sK7,X1)
      | ~ r1_tsep_1(sK7,sK8) ) ),
    inference(resolution,[],[f240,f66])).

fof(f240,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,X1)))))
      | ~ v1_funct_2(X0,u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,X1)))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,X1)))))
      | v1_funct_1(k10_tmap_1(sK6,sK3(sK8,sK7,X1),sK7,sK8,X0,X2))
      | ~ v1_funct_2(X2,u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,X1)))
      | sP0(sK8,sK7,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(resolution,[],[f207,f134])).

fof(f207,plain,(
    ! [X6,X4,X2,X5,X3] :
      ( ~ r1_tsep_1(X5,X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(X4,X5,X6)))))
      | ~ v1_funct_2(X3,u1_struct_0(sK7),u1_struct_0(sK3(X4,X5,X6)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(X4,X5,X6)))))
      | v1_funct_1(k10_tmap_1(sK6,sK3(X4,X5,X6),sK7,sK8,X3,X2))
      | ~ v1_funct_2(X2,u1_struct_0(sK8),u1_struct_0(sK3(X4,X5,X6)))
      | sP0(X4,X5,X6)
      | ~ v1_funct_1(X2) ) ),
    inference(subsumption_resolution,[],[f206,f56])).

fof(f206,plain,(
    ! [X6,X4,X2,X5,X3] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(X4,X5,X6)))))
      | ~ v1_funct_2(X3,u1_struct_0(sK7),u1_struct_0(sK3(X4,X5,X6)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(X4,X5,X6)))))
      | v1_funct_1(k10_tmap_1(sK6,sK3(X4,X5,X6),sK7,sK8,X3,X2))
      | ~ v1_funct_2(X2,u1_struct_0(sK8),u1_struct_0(sK3(X4,X5,X6)))
      | v2_struct_0(sK3(X4,X5,X6))
      | sP0(X4,X5,X6)
      | ~ r1_tsep_1(X5,X4) ) ),
    inference(subsumption_resolution,[],[f202,f57])).

fof(f202,plain,(
    ! [X6,X4,X2,X5,X3] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(X4,X5,X6)))))
      | ~ v1_funct_2(X3,u1_struct_0(sK7),u1_struct_0(sK3(X4,X5,X6)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(X4,X5,X6)))))
      | v1_funct_1(k10_tmap_1(sK6,sK3(X4,X5,X6),sK7,sK8,X3,X2))
      | ~ v1_funct_2(X2,u1_struct_0(sK8),u1_struct_0(sK3(X4,X5,X6)))
      | ~ v2_pre_topc(sK3(X4,X5,X6))
      | v2_struct_0(sK3(X4,X5,X6))
      | sP0(X4,X5,X6)
      | ~ r1_tsep_1(X5,X4) ) ),
    inference(resolution,[],[f191,f58])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),sK5(X0,X1,X2)))
      | ~ m1_subset_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),sK5(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2)))))
      | ~ v5_pre_topc(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),sK5(X0,X1,X2)),k1_tsep_1(X2,X1,X0),sK3(X0,X1,X2))
      | ~ v1_funct_2(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),sK5(X0,X1,X2)),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2)))
      | sP0(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f54,plain,(
    ! [X6,X2,X0,X8,X7,X1] :
      ( v5_pre_topc(k10_tmap_1(X2,X6,X1,X0,X7,X8),k1_tsep_1(X2,X1,X0),X6)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X6))))
      | ~ v5_pre_topc(X8,X0,X6)
      | ~ v1_funct_2(X8,u1_struct_0(X0),u1_struct_0(X6))
      | ~ v1_funct_1(X8)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X6))))
      | ~ v5_pre_topc(X7,X1,X6)
      | ~ v1_funct_2(X7,u1_struct_0(X1),u1_struct_0(X6))
      | ~ v1_funct_1(X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f76,plain,
    ( ~ sP0(sK8,sK7,sK6)
    | ~ r3_tsep_1(sK6,sK7,sK8) ),
    inference(cnf_transformation,[],[f40])).

fof(f726,plain,
    ( sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f725,f59])).

fof(f725,plain,(
    ~ v1_funct_1(sK4(sK8,sK7,sK6)) ),
    inference(subsumption_resolution,[],[f724,f134])).

fof(f724,plain,
    ( ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(subsumption_resolution,[],[f723,f666])).

fof(f723,plain,
    ( ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f722,f63])).

fof(f722,plain,
    ( ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6)) ),
    inference(subsumption_resolution,[],[f721,f134])).

fof(f721,plain,
    ( ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(subsumption_resolution,[],[f720,f666])).

fof(f720,plain,
    ( ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f719,f56])).

fof(f719,plain,
    ( v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6)) ),
    inference(subsumption_resolution,[],[f718,f134])).

fof(f718,plain,
    ( ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(subsumption_resolution,[],[f717,f666])).

fof(f717,plain,
    ( ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f716,f60])).

fof(f716,plain,
    ( ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6)) ),
    inference(subsumption_resolution,[],[f715,f134])).

fof(f715,plain,
    ( ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(subsumption_resolution,[],[f714,f666])).

fof(f714,plain,
    ( ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f713,f64])).

fof(f713,plain,
    ( ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6)) ),
    inference(subsumption_resolution,[],[f712,f134])).

fof(f712,plain,
    ( ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(subsumption_resolution,[],[f711,f666])).

fof(f711,plain,
    ( ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f710,f62])).

fof(f710,plain,
    ( ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) ),
    inference(subsumption_resolution,[],[f709,f134])).

fof(f709,plain,
    ( ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(subsumption_resolution,[],[f708,f666])).

fof(f708,plain,
    ( ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f707,f66])).

fof(f707,plain,
    ( ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) ),
    inference(subsumption_resolution,[],[f706,f134])).

fof(f706,plain,
    ( ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(subsumption_resolution,[],[f705,f666])).

fof(f705,plain,
    ( ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f704,f57])).

fof(f704,plain,
    ( ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) ),
    inference(subsumption_resolution,[],[f703,f134])).

fof(f703,plain,
    ( ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(subsumption_resolution,[],[f702,f666])).

fof(f702,plain,
    ( ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f701,f58])).

fof(f701,plain,
    ( ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6)) ),
    inference(subsumption_resolution,[],[f700,f68])).

fof(f700,plain,
    ( v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | v2_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f699,f69])).

fof(f699,plain,
    ( v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f698,f70])).

fof(f698,plain,
    ( v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f697,f71])).

fof(f697,plain,
    ( v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f696,f72])).

fof(f696,plain,
    ( v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ m1_pre_topc(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f695,f73])).

fof(f695,plain,
    ( v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f694,f74])).

fof(f694,plain,
    ( v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ m1_pre_topc(sK8,sK6)
    | v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(duplicate_literal_removal,[],[f691])).

fof(f691,plain,
    ( v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ m1_pre_topc(sK8,sK6)
    | v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(resolution,[],[f690,f111])).

fof(f690,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6)) ),
    inference(subsumption_resolution,[],[f689,f134])).

fof(f689,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(subsumption_resolution,[],[f688,f666])).

fof(f688,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f687,f59])).

fof(f687,plain,
    ( ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6)) ),
    inference(subsumption_resolution,[],[f686,f134])).

fof(f686,plain,
    ( ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(subsumption_resolution,[],[f685,f666])).

fof(f685,plain,
    ( ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f684,f63])).

fof(f684,plain,
    ( ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6)) ),
    inference(subsumption_resolution,[],[f683,f134])).

fof(f683,plain,
    ( ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(subsumption_resolution,[],[f682,f666])).

fof(f682,plain,
    ( ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f681,f60])).

fof(f681,plain,
    ( ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6)) ),
    inference(subsumption_resolution,[],[f680,f134])).

fof(f680,plain,
    ( ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(subsumption_resolution,[],[f679,f666])).

fof(f679,plain,
    ( ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f678,f64])).

fof(f678,plain,
    ( ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6)) ),
    inference(subsumption_resolution,[],[f677,f134])).

fof(f677,plain,
    ( ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(subsumption_resolution,[],[f676,f666])).

fof(f676,plain,
    ( ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f675,f62])).

fof(f675,plain,
    ( ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6)) ),
    inference(subsumption_resolution,[],[f674,f134])).

fof(f674,plain,
    ( ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(subsumption_resolution,[],[f673,f666])).

fof(f673,plain,
    ( ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f672,f66])).

fof(f672,plain,
    ( ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6)) ),
    inference(subsumption_resolution,[],[f671,f134])).

fof(f671,plain,
    ( ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(subsumption_resolution,[],[f670,f666])).

fof(f670,plain,
    ( ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f669,f57])).

fof(f669,plain,
    ( ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6)) ),
    inference(subsumption_resolution,[],[f668,f134])).

fof(f668,plain,
    ( v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(subsumption_resolution,[],[f667,f666])).

fof(f667,plain,
    ( v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f664,f58])).

fof(f664,plain,
    ( ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6)) ),
    inference(subsumption_resolution,[],[f663,f68])).

fof(f663,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | v2_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f662,f69])).

fof(f662,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f661,f70])).

fof(f661,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f660,f71])).

fof(f660,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f659,f72])).

fof(f659,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ m1_pre_topc(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f658,f73])).

fof(f658,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f657,f74])).

fof(f657,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ m1_pre_topc(sK8,sK6)
    | v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(duplicate_literal_removal,[],[f654])).

fof(f654,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ m1_pre_topc(sK8,sK6)
    | v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(resolution,[],[f653,f112])).

fof(f653,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6)) ),
    inference(global_subsumption,[],[f76,f613,f652])).

fof(f652,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6) ),
    inference(subsumption_resolution,[],[f651,f134])).

fof(f651,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f650,f59])).

fof(f650,plain,
    ( ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | v2_struct_0(sK3(sK8,sK7,sK6)) ),
    inference(global_subsumption,[],[f76,f613,f649])).

fof(f649,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6) ),
    inference(subsumption_resolution,[],[f648,f134])).

fof(f648,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f647,f63])).

fof(f647,plain,
    ( ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6)) ),
    inference(global_subsumption,[],[f76,f613,f646])).

fof(f646,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6) ),
    inference(subsumption_resolution,[],[f645,f134])).

fof(f645,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f644,f60])).

fof(f644,plain,
    ( ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6)) ),
    inference(global_subsumption,[],[f76,f613,f643])).

fof(f643,plain,
    ( ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sP0(sK8,sK7,sK6) ),
    inference(subsumption_resolution,[],[f642,f134])).

fof(f642,plain,
    ( ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f641,f64])).

fof(f641,plain,
    ( ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) ),
    inference(global_subsumption,[],[f76,f613,f640])).

fof(f640,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sP0(sK8,sK7,sK6) ),
    inference(subsumption_resolution,[],[f639,f134])).

fof(f639,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f638,f62])).

fof(f638,plain,
    ( ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) ),
    inference(global_subsumption,[],[f76,f613,f637])).

fof(f637,plain,
    ( ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sP0(sK8,sK7,sK6) ),
    inference(subsumption_resolution,[],[f636,f134])).

fof(f636,plain,
    ( ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f635,f66])).

fof(f635,plain,
    ( ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) ),
    inference(global_subsumption,[],[f76,f613,f634])).

fof(f634,plain,
    ( v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6) ),
    inference(subsumption_resolution,[],[f633,f134])).

fof(f633,plain,
    ( v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f632,f57])).

fof(f632,plain,
    ( ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) ),
    inference(global_subsumption,[],[f76,f613,f631])).

fof(f631,plain,
    ( ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sP0(sK8,sK7,sK6) ),
    inference(subsumption_resolution,[],[f630,f134])).

fof(f630,plain,
    ( ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f629,f58])).

fof(f629,plain,
    ( ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) ),
    inference(global_subsumption,[],[f76,f613,f628])).

fof(f628,plain,
    ( v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6) ),
    inference(subsumption_resolution,[],[f627,f134])).

fof(f627,plain,
    ( v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f626,f61])).

fof(f626,plain,
    ( ~ v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6)) ),
    inference(global_subsumption,[],[f76,f613,f625])).

fof(f625,plain,
    ( ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6) ),
    inference(subsumption_resolution,[],[f624,f134])).

fof(f624,plain,
    ( ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8) ),
    inference(resolution,[],[f615,f65])).

fof(f615,plain,
    ( ~ v5_pre_topc(sK5(sK8,sK7,sK6),sK8,sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK3(sK8,sK7,sK6))
    | v2_struct_0(sK3(sK8,sK7,sK6))
    | ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) ),
    inference(resolution,[],[f613,f320])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:36:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (13581)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.52  % (13586)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.53  % (13579)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.54  % (13599)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.54  % (13591)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.55  % (13584)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.55  % (13583)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.55  % (13587)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.55  % (13594)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.56  % (13595)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.56  % (13580)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.56  % (13597)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.56  % (13598)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.56  % (13577)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.56  % (13576)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.56  % (13576)Refutation not found, incomplete strategy% (13576)------------------------------
% 0.22/0.56  % (13576)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (13592)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.57  % (13590)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.57  % (13583)Refutation not found, incomplete strategy% (13583)------------------------------
% 0.22/0.57  % (13583)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (13583)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (13583)Memory used [KB]: 1791
% 0.22/0.57  % (13583)Time elapsed: 0.096 s
% 0.22/0.57  % (13583)------------------------------
% 0.22/0.57  % (13583)------------------------------
% 0.22/0.57  % (13589)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.57  % (13576)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (13576)Memory used [KB]: 10618
% 0.22/0.57  % (13576)Time elapsed: 0.138 s
% 0.22/0.57  % (13576)------------------------------
% 0.22/0.57  % (13576)------------------------------
% 0.22/0.57  % (13582)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.58  % (13582)Refutation not found, incomplete strategy% (13582)------------------------------
% 0.22/0.58  % (13582)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (13582)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (13582)Memory used [KB]: 10746
% 0.22/0.58  % (13582)Time elapsed: 0.153 s
% 0.22/0.58  % (13582)------------------------------
% 0.22/0.58  % (13582)------------------------------
% 0.22/0.58  % (13589)Refutation not found, incomplete strategy% (13589)------------------------------
% 0.22/0.58  % (13589)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (13589)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.59  
% 0.22/0.59  % (13589)Memory used [KB]: 6268
% 0.22/0.59  % (13589)Time elapsed: 0.160 s
% 0.22/0.59  % (13589)------------------------------
% 0.22/0.59  % (13589)------------------------------
% 0.22/0.59  % (13596)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.60  % (13588)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.60  % (13587)Refutation not found, incomplete strategy% (13587)------------------------------
% 0.22/0.60  % (13587)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.60  % (13587)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.60  
% 0.22/0.60  % (13587)Memory used [KB]: 11129
% 0.22/0.60  % (13587)Time elapsed: 0.177 s
% 0.22/0.60  % (13587)------------------------------
% 0.22/0.60  % (13587)------------------------------
% 0.22/0.60  % (13585)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.85/0.61  % (13601)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.85/0.62  % (13600)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.85/0.62  % (13593)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.85/0.62  % (13578)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 2.16/0.65  % (13597)Refutation found. Thanks to Tanya!
% 2.16/0.65  % SZS status Theorem for theBenchmark
% 2.16/0.65  % SZS output start Proof for theBenchmark
% 2.16/0.65  fof(f728,plain,(
% 2.16/0.65    $false),
% 2.16/0.65    inference(subsumption_resolution,[],[f727,f134])).
% 2.16/0.65  fof(f134,plain,(
% 2.16/0.65    r1_tsep_1(sK7,sK8)),
% 2.16/0.65    inference(subsumption_resolution,[],[f133,f84])).
% 2.16/0.65  fof(f84,plain,(
% 2.16/0.65    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | r1_tsep_1(X1,X0)) )),
% 2.16/0.65    inference(cnf_transformation,[],[f47])).
% 2.16/0.65  fof(f47,plain,(
% 2.16/0.65    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | (((~m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2))))) | ~v5_pre_topc(sK10(X0,X1,X2),k1_tsep_1(X2,X1,X0),sK9(X0,X1,X2)) | ~v1_funct_2(sK10(X0,X1,X2),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2))) | ~v1_funct_1(sK10(X0,X1,X2))) & m1_subset_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK9(X0,X1,X2))))) & v5_pre_topc(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)),X0,sK9(X0,X1,X2)) & v1_funct_2(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)),u1_struct_0(X0),u1_struct_0(sK9(X0,X1,X2))) & v1_funct_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2))) & m1_subset_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK9(X0,X1,X2))))) & v5_pre_topc(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)),X1,sK9(X0,X1,X2)) & v1_funct_2(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)),u1_struct_0(X1),u1_struct_0(sK9(X0,X1,X2))) & v1_funct_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2))) & m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2))))) & v1_funct_2(sK10(X0,X1,X2),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2))) & v1_funct_1(sK10(X0,X1,X2))) & l1_pre_topc(sK9(X0,X1,X2)) & v2_pre_topc(sK9(X0,X1,X2)) & ~v2_struct_0(sK9(X0,X1,X2))) | ~r1_tsep_1(X1,X0)) & ((! [X5] : (! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X5)))) & v5_pre_topc(X6,k1_tsep_1(X2,X1,X0),X5) & v1_funct_2(X6,u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X5)) & v1_funct_1(X6)) | ~m1_subset_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X0,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X5)))) | ~v5_pre_topc(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X0,X6),X0,X5) | ~v1_funct_2(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X0,X6),u1_struct_0(X0),u1_struct_0(X5)) | ~v1_funct_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X0,X6)) | ~m1_subset_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X1,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X5)))) | ~v5_pre_topc(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X1,X6),X1,X5) | ~v1_funct_2(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X1,X6),u1_struct_0(X1),u1_struct_0(X5)) | ~v1_funct_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X1,X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X5)))) | ~v1_funct_2(X6,u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X5)) | ~v1_funct_1(X6)) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) & r1_tsep_1(X1,X0)) | ~sP1(X0,X1,X2)))),
% 2.16/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f44,f46,f45])).
% 2.16/0.65  fof(f45,plain,(
% 2.16/0.65    ! [X2,X1,X0] : (? [X3] : (? [X4] : ((~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X3)))) | ~v5_pre_topc(X4,k1_tsep_1(X2,X1,X0),X3) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X3)) | ~v1_funct_1(X4)) & m1_subset_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X0,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3)))) & v5_pre_topc(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X0,X4),X0,X3) & v1_funct_2(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X0,X4),u1_struct_0(X0),u1_struct_0(X3)) & v1_funct_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X0,X4)) & m1_subset_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) & v5_pre_topc(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X1,X4),X1,X3) & v1_funct_2(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X1,X4),u1_struct_0(X1),u1_struct_0(X3)) & v1_funct_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X1,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X3)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X3)) & v1_funct_1(X4)) & l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) => (? [X4] : ((~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2))))) | ~v5_pre_topc(X4,k1_tsep_1(X2,X1,X0),sK9(X0,X1,X2)) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2))) | ~v1_funct_1(X4)) & m1_subset_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK9(X0,X1,X2))))) & v5_pre_topc(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,X4),X0,sK9(X0,X1,X2)) & v1_funct_2(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,X4),u1_struct_0(X0),u1_struct_0(sK9(X0,X1,X2))) & v1_funct_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,X4)) & m1_subset_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK9(X0,X1,X2))))) & v5_pre_topc(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,X4),X1,sK9(X0,X1,X2)) & v1_funct_2(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,X4),u1_struct_0(X1),u1_struct_0(sK9(X0,X1,X2))) & v1_funct_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2))))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2))) & v1_funct_1(X4)) & l1_pre_topc(sK9(X0,X1,X2)) & v2_pre_topc(sK9(X0,X1,X2)) & ~v2_struct_0(sK9(X0,X1,X2))))),
% 2.16/0.65    introduced(choice_axiom,[])).
% 2.16/0.65  fof(f46,plain,(
% 2.16/0.65    ! [X2,X1,X0] : (? [X4] : ((~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2))))) | ~v5_pre_topc(X4,k1_tsep_1(X2,X1,X0),sK9(X0,X1,X2)) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2))) | ~v1_funct_1(X4)) & m1_subset_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK9(X0,X1,X2))))) & v5_pre_topc(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,X4),X0,sK9(X0,X1,X2)) & v1_funct_2(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,X4),u1_struct_0(X0),u1_struct_0(sK9(X0,X1,X2))) & v1_funct_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,X4)) & m1_subset_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK9(X0,X1,X2))))) & v5_pre_topc(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,X4),X1,sK9(X0,X1,X2)) & v1_funct_2(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,X4),u1_struct_0(X1),u1_struct_0(sK9(X0,X1,X2))) & v1_funct_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2))))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2))) & v1_funct_1(X4)) => ((~m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2))))) | ~v5_pre_topc(sK10(X0,X1,X2),k1_tsep_1(X2,X1,X0),sK9(X0,X1,X2)) | ~v1_funct_2(sK10(X0,X1,X2),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2))) | ~v1_funct_1(sK10(X0,X1,X2))) & m1_subset_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK9(X0,X1,X2))))) & v5_pre_topc(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)),X0,sK9(X0,X1,X2)) & v1_funct_2(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)),u1_struct_0(X0),u1_struct_0(sK9(X0,X1,X2))) & v1_funct_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2))) & m1_subset_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK9(X0,X1,X2))))) & v5_pre_topc(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)),X1,sK9(X0,X1,X2)) & v1_funct_2(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)),u1_struct_0(X1),u1_struct_0(sK9(X0,X1,X2))) & v1_funct_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2))) & m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2))))) & v1_funct_2(sK10(X0,X1,X2),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2))) & v1_funct_1(sK10(X0,X1,X2))))),
% 2.16/0.65    introduced(choice_axiom,[])).
% 2.16/0.65  fof(f44,plain,(
% 2.16/0.65    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : (? [X4] : ((~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X3)))) | ~v5_pre_topc(X4,k1_tsep_1(X2,X1,X0),X3) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X3)) | ~v1_funct_1(X4)) & m1_subset_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X0,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3)))) & v5_pre_topc(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X0,X4),X0,X3) & v1_funct_2(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X0,X4),u1_struct_0(X0),u1_struct_0(X3)) & v1_funct_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X0,X4)) & m1_subset_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) & v5_pre_topc(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X1,X4),X1,X3) & v1_funct_2(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X1,X4),u1_struct_0(X1),u1_struct_0(X3)) & v1_funct_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X1,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X3)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X3)) & v1_funct_1(X4)) & l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) | ~r1_tsep_1(X1,X0)) & ((! [X5] : (! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X5)))) & v5_pre_topc(X6,k1_tsep_1(X2,X1,X0),X5) & v1_funct_2(X6,u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X5)) & v1_funct_1(X6)) | ~m1_subset_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X0,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X5)))) | ~v5_pre_topc(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X0,X6),X0,X5) | ~v1_funct_2(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X0,X6),u1_struct_0(X0),u1_struct_0(X5)) | ~v1_funct_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X0,X6)) | ~m1_subset_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X1,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X5)))) | ~v5_pre_topc(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X1,X6),X1,X5) | ~v1_funct_2(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X1,X6),u1_struct_0(X1),u1_struct_0(X5)) | ~v1_funct_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X1,X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X5)))) | ~v1_funct_2(X6,u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X5)) | ~v1_funct_1(X6)) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) & r1_tsep_1(X1,X0)) | ~sP1(X0,X1,X2)))),
% 2.16/0.65    inference(rectify,[],[f43])).
% 2.16/0.65  fof(f43,plain,(
% 2.16/0.65    ! [X2,X1,X0] : ((sP1(X2,X1,X0) | ? [X3] : (? [X4] : ((~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) | ~v1_funct_1(X4)) & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3) & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4)) & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3) & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3)) & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(X4)) & l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) | ~r1_tsep_1(X1,X2)) & ((! [X3] : (! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(X4)) | ~m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) | ~v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3) | ~v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3)) | ~v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4)) | ~m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3) | ~v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) | ~v1_funct_1(X4)) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) & r1_tsep_1(X1,X2)) | ~sP1(X2,X1,X0)))),
% 2.16/0.65    inference(flattening,[],[f42])).
% 2.16/0.65  fof(f42,plain,(
% 2.16/0.65    ! [X2,X1,X0] : ((sP1(X2,X1,X0) | (? [X3] : (? [X4] : ((~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) | ~v1_funct_1(X4)) & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3) & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4)) & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3) & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3)) & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(X4)) & l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) | ~r1_tsep_1(X1,X2))) & ((! [X3] : (! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(X4)) | ~m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) | ~v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3) | ~v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3)) | ~v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4)) | ~m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3) | ~v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) | ~v1_funct_1(X4)) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) & r1_tsep_1(X1,X2)) | ~sP1(X2,X1,X0)))),
% 2.16/0.65    inference(nnf_transformation,[],[f25])).
% 2.16/0.65  fof(f25,plain,(
% 2.16/0.65    ! [X2,X1,X0] : (sP1(X2,X1,X0) <=> (! [X3] : (! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(X4)) | ~m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) | ~v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3) | ~v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3)) | ~v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4)) | ~m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3) | ~v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) | ~v1_funct_1(X4)) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) & r1_tsep_1(X1,X2)))),
% 2.16/0.65    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.16/0.65  fof(f133,plain,(
% 2.16/0.65    sP1(sK8,sK7,sK6) | r1_tsep_1(sK7,sK8)),
% 2.16/0.65    inference(subsumption_resolution,[],[f132,f73])).
% 2.16/0.65  fof(f73,plain,(
% 2.16/0.65    ~v2_struct_0(sK8)),
% 2.16/0.65    inference(cnf_transformation,[],[f40])).
% 2.16/0.65  fof(f40,plain,(
% 2.16/0.65    (((~sP0(sK8,sK7,sK6) | ~r3_tsep_1(sK6,sK7,sK8)) & (sP0(sK8,sK7,sK6) | r3_tsep_1(sK6,sK7,sK8)) & m1_pre_topc(sK8,sK6) & ~v2_struct_0(sK8)) & m1_pre_topc(sK7,sK6) & ~v2_struct_0(sK7)) & l1_pre_topc(sK6) & v2_pre_topc(sK6) & ~v2_struct_0(sK6)),
% 2.16/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f36,f39,f38,f37])).
% 2.16/0.65  fof(f37,plain,(
% 2.16/0.65    ? [X0] : (? [X1] : (? [X2] : ((~sP0(X2,X1,X0) | ~r3_tsep_1(X0,X1,X2)) & (sP0(X2,X1,X0) | r3_tsep_1(X0,X1,X2)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~sP0(X2,X1,sK6) | ~r3_tsep_1(sK6,X1,X2)) & (sP0(X2,X1,sK6) | r3_tsep_1(sK6,X1,X2)) & m1_pre_topc(X2,sK6) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK6) & ~v2_struct_0(X1)) & l1_pre_topc(sK6) & v2_pre_topc(sK6) & ~v2_struct_0(sK6))),
% 2.16/0.65    introduced(choice_axiom,[])).
% 2.16/0.65  fof(f38,plain,(
% 2.16/0.65    ? [X1] : (? [X2] : ((~sP0(X2,X1,sK6) | ~r3_tsep_1(sK6,X1,X2)) & (sP0(X2,X1,sK6) | r3_tsep_1(sK6,X1,X2)) & m1_pre_topc(X2,sK6) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK6) & ~v2_struct_0(X1)) => (? [X2] : ((~sP0(X2,sK7,sK6) | ~r3_tsep_1(sK6,sK7,X2)) & (sP0(X2,sK7,sK6) | r3_tsep_1(sK6,sK7,X2)) & m1_pre_topc(X2,sK6) & ~v2_struct_0(X2)) & m1_pre_topc(sK7,sK6) & ~v2_struct_0(sK7))),
% 2.16/0.65    introduced(choice_axiom,[])).
% 2.16/0.65  fof(f39,plain,(
% 2.16/0.65    ? [X2] : ((~sP0(X2,sK7,sK6) | ~r3_tsep_1(sK6,sK7,X2)) & (sP0(X2,sK7,sK6) | r3_tsep_1(sK6,sK7,X2)) & m1_pre_topc(X2,sK6) & ~v2_struct_0(X2)) => ((~sP0(sK8,sK7,sK6) | ~r3_tsep_1(sK6,sK7,sK8)) & (sP0(sK8,sK7,sK6) | r3_tsep_1(sK6,sK7,sK8)) & m1_pre_topc(sK8,sK6) & ~v2_struct_0(sK8))),
% 2.16/0.65    introduced(choice_axiom,[])).
% 2.16/0.65  fof(f36,plain,(
% 2.16/0.65    ? [X0] : (? [X1] : (? [X2] : ((~sP0(X2,X1,X0) | ~r3_tsep_1(X0,X1,X2)) & (sP0(X2,X1,X0) | r3_tsep_1(X0,X1,X2)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.16/0.65    inference(flattening,[],[f35])).
% 2.16/0.65  fof(f35,plain,(
% 2.16/0.65    ? [X0] : (? [X1] : (? [X2] : (((~sP0(X2,X1,X0) | ~r3_tsep_1(X0,X1,X2)) & (sP0(X2,X1,X0) | r3_tsep_1(X0,X1,X2))) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.16/0.65    inference(nnf_transformation,[],[f24])).
% 2.16/0.65  fof(f24,plain,(
% 2.16/0.65    ? [X0] : (? [X1] : (? [X2] : ((r3_tsep_1(X0,X1,X2) <~> sP0(X2,X1,X0)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.16/0.65    inference(definition_folding,[],[f10,f23])).
% 2.16/0.65  fof(f23,plain,(
% 2.16/0.65    ! [X2,X1,X0] : (sP0(X2,X1,X0) <=> (! [X3] : (! [X4] : (! [X5] : ((m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) | ~v5_pre_topc(X5,X2,X3) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v5_pre_topc(X4,X1,X3) | ~v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(X4)) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) & r1_tsep_1(X1,X2)))),
% 2.16/0.65    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.16/0.65  fof(f10,plain,(
% 2.16/0.65    ? [X0] : (? [X1] : (? [X2] : ((r3_tsep_1(X0,X1,X2) <~> (! [X3] : (! [X4] : (! [X5] : ((m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) | ~v5_pre_topc(X5,X2,X3) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v5_pre_topc(X4,X1,X3) | ~v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(X4)) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) & r1_tsep_1(X1,X2))) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.16/0.65    inference(flattening,[],[f9])).
% 2.16/0.65  fof(f9,plain,(
% 2.16/0.65    ? [X0] : (? [X1] : (? [X2] : ((r3_tsep_1(X0,X1,X2) <~> (! [X3] : (! [X4] : (! [X5] : ((m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) | ~v5_pre_topc(X5,X2,X3) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v5_pre_topc(X4,X1,X3) | ~v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(X4))) | (~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3))) & r1_tsep_1(X1,X2))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.16/0.65    inference(ennf_transformation,[],[f8])).
% 2.16/0.65  fof(f8,negated_conjecture,(
% 2.16/0.65    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r3_tsep_1(X0,X1,X2) <=> (! [X3] : ((l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) & v5_pre_topc(X4,X1,X3) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v5_pre_topc(X5,X2,X3) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) => (m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)))))) & r1_tsep_1(X1,X2))))))),
% 2.16/0.65    inference(negated_conjecture,[],[f7])).
% 2.16/0.65  fof(f7,conjecture,(
% 2.16/0.65    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r3_tsep_1(X0,X1,X2) <=> (! [X3] : ((l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) & v5_pre_topc(X4,X1,X3) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v5_pre_topc(X5,X2,X3) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) => (m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)))))) & r1_tsep_1(X1,X2))))))),
% 2.16/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_tmap_1)).
% 2.16/0.65  fof(f132,plain,(
% 2.16/0.65    v2_struct_0(sK8) | sP1(sK8,sK7,sK6) | r1_tsep_1(sK7,sK8)),
% 2.16/0.65    inference(subsumption_resolution,[],[f131,f74])).
% 2.16/0.65  fof(f74,plain,(
% 2.16/0.65    m1_pre_topc(sK8,sK6)),
% 2.16/0.65    inference(cnf_transformation,[],[f40])).
% 2.16/0.65  fof(f131,plain,(
% 2.16/0.65    ~m1_pre_topc(sK8,sK6) | v2_struct_0(sK8) | sP1(sK8,sK7,sK6) | r1_tsep_1(sK7,sK8)),
% 2.16/0.65    inference(resolution,[],[f128,f115])).
% 2.16/0.65  fof(f115,plain,(
% 2.16/0.65    r3_tsep_1(sK6,sK7,sK8) | r1_tsep_1(sK7,sK8)),
% 2.16/0.65    inference(resolution,[],[f75,f51])).
% 2.16/0.65  fof(f51,plain,(
% 2.16/0.65    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r1_tsep_1(X1,X0)) )),
% 2.16/0.65    inference(cnf_transformation,[],[f34])).
% 2.16/0.65  fof(f34,plain,(
% 2.16/0.65    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((((~m1_subset_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),sK5(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2))))) | ~v5_pre_topc(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),sK5(X0,X1,X2)),k1_tsep_1(X2,X1,X0),sK3(X0,X1,X2)) | ~v1_funct_2(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),sK5(X0,X1,X2)),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2))) | ~v1_funct_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),sK5(X0,X1,X2)))) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2))))) & v5_pre_topc(sK5(X0,X1,X2),X0,sK3(X0,X1,X2)) & v1_funct_2(sK5(X0,X1,X2),u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2))) & v1_funct_1(sK5(X0,X1,X2))) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3(X0,X1,X2))))) & v5_pre_topc(sK4(X0,X1,X2),X1,sK3(X0,X1,X2)) & v1_funct_2(sK4(X0,X1,X2),u1_struct_0(X1),u1_struct_0(sK3(X0,X1,X2))) & v1_funct_1(sK4(X0,X1,X2))) & l1_pre_topc(sK3(X0,X1,X2)) & v2_pre_topc(sK3(X0,X1,X2)) & ~v2_struct_0(sK3(X0,X1,X2))) | ~r1_tsep_1(X1,X0)) & ((! [X6] : (! [X7] : (! [X8] : ((m1_subset_1(k10_tmap_1(X2,X6,X1,X0,X7,X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X6)))) & v5_pre_topc(k10_tmap_1(X2,X6,X1,X0,X7,X8),k1_tsep_1(X2,X1,X0),X6) & v1_funct_2(k10_tmap_1(X2,X6,X1,X0,X7,X8),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X6)) & v1_funct_1(k10_tmap_1(X2,X6,X1,X0,X7,X8))) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X6)))) | ~v5_pre_topc(X8,X0,X6) | ~v1_funct_2(X8,u1_struct_0(X0),u1_struct_0(X6)) | ~v1_funct_1(X8)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X6)))) | ~v5_pre_topc(X7,X1,X6) | ~v1_funct_2(X7,u1_struct_0(X1),u1_struct_0(X6)) | ~v1_funct_1(X7)) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) & r1_tsep_1(X1,X0)) | ~sP0(X0,X1,X2)))),
% 2.16/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f30,f33,f32,f31])).
% 2.16/0.65  fof(f31,plain,(
% 2.16/0.65    ! [X2,X1,X0] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X2,X3,X1,X0,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X3)))) | ~v5_pre_topc(k10_tmap_1(X2,X3,X1,X0,X4,X5),k1_tsep_1(X2,X1,X0),X3) | ~v1_funct_2(k10_tmap_1(X2,X3,X1,X0,X4,X5),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X3)) | ~v1_funct_1(k10_tmap_1(X2,X3,X1,X0,X4,X5))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3)))) & v5_pre_topc(X5,X0,X3) & v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) & v5_pre_topc(X4,X1,X3) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3)) & v1_funct_1(X4)) & l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2))))) | ~v5_pre_topc(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,X4,X5),k1_tsep_1(X2,X1,X0),sK3(X0,X1,X2)) | ~v1_funct_2(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,X4,X5),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2))) | ~v1_funct_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,X4,X5))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2))))) & v5_pre_topc(X5,X0,sK3(X0,X1,X2)) & v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2))) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3(X0,X1,X2))))) & v5_pre_topc(X4,X1,sK3(X0,X1,X2)) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(sK3(X0,X1,X2))) & v1_funct_1(X4)) & l1_pre_topc(sK3(X0,X1,X2)) & v2_pre_topc(sK3(X0,X1,X2)) & ~v2_struct_0(sK3(X0,X1,X2))))),
% 2.16/0.65    introduced(choice_axiom,[])).
% 2.16/0.65  fof(f32,plain,(
% 2.16/0.65    ! [X2,X1,X0] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2))))) | ~v5_pre_topc(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,X4,X5),k1_tsep_1(X2,X1,X0),sK3(X0,X1,X2)) | ~v1_funct_2(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,X4,X5),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2))) | ~v1_funct_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,X4,X5))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2))))) & v5_pre_topc(X5,X0,sK3(X0,X1,X2)) & v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2))) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3(X0,X1,X2))))) & v5_pre_topc(X4,X1,sK3(X0,X1,X2)) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(sK3(X0,X1,X2))) & v1_funct_1(X4)) => (? [X5] : ((~m1_subset_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2))))) | ~v5_pre_topc(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),X5),k1_tsep_1(X2,X1,X0),sK3(X0,X1,X2)) | ~v1_funct_2(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),X5),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2))) | ~v1_funct_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),X5))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2))))) & v5_pre_topc(X5,X0,sK3(X0,X1,X2)) & v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2))) & v1_funct_1(X5)) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3(X0,X1,X2))))) & v5_pre_topc(sK4(X0,X1,X2),X1,sK3(X0,X1,X2)) & v1_funct_2(sK4(X0,X1,X2),u1_struct_0(X1),u1_struct_0(sK3(X0,X1,X2))) & v1_funct_1(sK4(X0,X1,X2))))),
% 2.16/0.65    introduced(choice_axiom,[])).
% 2.16/0.65  fof(f33,plain,(
% 2.16/0.65    ! [X2,X1,X0] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2))))) | ~v5_pre_topc(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),X5),k1_tsep_1(X2,X1,X0),sK3(X0,X1,X2)) | ~v1_funct_2(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),X5),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2))) | ~v1_funct_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),X5))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2))))) & v5_pre_topc(X5,X0,sK3(X0,X1,X2)) & v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2))) & v1_funct_1(X5)) => ((~m1_subset_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),sK5(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2))))) | ~v5_pre_topc(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),sK5(X0,X1,X2)),k1_tsep_1(X2,X1,X0),sK3(X0,X1,X2)) | ~v1_funct_2(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),sK5(X0,X1,X2)),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2))) | ~v1_funct_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),sK5(X0,X1,X2)))) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2))))) & v5_pre_topc(sK5(X0,X1,X2),X0,sK3(X0,X1,X2)) & v1_funct_2(sK5(X0,X1,X2),u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2))) & v1_funct_1(sK5(X0,X1,X2))))),
% 2.16/0.65    introduced(choice_axiom,[])).
% 2.16/0.65  fof(f30,plain,(
% 2.16/0.65    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X2,X3,X1,X0,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X3)))) | ~v5_pre_topc(k10_tmap_1(X2,X3,X1,X0,X4,X5),k1_tsep_1(X2,X1,X0),X3) | ~v1_funct_2(k10_tmap_1(X2,X3,X1,X0,X4,X5),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X3)) | ~v1_funct_1(k10_tmap_1(X2,X3,X1,X0,X4,X5))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3)))) & v5_pre_topc(X5,X0,X3) & v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) & v5_pre_topc(X4,X1,X3) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3)) & v1_funct_1(X4)) & l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) | ~r1_tsep_1(X1,X0)) & ((! [X6] : (! [X7] : (! [X8] : ((m1_subset_1(k10_tmap_1(X2,X6,X1,X0,X7,X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X6)))) & v5_pre_topc(k10_tmap_1(X2,X6,X1,X0,X7,X8),k1_tsep_1(X2,X1,X0),X6) & v1_funct_2(k10_tmap_1(X2,X6,X1,X0,X7,X8),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X6)) & v1_funct_1(k10_tmap_1(X2,X6,X1,X0,X7,X8))) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X6)))) | ~v5_pre_topc(X8,X0,X6) | ~v1_funct_2(X8,u1_struct_0(X0),u1_struct_0(X6)) | ~v1_funct_1(X8)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X6)))) | ~v5_pre_topc(X7,X1,X6) | ~v1_funct_2(X7,u1_struct_0(X1),u1_struct_0(X6)) | ~v1_funct_1(X7)) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) & r1_tsep_1(X1,X0)) | ~sP0(X0,X1,X2)))),
% 2.16/0.65    inference(rectify,[],[f29])).
% 2.16/0.65  fof(f29,plain,(
% 2.16/0.65    ! [X2,X1,X0] : ((sP0(X2,X1,X0) | ? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) | ~v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3) | ~v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) | ~v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v5_pre_topc(X5,X2,X3) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) & v5_pre_topc(X4,X1,X3) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3)) & v1_funct_1(X4)) & l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) | ~r1_tsep_1(X1,X2)) & ((! [X3] : (! [X4] : (! [X5] : ((m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) | ~v5_pre_topc(X5,X2,X3) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v5_pre_topc(X4,X1,X3) | ~v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(X4)) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) & r1_tsep_1(X1,X2)) | ~sP0(X2,X1,X0)))),
% 2.16/0.65    inference(flattening,[],[f28])).
% 2.16/0.65  fof(f28,plain,(
% 2.16/0.65    ! [X2,X1,X0] : ((sP0(X2,X1,X0) | (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) | ~v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3) | ~v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) | ~v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v5_pre_topc(X5,X2,X3) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) & v5_pre_topc(X4,X1,X3) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3)) & v1_funct_1(X4)) & l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) | ~r1_tsep_1(X1,X2))) & ((! [X3] : (! [X4] : (! [X5] : ((m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) | ~v5_pre_topc(X5,X2,X3) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v5_pre_topc(X4,X1,X3) | ~v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(X4)) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) & r1_tsep_1(X1,X2)) | ~sP0(X2,X1,X0)))),
% 2.16/0.65    inference(nnf_transformation,[],[f23])).
% 2.16/0.65  fof(f75,plain,(
% 2.16/0.65    sP0(sK8,sK7,sK6) | r3_tsep_1(sK6,sK7,sK8)),
% 2.16/0.65    inference(cnf_transformation,[],[f40])).
% 2.16/0.65  fof(f128,plain,(
% 2.16/0.65    ( ! [X1] : (~r3_tsep_1(sK6,sK7,X1) | ~m1_pre_topc(X1,sK6) | v2_struct_0(X1) | sP1(X1,sK7,sK6)) )),
% 2.16/0.65    inference(resolution,[],[f122,f82])).
% 2.16/0.65  fof(f82,plain,(
% 2.16/0.65    ( ! [X2,X0,X1] : (~sP2(X0,X1,X2) | ~r3_tsep_1(X0,X1,X2) | sP1(X2,X1,X0)) )),
% 2.16/0.65    inference(cnf_transformation,[],[f41])).
% 2.16/0.65  fof(f41,plain,(
% 2.16/0.65    ! [X0,X1,X2] : (((r3_tsep_1(X0,X1,X2) | ~sP1(X2,X1,X0)) & (sP1(X2,X1,X0) | ~r3_tsep_1(X0,X1,X2))) | ~sP2(X0,X1,X2))),
% 2.16/0.65    inference(nnf_transformation,[],[f26])).
% 2.16/0.65  fof(f26,plain,(
% 2.16/0.65    ! [X0,X1,X2] : ((r3_tsep_1(X0,X1,X2) <=> sP1(X2,X1,X0)) | ~sP2(X0,X1,X2))),
% 2.16/0.65    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 2.16/0.65  fof(f122,plain,(
% 2.16/0.65    ( ! [X0] : (sP2(sK6,sK7,X0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK6)) )),
% 2.16/0.65    inference(subsumption_resolution,[],[f121,f68])).
% 2.16/0.65  fof(f68,plain,(
% 2.16/0.65    ~v2_struct_0(sK6)),
% 2.16/0.65    inference(cnf_transformation,[],[f40])).
% 2.16/0.65  fof(f121,plain,(
% 2.16/0.65    ( ! [X0] : (~m1_pre_topc(X0,sK6) | v2_struct_0(X0) | sP2(sK6,sK7,X0) | v2_struct_0(sK6)) )),
% 2.16/0.65    inference(subsumption_resolution,[],[f120,f69])).
% 2.16/0.65  fof(f69,plain,(
% 2.16/0.65    v2_pre_topc(sK6)),
% 2.16/0.65    inference(cnf_transformation,[],[f40])).
% 2.16/0.65  fof(f120,plain,(
% 2.16/0.65    ( ! [X0] : (~m1_pre_topc(X0,sK6) | v2_struct_0(X0) | sP2(sK6,sK7,X0) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)) )),
% 2.16/0.65    inference(subsumption_resolution,[],[f119,f70])).
% 2.16/0.65  fof(f70,plain,(
% 2.16/0.65    l1_pre_topc(sK6)),
% 2.16/0.65    inference(cnf_transformation,[],[f40])).
% 2.16/0.65  fof(f119,plain,(
% 2.16/0.65    ( ! [X0] : (~m1_pre_topc(X0,sK6) | v2_struct_0(X0) | sP2(sK6,sK7,X0) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)) )),
% 2.16/0.65    inference(subsumption_resolution,[],[f117,f71])).
% 2.16/0.65  fof(f71,plain,(
% 2.16/0.65    ~v2_struct_0(sK7)),
% 2.16/0.65    inference(cnf_transformation,[],[f40])).
% 2.16/0.65  fof(f117,plain,(
% 2.16/0.65    ( ! [X0] : (~m1_pre_topc(X0,sK6) | v2_struct_0(X0) | sP2(sK6,sK7,X0) | v2_struct_0(sK7) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)) )),
% 2.16/0.65    inference(resolution,[],[f104,f72])).
% 2.16/0.65  fof(f72,plain,(
% 2.16/0.65    m1_pre_topc(sK7,sK6)),
% 2.16/0.65    inference(cnf_transformation,[],[f40])).
% 2.16/0.65  fof(f104,plain,(
% 2.16/0.65    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | sP2(X0,X1,X2) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.16/0.65    inference(cnf_transformation,[],[f27])).
% 2.16/0.65  fof(f27,plain,(
% 2.16/0.65    ! [X0] : (! [X1] : (! [X2] : (sP2(X0,X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.16/0.65    inference(definition_folding,[],[f16,f26,f25])).
% 2.16/0.65  fof(f16,plain,(
% 2.16/0.65    ! [X0] : (! [X1] : (! [X2] : ((r3_tsep_1(X0,X1,X2) <=> (! [X3] : (! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(X4)) | ~m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) | ~v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3) | ~v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3)) | ~v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4)) | ~m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3) | ~v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) | ~v1_funct_1(X4)) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) & r1_tsep_1(X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.16/0.65    inference(flattening,[],[f15])).
% 2.16/0.65  fof(f15,plain,(
% 2.16/0.65    ! [X0] : (! [X1] : (! [X2] : ((r3_tsep_1(X0,X1,X2) <=> (! [X3] : (! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(X4)) | (~m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) | ~v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3) | ~v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3)) | ~v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4)) | ~m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3) | ~v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) | ~v1_funct_1(X4))) | (~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3))) & r1_tsep_1(X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.16/0.65    inference(ennf_transformation,[],[f3])).
% 2.16/0.65  fof(f3,axiom,(
% 2.16/0.65    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r3_tsep_1(X0,X1,X2) <=> (! [X3] : ((l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(X4)) => ((m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3) & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4)) & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3) & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3)) & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4))) => (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(X4))))) & r1_tsep_1(X1,X2))))))),
% 2.16/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_tmap_1)).
% 2.16/0.65  fof(f727,plain,(
% 2.16/0.65    ~r1_tsep_1(sK7,sK8)),
% 2.16/0.65    inference(subsumption_resolution,[],[f726,f666])).
% 2.16/0.65  fof(f666,plain,(
% 2.16/0.65    ~sP0(sK8,sK7,sK6)),
% 2.16/0.65    inference(global_subsumption,[],[f76,f613])).
% 2.16/0.65  fof(f613,plain,(
% 2.16/0.65    r3_tsep_1(sK6,sK7,sK8)),
% 2.16/0.65    inference(subsumption_resolution,[],[f612,f73])).
% 2.16/0.65  fof(f612,plain,(
% 2.16/0.65    r3_tsep_1(sK6,sK7,sK8) | v2_struct_0(sK8)),
% 2.16/0.65    inference(subsumption_resolution,[],[f611,f74])).
% 2.16/0.65  fof(f611,plain,(
% 2.16/0.65    r3_tsep_1(sK6,sK7,sK8) | ~m1_pre_topc(sK8,sK6) | v2_struct_0(sK8)),
% 2.16/0.65    inference(duplicate_literal_removal,[],[f608])).
% 2.16/0.65  fof(f608,plain,(
% 2.16/0.65    r3_tsep_1(sK6,sK7,sK8) | ~m1_pre_topc(sK8,sK6) | v2_struct_0(sK8) | r3_tsep_1(sK6,sK7,sK8)),
% 2.16/0.65    inference(resolution,[],[f607,f127])).
% 2.16/0.65  fof(f127,plain,(
% 2.16/0.65    ( ! [X0] : (~sP1(X0,sK7,sK6) | ~m1_pre_topc(X0,sK6) | v2_struct_0(X0) | r3_tsep_1(sK6,sK7,X0)) )),
% 2.16/0.65    inference(resolution,[],[f122,f83])).
% 2.34/0.65  fof(f83,plain,(
% 2.34/0.65    ( ! [X2,X0,X1] : (~sP2(X0,X1,X2) | ~sP1(X2,X1,X0) | r3_tsep_1(X0,X1,X2)) )),
% 2.34/0.65    inference(cnf_transformation,[],[f41])).
% 2.34/0.65  fof(f607,plain,(
% 2.34/0.65    sP1(sK8,sK7,sK6) | r3_tsep_1(sK6,sK7,sK8)),
% 2.34/0.65    inference(subsumption_resolution,[],[f606,f134])).
% 2.34/0.65  fof(f606,plain,(
% 2.34/0.65    r3_tsep_1(sK6,sK7,sK8) | sP1(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.65    inference(duplicate_literal_removal,[],[f605])).
% 2.34/0.65  fof(f605,plain,(
% 2.34/0.65    r3_tsep_1(sK6,sK7,sK8) | sP1(sK8,sK7,sK6) | sP1(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.65    inference(resolution,[],[f604,f89])).
% 2.34/0.65  fof(f89,plain,(
% 2.34/0.65    ( ! [X2,X0,X1] : (~v2_struct_0(sK9(X0,X1,X2)) | sP1(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 2.34/0.65    inference(cnf_transformation,[],[f47])).
% 2.34/0.65  fof(f604,plain,(
% 2.34/0.65    v2_struct_0(sK9(sK8,sK7,sK6)) | r3_tsep_1(sK6,sK7,sK8) | sP1(sK8,sK7,sK6)),
% 2.34/0.65    inference(subsumption_resolution,[],[f603,f134])).
% 2.34/0.65  fof(f603,plain,(
% 2.34/0.65    v2_struct_0(sK9(sK8,sK7,sK6)) | r3_tsep_1(sK6,sK7,sK8) | sP1(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.65    inference(duplicate_literal_removal,[],[f602])).
% 2.34/0.65  fof(f602,plain,(
% 2.34/0.65    v2_struct_0(sK9(sK8,sK7,sK6)) | r3_tsep_1(sK6,sK7,sK8) | sP1(sK8,sK7,sK6) | sP1(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.65    inference(resolution,[],[f601,f167])).
% 2.34/0.65  fof(f167,plain,(
% 2.34/0.65    ( ! [X2,X0,X1] : (~v5_pre_topc(sK10(X0,X1,X2),k1_tsep_1(X2,X1,X0),sK9(X0,X1,X2)) | sP1(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 2.34/0.65    inference(subsumption_resolution,[],[f166,f92])).
% 2.34/0.65  fof(f92,plain,(
% 2.34/0.65    ( ! [X2,X0,X1] : (v1_funct_1(sK10(X0,X1,X2)) | sP1(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 2.34/0.65    inference(cnf_transformation,[],[f47])).
% 2.34/0.65  fof(f166,plain,(
% 2.34/0.65    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | ~v5_pre_topc(sK10(X0,X1,X2),k1_tsep_1(X2,X1,X0),sK9(X0,X1,X2)) | ~v1_funct_1(sK10(X0,X1,X2)) | ~r1_tsep_1(X1,X0)) )),
% 2.34/0.65    inference(subsumption_resolution,[],[f165,f93])).
% 2.34/0.65  fof(f93,plain,(
% 2.34/0.65    ( ! [X2,X0,X1] : (v1_funct_2(sK10(X0,X1,X2),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2))) | sP1(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 2.34/0.65    inference(cnf_transformation,[],[f47])).
% 2.34/0.65  fof(f165,plain,(
% 2.34/0.65    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | ~v5_pre_topc(sK10(X0,X1,X2),k1_tsep_1(X2,X1,X0),sK9(X0,X1,X2)) | ~v1_funct_2(sK10(X0,X1,X2),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2))) | ~v1_funct_1(sK10(X0,X1,X2)) | ~r1_tsep_1(X1,X0)) )),
% 2.34/0.65    inference(subsumption_resolution,[],[f103,f94])).
% 2.34/0.65  fof(f94,plain,(
% 2.34/0.65    ( ! [X2,X0,X1] : (m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2))))) | sP1(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 2.34/0.65    inference(cnf_transformation,[],[f47])).
% 2.34/0.65  fof(f103,plain,(
% 2.34/0.65    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | ~m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2))))) | ~v5_pre_topc(sK10(X0,X1,X2),k1_tsep_1(X2,X1,X0),sK9(X0,X1,X2)) | ~v1_funct_2(sK10(X0,X1,X2),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2))) | ~v1_funct_1(sK10(X0,X1,X2)) | ~r1_tsep_1(X1,X0)) )),
% 2.34/0.65    inference(cnf_transformation,[],[f47])).
% 2.34/0.65  fof(f601,plain,(
% 2.34/0.65    v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6)) | v2_struct_0(sK9(sK8,sK7,sK6)) | r3_tsep_1(sK6,sK7,sK8) | sP1(sK8,sK7,sK6)),
% 2.34/0.65    inference(subsumption_resolution,[],[f600,f134])).
% 2.34/0.65  fof(f600,plain,(
% 2.34/0.65    v2_struct_0(sK9(sK8,sK7,sK6)) | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6)) | r3_tsep_1(sK6,sK7,sK8) | sP1(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.65    inference(duplicate_literal_removal,[],[f599])).
% 2.34/0.65  fof(f599,plain,(
% 2.34/0.65    v2_struct_0(sK9(sK8,sK7,sK6)) | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6)) | r3_tsep_1(sK6,sK7,sK8) | sP1(sK8,sK7,sK6) | sP1(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.65    inference(resolution,[],[f598,f95])).
% 2.34/0.65  fof(f95,plain,(
% 2.34/0.65    ( ! [X2,X0,X1] : (v1_funct_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2))) | sP1(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 2.34/0.65    inference(cnf_transformation,[],[f47])).
% 2.34/0.65  fof(f598,plain,(
% 2.34/0.65    ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | v2_struct_0(sK9(sK8,sK7,sK6)) | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6)) | r3_tsep_1(sK6,sK7,sK8) | sP1(sK8,sK7,sK6)),
% 2.34/0.65    inference(subsumption_resolution,[],[f597,f134])).
% 2.34/0.65  fof(f597,plain,(
% 2.34/0.65    ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | v2_struct_0(sK9(sK8,sK7,sK6)) | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6)) | r3_tsep_1(sK6,sK7,sK8) | sP1(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.65    inference(duplicate_literal_removal,[],[f596])).
% 2.34/0.65  fof(f596,plain,(
% 2.34/0.65    ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | v2_struct_0(sK9(sK8,sK7,sK6)) | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6)) | r3_tsep_1(sK6,sK7,sK8) | sP1(sK8,sK7,sK6) | sP1(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.65    inference(resolution,[],[f595,f99])).
% 2.34/0.65  fof(f99,plain,(
% 2.34/0.65    ( ! [X2,X0,X1] : (v1_funct_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2))) | sP1(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 2.34/0.65    inference(cnf_transformation,[],[f47])).
% 2.34/0.65  fof(f595,plain,(
% 2.34/0.65    ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | v2_struct_0(sK9(sK8,sK7,sK6)) | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6)) | r3_tsep_1(sK6,sK7,sK8) | sP1(sK8,sK7,sK6)),
% 2.34/0.65    inference(subsumption_resolution,[],[f594,f134])).
% 2.34/0.65  fof(f594,plain,(
% 2.34/0.65    ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK9(sK8,sK7,sK6)) | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6)) | r3_tsep_1(sK6,sK7,sK8) | sP1(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.65    inference(duplicate_literal_removal,[],[f593])).
% 2.34/0.65  fof(f593,plain,(
% 2.34/0.65    ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK9(sK8,sK7,sK6)) | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6)) | r3_tsep_1(sK6,sK7,sK8) | sP1(sK8,sK7,sK6) | sP1(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.65    inference(resolution,[],[f592,f96])).
% 2.34/0.65  fof(f96,plain,(
% 2.34/0.65    ( ! [X2,X0,X1] : (v1_funct_2(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)),u1_struct_0(X1),u1_struct_0(sK9(X0,X1,X2))) | sP1(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 2.34/0.65    inference(cnf_transformation,[],[f47])).
% 2.34/0.65  fof(f592,plain,(
% 2.34/0.65    ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK9(sK8,sK7,sK6)) | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6)) | r3_tsep_1(sK6,sK7,sK8) | sP1(sK8,sK7,sK6)),
% 2.34/0.65    inference(subsumption_resolution,[],[f591,f134])).
% 2.34/0.65  fof(f591,plain,(
% 2.34/0.65    ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK9(sK8,sK7,sK6)) | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6)) | r3_tsep_1(sK6,sK7,sK8) | sP1(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.65    inference(duplicate_literal_removal,[],[f590])).
% 2.34/0.65  fof(f590,plain,(
% 2.34/0.65    ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK9(sK8,sK7,sK6)) | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6)) | r3_tsep_1(sK6,sK7,sK8) | sP1(sK8,sK7,sK6) | sP1(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.65    inference(resolution,[],[f589,f100])).
% 2.34/0.65  fof(f100,plain,(
% 2.34/0.65    ( ! [X2,X0,X1] : (v1_funct_2(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)),u1_struct_0(X0),u1_struct_0(sK9(X0,X1,X2))) | sP1(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 2.34/0.65    inference(cnf_transformation,[],[f47])).
% 2.34/0.65  fof(f589,plain,(
% 2.34/0.65    ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK9(sK8,sK7,sK6)) | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6)) | r3_tsep_1(sK6,sK7,sK8) | sP1(sK8,sK7,sK6)),
% 2.34/0.65    inference(subsumption_resolution,[],[f588,f134])).
% 2.34/0.65  fof(f588,plain,(
% 2.34/0.65    ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK9(sK8,sK7,sK6)) | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6)) | r3_tsep_1(sK6,sK7,sK8) | sP1(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.65    inference(duplicate_literal_removal,[],[f587])).
% 2.34/0.65  fof(f587,plain,(
% 2.34/0.65    ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK9(sK8,sK7,sK6)) | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6)) | r3_tsep_1(sK6,sK7,sK8) | sP1(sK8,sK7,sK6) | sP1(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.65    inference(resolution,[],[f586,f98])).
% 2.34/0.65  fof(f98,plain,(
% 2.34/0.65    ( ! [X2,X0,X1] : (m1_subset_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK9(X0,X1,X2))))) | sP1(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 2.34/0.65    inference(cnf_transformation,[],[f47])).
% 2.34/0.65  fof(f586,plain,(
% 2.34/0.65    ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK9(sK8,sK7,sK6)) | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6)) | r3_tsep_1(sK6,sK7,sK8) | sP1(sK8,sK7,sK6)),
% 2.34/0.65    inference(subsumption_resolution,[],[f585,f134])).
% 2.34/0.65  fof(f585,plain,(
% 2.34/0.65    ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK9(sK8,sK7,sK6)) | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6)) | r3_tsep_1(sK6,sK7,sK8) | sP1(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.65    inference(duplicate_literal_removal,[],[f584])).
% 2.34/0.65  fof(f584,plain,(
% 2.34/0.65    ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK9(sK8,sK7,sK6)) | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6)) | r3_tsep_1(sK6,sK7,sK8) | sP1(sK8,sK7,sK6) | sP1(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.65    inference(resolution,[],[f583,f102])).
% 2.34/0.65  fof(f102,plain,(
% 2.34/0.65    ( ! [X2,X0,X1] : (m1_subset_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK9(X0,X1,X2))))) | sP1(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 2.34/0.65    inference(cnf_transformation,[],[f47])).
% 2.34/0.65  fof(f583,plain,(
% 2.34/0.65    ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK9(sK8,sK7,sK6)) | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6)) | r3_tsep_1(sK6,sK7,sK8) | sP1(sK8,sK7,sK6)),
% 2.34/0.65    inference(subsumption_resolution,[],[f582,f134])).
% 2.34/0.65  fof(f582,plain,(
% 2.34/0.65    ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK9(sK8,sK7,sK6)) | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6)) | r3_tsep_1(sK6,sK7,sK8) | sP1(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.65    inference(duplicate_literal_removal,[],[f581])).
% 2.34/0.65  fof(f581,plain,(
% 2.34/0.65    ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK9(sK8,sK7,sK6)) | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6)) | r3_tsep_1(sK6,sK7,sK8) | sP1(sK8,sK7,sK6) | sP1(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.65    inference(resolution,[],[f580,f90])).
% 2.34/0.65  fof(f90,plain,(
% 2.34/0.65    ( ! [X2,X0,X1] : (v2_pre_topc(sK9(X0,X1,X2)) | sP1(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 2.34/0.65    inference(cnf_transformation,[],[f47])).
% 2.34/0.65  fof(f580,plain,(
% 2.34/0.65    ~v2_pre_topc(sK9(sK8,sK7,sK6)) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK9(sK8,sK7,sK6)) | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6)) | r3_tsep_1(sK6,sK7,sK8) | sP1(sK8,sK7,sK6)),
% 2.34/0.65    inference(subsumption_resolution,[],[f579,f134])).
% 2.34/0.66  fof(f579,plain,(
% 2.34/0.66    ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v2_pre_topc(sK9(sK8,sK7,sK6)) | v2_struct_0(sK9(sK8,sK7,sK6)) | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6)) | r3_tsep_1(sK6,sK7,sK8) | sP1(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(duplicate_literal_removal,[],[f578])).
% 2.34/0.66  fof(f578,plain,(
% 2.34/0.66    ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v2_pre_topc(sK9(sK8,sK7,sK6)) | v2_struct_0(sK9(sK8,sK7,sK6)) | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6)) | r3_tsep_1(sK6,sK7,sK8) | sP1(sK8,sK7,sK6) | sP1(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(resolution,[],[f577,f91])).
% 2.34/0.66  fof(f91,plain,(
% 2.34/0.66    ( ! [X2,X0,X1] : (l1_pre_topc(sK9(X0,X1,X2)) | sP1(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 2.34/0.66    inference(cnf_transformation,[],[f47])).
% 2.34/0.66  fof(f577,plain,(
% 2.34/0.66    ~l1_pre_topc(sK9(sK8,sK7,sK6)) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v2_pre_topc(sK9(sK8,sK7,sK6)) | v2_struct_0(sK9(sK8,sK7,sK6)) | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6)) | r3_tsep_1(sK6,sK7,sK8) | sP1(sK8,sK7,sK6)),
% 2.34/0.66    inference(subsumption_resolution,[],[f576,f134])).
% 2.34/0.66  fof(f576,plain,(
% 2.34/0.66    ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~l1_pre_topc(sK9(sK8,sK7,sK6)) | ~v2_pre_topc(sK9(sK8,sK7,sK6)) | v2_struct_0(sK9(sK8,sK7,sK6)) | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6)) | r3_tsep_1(sK6,sK7,sK8) | sP1(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(duplicate_literal_removal,[],[f575])).
% 2.34/0.66  fof(f575,plain,(
% 2.34/0.66    ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~l1_pre_topc(sK9(sK8,sK7,sK6)) | ~v2_pre_topc(sK9(sK8,sK7,sK6)) | v2_struct_0(sK9(sK8,sK7,sK6)) | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6)) | r3_tsep_1(sK6,sK7,sK8) | sP1(sK8,sK7,sK6) | sP1(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(resolution,[],[f574,f97])).
% 2.34/0.66  fof(f97,plain,(
% 2.34/0.66    ( ! [X2,X0,X1] : (v5_pre_topc(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)),X1,sK9(X0,X1,X2)) | sP1(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 2.34/0.66    inference(cnf_transformation,[],[f47])).
% 2.34/0.66  fof(f574,plain,(
% 2.34/0.66    ~v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),sK7,sK9(sK8,sK7,sK6)) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~l1_pre_topc(sK9(sK8,sK7,sK6)) | ~v2_pre_topc(sK9(sK8,sK7,sK6)) | v2_struct_0(sK9(sK8,sK7,sK6)) | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6)) | r3_tsep_1(sK6,sK7,sK8) | sP1(sK8,sK7,sK6)),
% 2.34/0.66    inference(subsumption_resolution,[],[f573,f134])).
% 2.34/0.66  fof(f573,plain,(
% 2.34/0.66    ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),sK7,sK9(sK8,sK7,sK6)) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~l1_pre_topc(sK9(sK8,sK7,sK6)) | ~v2_pre_topc(sK9(sK8,sK7,sK6)) | v2_struct_0(sK9(sK8,sK7,sK6)) | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6)) | r3_tsep_1(sK6,sK7,sK8) | sP1(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(resolution,[],[f564,f101])).
% 2.34/0.66  fof(f101,plain,(
% 2.34/0.66    ( ! [X2,X0,X1] : (v5_pre_topc(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)),X0,sK9(X0,X1,X2)) | sP1(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 2.34/0.66    inference(cnf_transformation,[],[f47])).
% 2.34/0.66  fof(f564,plain,(
% 2.34/0.66    ~v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),sK8,sK9(sK8,sK7,sK6)) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),sK7,sK9(sK8,sK7,sK6)) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~l1_pre_topc(sK9(sK8,sK7,sK6)) | ~v2_pre_topc(sK9(sK8,sK7,sK6)) | v2_struct_0(sK9(sK8,sK7,sK6)) | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6)) | r3_tsep_1(sK6,sK7,sK8)),
% 2.34/0.66    inference(resolution,[],[f523,f75])).
% 2.34/0.66  fof(f523,plain,(
% 2.34/0.66    ~sP0(sK8,sK7,sK6) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),sK8,sK9(sK8,sK7,sK6)) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),sK7,sK9(sK8,sK7,sK6)) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~l1_pre_topc(sK9(sK8,sK7,sK6)) | ~v2_pre_topc(sK9(sK8,sK7,sK6)) | v2_struct_0(sK9(sK8,sK7,sK6)) | v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6))),
% 2.34/0.66    inference(superposition,[],[f54,f518])).
% 2.34/0.66  fof(f518,plain,(
% 2.34/0.66    sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))),
% 2.34/0.66    inference(subsumption_resolution,[],[f515,f402])).
% 2.34/0.66  fof(f402,plain,(
% 2.34/0.66    r3_tsep_1(sK6,sK7,sK8) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))),
% 2.34/0.66    inference(subsumption_resolution,[],[f401,f73])).
% 2.34/0.66  fof(f401,plain,(
% 2.34/0.66    sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | r3_tsep_1(sK6,sK7,sK8) | v2_struct_0(sK8)),
% 2.34/0.66    inference(subsumption_resolution,[],[f400,f74])).
% 2.34/0.66  fof(f400,plain,(
% 2.34/0.66    sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | r3_tsep_1(sK6,sK7,sK8) | ~m1_pre_topc(sK8,sK6) | v2_struct_0(sK8)),
% 2.34/0.66    inference(duplicate_literal_removal,[],[f397])).
% 2.34/0.66  fof(f397,plain,(
% 2.34/0.66    sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | r3_tsep_1(sK6,sK7,sK8) | ~m1_pre_topc(sK8,sK6) | v2_struct_0(sK8) | r3_tsep_1(sK6,sK7,sK8)),
% 2.34/0.66    inference(resolution,[],[f396,f127])).
% 2.34/0.66  fof(f396,plain,(
% 2.34/0.66    sP1(sK8,sK7,sK6) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | r3_tsep_1(sK6,sK7,sK8)),
% 2.34/0.66    inference(subsumption_resolution,[],[f395,f134])).
% 2.34/0.66  fof(f395,plain,(
% 2.34/0.66    sP1(sK8,sK7,sK6) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | r3_tsep_1(sK6,sK7,sK8) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(duplicate_literal_removal,[],[f394])).
% 2.34/0.66  fof(f394,plain,(
% 2.34/0.66    sP1(sK8,sK7,sK6) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | r3_tsep_1(sK6,sK7,sK8) | sP1(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(resolution,[],[f393,f89])).
% 2.34/0.66  fof(f393,plain,(
% 2.34/0.66    v2_struct_0(sK9(sK8,sK7,sK6)) | sP1(sK8,sK7,sK6) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | r3_tsep_1(sK6,sK7,sK8)),
% 2.34/0.66    inference(subsumption_resolution,[],[f392,f134])).
% 2.34/0.66  fof(f392,plain,(
% 2.34/0.66    v2_struct_0(sK9(sK8,sK7,sK6)) | sP1(sK8,sK7,sK6) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | r3_tsep_1(sK6,sK7,sK8) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(duplicate_literal_removal,[],[f391])).
% 2.34/0.66  fof(f391,plain,(
% 2.34/0.66    v2_struct_0(sK9(sK8,sK7,sK6)) | sP1(sK8,sK7,sK6) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | r3_tsep_1(sK6,sK7,sK8) | sP1(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(resolution,[],[f390,f95])).
% 2.34/0.66  fof(f390,plain,(
% 2.34/0.66    ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | v2_struct_0(sK9(sK8,sK7,sK6)) | sP1(sK8,sK7,sK6) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | r3_tsep_1(sK6,sK7,sK8)),
% 2.34/0.66    inference(subsumption_resolution,[],[f389,f134])).
% 2.34/0.66  fof(f389,plain,(
% 2.34/0.66    ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | v2_struct_0(sK9(sK8,sK7,sK6)) | sP1(sK8,sK7,sK6) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | r3_tsep_1(sK6,sK7,sK8) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(duplicate_literal_removal,[],[f388])).
% 2.34/0.66  fof(f388,plain,(
% 2.34/0.66    ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | v2_struct_0(sK9(sK8,sK7,sK6)) | sP1(sK8,sK7,sK6) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | r3_tsep_1(sK6,sK7,sK8) | sP1(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(resolution,[],[f387,f99])).
% 2.34/0.66  fof(f387,plain,(
% 2.34/0.66    ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | v2_struct_0(sK9(sK8,sK7,sK6)) | sP1(sK8,sK7,sK6) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | r3_tsep_1(sK6,sK7,sK8)),
% 2.34/0.66    inference(subsumption_resolution,[],[f386,f134])).
% 2.34/0.66  fof(f386,plain,(
% 2.34/0.66    v2_struct_0(sK9(sK8,sK7,sK6)) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | r3_tsep_1(sK6,sK7,sK8) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(duplicate_literal_removal,[],[f385])).
% 2.34/0.66  fof(f385,plain,(
% 2.34/0.66    v2_struct_0(sK9(sK8,sK7,sK6)) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | r3_tsep_1(sK6,sK7,sK8) | sP1(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(resolution,[],[f384,f96])).
% 2.34/0.66  fof(f384,plain,(
% 2.34/0.66    ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | v2_struct_0(sK9(sK8,sK7,sK6)) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | r3_tsep_1(sK6,sK7,sK8)),
% 2.34/0.66    inference(subsumption_resolution,[],[f383,f134])).
% 2.34/0.66  fof(f383,plain,(
% 2.34/0.66    v2_struct_0(sK9(sK8,sK7,sK6)) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | r3_tsep_1(sK6,sK7,sK8) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(duplicate_literal_removal,[],[f382])).
% 2.34/0.66  fof(f382,plain,(
% 2.34/0.66    v2_struct_0(sK9(sK8,sK7,sK6)) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | r3_tsep_1(sK6,sK7,sK8) | sP1(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(resolution,[],[f381,f100])).
% 2.34/0.66  fof(f381,plain,(
% 2.34/0.66    ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | v2_struct_0(sK9(sK8,sK7,sK6)) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | r3_tsep_1(sK6,sK7,sK8)),
% 2.34/0.66    inference(subsumption_resolution,[],[f380,f134])).
% 2.34/0.66  fof(f380,plain,(
% 2.34/0.66    ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK9(sK8,sK7,sK6)) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | r3_tsep_1(sK6,sK7,sK8) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(duplicate_literal_removal,[],[f379])).
% 2.34/0.66  fof(f379,plain,(
% 2.34/0.66    ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK9(sK8,sK7,sK6)) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | r3_tsep_1(sK6,sK7,sK8) | sP1(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(resolution,[],[f378,f98])).
% 2.34/0.66  fof(f378,plain,(
% 2.34/0.66    ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK9(sK8,sK7,sK6)) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | r3_tsep_1(sK6,sK7,sK8)),
% 2.34/0.66    inference(subsumption_resolution,[],[f377,f134])).
% 2.34/0.66  fof(f377,plain,(
% 2.34/0.66    ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | v2_struct_0(sK9(sK8,sK7,sK6)) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | r3_tsep_1(sK6,sK7,sK8) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(duplicate_literal_removal,[],[f376])).
% 2.34/0.66  fof(f376,plain,(
% 2.34/0.66    ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | v2_struct_0(sK9(sK8,sK7,sK6)) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | r3_tsep_1(sK6,sK7,sK8) | sP1(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(resolution,[],[f375,f102])).
% 2.34/0.66  fof(f375,plain,(
% 2.34/0.66    ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | v2_struct_0(sK9(sK8,sK7,sK6)) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | r3_tsep_1(sK6,sK7,sK8)),
% 2.34/0.66    inference(subsumption_resolution,[],[f374,f134])).
% 2.34/0.66  fof(f374,plain,(
% 2.34/0.66    ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | v2_struct_0(sK9(sK8,sK7,sK6)) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))))) | sP1(sK8,sK7,sK6) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | r3_tsep_1(sK6,sK7,sK8) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(duplicate_literal_removal,[],[f373])).
% 2.34/0.66  fof(f373,plain,(
% 2.34/0.66    ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | v2_struct_0(sK9(sK8,sK7,sK6)) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))))) | sP1(sK8,sK7,sK6) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | r3_tsep_1(sK6,sK7,sK8) | sP1(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(resolution,[],[f372,f90])).
% 2.34/0.66  fof(f372,plain,(
% 2.34/0.66    ~v2_pre_topc(sK9(sK8,sK7,sK6)) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | v2_struct_0(sK9(sK8,sK7,sK6)) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))))) | sP1(sK8,sK7,sK6) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | r3_tsep_1(sK6,sK7,sK8)),
% 2.34/0.66    inference(subsumption_resolution,[],[f371,f134])).
% 2.34/0.66  fof(f371,plain,(
% 2.34/0.66    sP1(sK8,sK7,sK6) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | v2_struct_0(sK9(sK8,sK7,sK6)) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v2_pre_topc(sK9(sK8,sK7,sK6)) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | r3_tsep_1(sK6,sK7,sK8) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(duplicate_literal_removal,[],[f370])).
% 2.34/0.66  fof(f370,plain,(
% 2.34/0.66    sP1(sK8,sK7,sK6) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | v2_struct_0(sK9(sK8,sK7,sK6)) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v2_pre_topc(sK9(sK8,sK7,sK6)) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | r3_tsep_1(sK6,sK7,sK8) | sP1(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(resolution,[],[f369,f91])).
% 2.34/0.66  fof(f369,plain,(
% 2.34/0.66    ~l1_pre_topc(sK9(sK8,sK7,sK6)) | sP1(sK8,sK7,sK6) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | v2_struct_0(sK9(sK8,sK7,sK6)) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v2_pre_topc(sK9(sK8,sK7,sK6)) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | r3_tsep_1(sK6,sK7,sK8)),
% 2.34/0.66    inference(subsumption_resolution,[],[f368,f134])).
% 2.34/0.66  fof(f368,plain,(
% 2.34/0.66    ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))))) | sP1(sK8,sK7,sK6) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | v2_struct_0(sK9(sK8,sK7,sK6)) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~l1_pre_topc(sK9(sK8,sK7,sK6)) | ~v2_pre_topc(sK9(sK8,sK7,sK6)) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | r3_tsep_1(sK6,sK7,sK8) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(duplicate_literal_removal,[],[f367])).
% 2.34/0.66  fof(f367,plain,(
% 2.34/0.66    ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))))) | sP1(sK8,sK7,sK6) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | v2_struct_0(sK9(sK8,sK7,sK6)) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~l1_pre_topc(sK9(sK8,sK7,sK6)) | ~v2_pre_topc(sK9(sK8,sK7,sK6)) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | r3_tsep_1(sK6,sK7,sK8) | sP1(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(resolution,[],[f366,f97])).
% 2.34/0.66  fof(f366,plain,(
% 2.34/0.66    ~v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),sK7,sK9(sK8,sK7,sK6)) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))))) | sP1(sK8,sK7,sK6) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | v2_struct_0(sK9(sK8,sK7,sK6)) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~l1_pre_topc(sK9(sK8,sK7,sK6)) | ~v2_pre_topc(sK9(sK8,sK7,sK6)) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | r3_tsep_1(sK6,sK7,sK8)),
% 2.34/0.66    inference(subsumption_resolution,[],[f365,f134])).
% 2.34/0.66  fof(f365,plain,(
% 2.34/0.66    v2_struct_0(sK9(sK8,sK7,sK6)) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))))) | sP1(sK8,sK7,sK6) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),sK7,sK9(sK8,sK7,sK6)) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~l1_pre_topc(sK9(sK8,sK7,sK6)) | ~v2_pre_topc(sK9(sK8,sK7,sK6)) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | r3_tsep_1(sK6,sK7,sK8) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(duplicate_literal_removal,[],[f364])).
% 2.34/0.66  fof(f364,plain,(
% 2.34/0.66    v2_struct_0(sK9(sK8,sK7,sK6)) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))))) | sP1(sK8,sK7,sK6) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),sK7,sK9(sK8,sK7,sK6)) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~l1_pre_topc(sK9(sK8,sK7,sK6)) | ~v2_pre_topc(sK9(sK8,sK7,sK6)) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | r3_tsep_1(sK6,sK7,sK8) | sP1(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(resolution,[],[f363,f101])).
% 2.34/0.66  fof(f363,plain,(
% 2.34/0.66    ~v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),sK8,sK9(sK8,sK7,sK6)) | v2_struct_0(sK9(sK8,sK7,sK6)) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))))) | sP1(sK8,sK7,sK6) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),sK7,sK9(sK8,sK7,sK6)) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~l1_pre_topc(sK9(sK8,sK7,sK6)) | ~v2_pre_topc(sK9(sK8,sK7,sK6)) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | r3_tsep_1(sK6,sK7,sK8)),
% 2.34/0.66    inference(resolution,[],[f362,f75])).
% 2.34/0.66  fof(f362,plain,(
% 2.34/0.66    ~sP0(sK8,sK7,sK6) | sP1(sK8,sK7,sK6) | v2_struct_0(sK9(sK8,sK7,sK6)) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),sK8,sK9(sK8,sK7,sK6)) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),sK7,sK9(sK8,sK7,sK6)) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~l1_pre_topc(sK9(sK8,sK7,sK6)) | ~v2_pre_topc(sK9(sK8,sK7,sK6)) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))),
% 2.34/0.66    inference(subsumption_resolution,[],[f353,f53])).
% 2.34/0.66  fof(f53,plain,(
% 2.34/0.66    ( ! [X6,X2,X0,X8,X7,X1] : (v1_funct_2(k10_tmap_1(X2,X6,X1,X0,X7,X8),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X6)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X6)))) | ~v5_pre_topc(X8,X0,X6) | ~v1_funct_2(X8,u1_struct_0(X0),u1_struct_0(X6)) | ~v1_funct_1(X8) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X6)))) | ~v5_pre_topc(X7,X1,X6) | ~v1_funct_2(X7,u1_struct_0(X1),u1_struct_0(X6)) | ~v1_funct_1(X7) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6) | ~sP0(X0,X1,X2)) )),
% 2.34/0.66    inference(cnf_transformation,[],[f34])).
% 2.34/0.66  fof(f353,plain,(
% 2.34/0.66    ~v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | v2_struct_0(sK9(sK8,sK7,sK6)) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),sK8,sK9(sK8,sK7,sK6)) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),sK7,sK9(sK8,sK7,sK6)) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~l1_pre_topc(sK9(sK8,sK7,sK6)) | ~v2_pre_topc(sK9(sK8,sK7,sK6)) | ~sP0(sK8,sK7,sK6)),
% 2.34/0.66    inference(duplicate_literal_removal,[],[f352])).
% 2.34/0.66  fof(f352,plain,(
% 2.34/0.66    ~v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | v2_struct_0(sK9(sK8,sK7,sK6)) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),sK8,sK9(sK8,sK7,sK6)) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),sK7,sK9(sK8,sK7,sK6)) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~l1_pre_topc(sK9(sK8,sK7,sK6)) | ~v2_pre_topc(sK9(sK8,sK7,sK6)) | v2_struct_0(sK9(sK8,sK7,sK6)) | ~sP0(sK8,sK7,sK6)),
% 2.34/0.66    inference(resolution,[],[f350,f55])).
% 2.34/0.66  fof(f55,plain,(
% 2.34/0.66    ( ! [X6,X2,X0,X8,X7,X1] : (m1_subset_1(k10_tmap_1(X2,X6,X1,X0,X7,X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X6)))) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X6)))) | ~v5_pre_topc(X8,X0,X6) | ~v1_funct_2(X8,u1_struct_0(X0),u1_struct_0(X6)) | ~v1_funct_1(X8) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X6)))) | ~v5_pre_topc(X7,X1,X6) | ~v1_funct_2(X7,u1_struct_0(X1),u1_struct_0(X6)) | ~v1_funct_1(X7) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6) | ~sP0(X0,X1,X2)) )),
% 2.34/0.66    inference(cnf_transformation,[],[f34])).
% 2.34/0.66  fof(f350,plain,(
% 2.34/0.66    ~m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | v2_struct_0(sK9(sK8,sK7,sK6))),
% 2.34/0.66    inference(subsumption_resolution,[],[f349,f134])).
% 2.34/0.66  fof(f349,plain,(
% 2.34/0.66    ~v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | v2_struct_0(sK9(sK8,sK7,sK6)) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(duplicate_literal_removal,[],[f348])).
% 2.34/0.66  fof(f348,plain,(
% 2.34/0.66    ~v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | v2_struct_0(sK9(sK8,sK7,sK6)) | sP1(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(resolution,[],[f347,f95])).
% 2.34/0.66  fof(f347,plain,(
% 2.34/0.66    ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | v2_struct_0(sK9(sK8,sK7,sK6))),
% 2.34/0.66    inference(subsumption_resolution,[],[f346,f134])).
% 2.34/0.66  fof(f346,plain,(
% 2.34/0.66    ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | v2_struct_0(sK9(sK8,sK7,sK6)) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(duplicate_literal_removal,[],[f345])).
% 2.34/0.66  fof(f345,plain,(
% 2.34/0.66    ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | v2_struct_0(sK9(sK8,sK7,sK6)) | sP1(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(resolution,[],[f344,f99])).
% 2.34/0.66  fof(f344,plain,(
% 2.34/0.66    ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | v2_struct_0(sK9(sK8,sK7,sK6))),
% 2.34/0.66    inference(subsumption_resolution,[],[f343,f134])).
% 2.34/0.66  fof(f343,plain,(
% 2.34/0.66    v2_struct_0(sK9(sK8,sK7,sK6)) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(duplicate_literal_removal,[],[f342])).
% 2.34/0.66  fof(f342,plain,(
% 2.34/0.66    v2_struct_0(sK9(sK8,sK7,sK6)) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(resolution,[],[f341,f92])).
% 2.34/0.66  fof(f341,plain,(
% 2.34/0.66    ~v1_funct_1(sK10(sK8,sK7,sK6)) | v2_struct_0(sK9(sK8,sK7,sK6)) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))),
% 2.34/0.66    inference(subsumption_resolution,[],[f340,f134])).
% 2.34/0.66  fof(f340,plain,(
% 2.34/0.66    ~v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | v2_struct_0(sK9(sK8,sK7,sK6)) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~v1_funct_1(sK10(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(duplicate_literal_removal,[],[f339])).
% 2.34/0.66  fof(f339,plain,(
% 2.34/0.66    ~v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | v2_struct_0(sK9(sK8,sK7,sK6)) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~v1_funct_1(sK10(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(resolution,[],[f338,f96])).
% 2.34/0.66  fof(f338,plain,(
% 2.34/0.66    ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | v2_struct_0(sK9(sK8,sK7,sK6)) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~v1_funct_1(sK10(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))),
% 2.34/0.66    inference(subsumption_resolution,[],[f337,f134])).
% 2.34/0.66  fof(f337,plain,(
% 2.34/0.66    ~m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | v2_struct_0(sK9(sK8,sK7,sK6)) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~v1_funct_1(sK10(sK8,sK7,sK6)) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(duplicate_literal_removal,[],[f336])).
% 2.34/0.66  fof(f336,plain,(
% 2.34/0.66    ~m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | v2_struct_0(sK9(sK8,sK7,sK6)) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~v1_funct_1(sK10(sK8,sK7,sK6)) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(resolution,[],[f335,f100])).
% 2.34/0.66  fof(f335,plain,(
% 2.34/0.66    ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | v2_struct_0(sK9(sK8,sK7,sK6)) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~v1_funct_1(sK10(sK8,sK7,sK6)) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))),
% 2.34/0.66    inference(subsumption_resolution,[],[f334,f134])).
% 2.34/0.66  fof(f334,plain,(
% 2.34/0.66    sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | v2_struct_0(sK9(sK8,sK7,sK6)) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~v1_funct_1(sK10(sK8,sK7,sK6)) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(duplicate_literal_removal,[],[f333])).
% 2.34/0.66  fof(f333,plain,(
% 2.34/0.66    sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | v2_struct_0(sK9(sK8,sK7,sK6)) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~v1_funct_1(sK10(sK8,sK7,sK6)) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(resolution,[],[f332,f93])).
% 2.34/0.66  fof(f332,plain,(
% 2.34/0.66    ~v1_funct_2(sK10(sK8,sK7,sK6),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | v2_struct_0(sK9(sK8,sK7,sK6)) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~v1_funct_1(sK10(sK8,sK7,sK6)) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))),
% 2.34/0.66    inference(subsumption_resolution,[],[f331,f134])).
% 2.34/0.66  fof(f331,plain,(
% 2.34/0.66    v2_struct_0(sK9(sK8,sK7,sK6)) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_2(sK10(sK8,sK7,sK6),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~v1_funct_1(sK10(sK8,sK7,sK6)) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(duplicate_literal_removal,[],[f330])).
% 2.34/0.66  fof(f330,plain,(
% 2.34/0.66    v2_struct_0(sK9(sK8,sK7,sK6)) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_2(sK10(sK8,sK7,sK6),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~v1_funct_1(sK10(sK8,sK7,sK6)) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(resolution,[],[f329,f98])).
% 2.34/0.66  fof(f329,plain,(
% 2.34/0.66    ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | v2_struct_0(sK9(sK8,sK7,sK6)) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_2(sK10(sK8,sK7,sK6),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~v1_funct_1(sK10(sK8,sK7,sK6)) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))),
% 2.34/0.66    inference(subsumption_resolution,[],[f328,f134])).
% 2.34/0.66  fof(f328,plain,(
% 2.34/0.66    ~v1_funct_1(sK10(sK8,sK7,sK6)) | v2_struct_0(sK9(sK8,sK7,sK6)) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_2(sK10(sK8,sK7,sK6),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(duplicate_literal_removal,[],[f327])).
% 2.34/0.66  fof(f327,plain,(
% 2.34/0.66    ~v1_funct_1(sK10(sK8,sK7,sK6)) | v2_struct_0(sK9(sK8,sK7,sK6)) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_2(sK10(sK8,sK7,sK6),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(resolution,[],[f326,f94])).
% 2.34/0.66  fof(f326,plain,(
% 2.34/0.66    ~m1_subset_1(sK10(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_1(sK10(sK8,sK7,sK6)) | v2_struct_0(sK9(sK8,sK7,sK6)) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_2(sK10(sK8,sK7,sK6),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))),
% 2.34/0.66    inference(subsumption_resolution,[],[f325,f134])).
% 2.34/0.66  fof(f325,plain,(
% 2.34/0.66    ~v1_funct_2(sK10(sK8,sK7,sK6),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(sK10(sK8,sK7,sK6)) | v2_struct_0(sK9(sK8,sK7,sK6)) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | ~m1_subset_1(sK10(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(duplicate_literal_removal,[],[f324])).
% 2.34/0.66  fof(f324,plain,(
% 2.34/0.66    ~v1_funct_2(sK10(sK8,sK7,sK6),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(sK10(sK8,sK7,sK6)) | v2_struct_0(sK9(sK8,sK7,sK6)) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | ~m1_subset_1(sK10(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(resolution,[],[f323,f90])).
% 2.34/0.66  fof(f323,plain,(
% 2.34/0.66    ~v2_pre_topc(sK9(sK8,sK7,sK6)) | ~v1_funct_2(sK10(sK8,sK7,sK6),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(sK10(sK8,sK7,sK6)) | v2_struct_0(sK9(sK8,sK7,sK6)) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | ~m1_subset_1(sK10(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))),
% 2.34/0.66    inference(subsumption_resolution,[],[f322,f134])).
% 2.34/0.66  fof(f322,plain,(
% 2.34/0.66    ~v1_funct_1(sK10(sK8,sK7,sK6)) | ~v1_funct_2(sK10(sK8,sK7,sK6),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v2_pre_topc(sK9(sK8,sK7,sK6)) | v2_struct_0(sK9(sK8,sK7,sK6)) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | ~m1_subset_1(sK10(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(duplicate_literal_removal,[],[f321])).
% 2.34/0.66  fof(f321,plain,(
% 2.34/0.66    ~v1_funct_1(sK10(sK8,sK7,sK6)) | ~v1_funct_2(sK10(sK8,sK7,sK6),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v2_pre_topc(sK9(sK8,sK7,sK6)) | v2_struct_0(sK9(sK8,sK7,sK6)) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | ~m1_subset_1(sK10(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(resolution,[],[f311,f91])).
% 2.34/0.66  fof(f311,plain,(
% 2.34/0.66    ~l1_pre_topc(sK9(sK8,sK7,sK6)) | ~v1_funct_1(sK10(sK8,sK7,sK6)) | ~v1_funct_2(sK10(sK8,sK7,sK6),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v2_pre_topc(sK9(sK8,sK7,sK6)) | v2_struct_0(sK9(sK8,sK7,sK6)) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | ~m1_subset_1(sK10(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))),
% 2.34/0.66    inference(subsumption_resolution,[],[f310,f68])).
% 2.34/0.66  fof(f310,plain,(
% 2.34/0.66    ~v1_funct_2(sK10(sK8,sK7,sK6),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(sK10(sK8,sK7,sK6)) | ~l1_pre_topc(sK9(sK8,sK7,sK6)) | ~v2_pre_topc(sK9(sK8,sK7,sK6)) | v2_struct_0(sK9(sK8,sK7,sK6)) | v2_struct_0(sK6) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | ~m1_subset_1(sK10(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))),
% 2.34/0.66    inference(subsumption_resolution,[],[f309,f69])).
% 2.34/0.66  fof(f309,plain,(
% 2.34/0.66    ~v1_funct_2(sK10(sK8,sK7,sK6),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(sK10(sK8,sK7,sK6)) | ~l1_pre_topc(sK9(sK8,sK7,sK6)) | ~v2_pre_topc(sK9(sK8,sK7,sK6)) | v2_struct_0(sK9(sK8,sK7,sK6)) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | ~m1_subset_1(sK10(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))),
% 2.34/0.66    inference(subsumption_resolution,[],[f308,f70])).
% 2.34/0.66  fof(f308,plain,(
% 2.34/0.66    ~v1_funct_2(sK10(sK8,sK7,sK6),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(sK10(sK8,sK7,sK6)) | ~l1_pre_topc(sK9(sK8,sK7,sK6)) | ~v2_pre_topc(sK9(sK8,sK7,sK6)) | v2_struct_0(sK9(sK8,sK7,sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | ~m1_subset_1(sK10(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))),
% 2.34/0.66    inference(subsumption_resolution,[],[f307,f71])).
% 2.34/0.66  fof(f307,plain,(
% 2.34/0.66    ~v1_funct_2(sK10(sK8,sK7,sK6),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(sK10(sK8,sK7,sK6)) | v2_struct_0(sK7) | ~l1_pre_topc(sK9(sK8,sK7,sK6)) | ~v2_pre_topc(sK9(sK8,sK7,sK6)) | v2_struct_0(sK9(sK8,sK7,sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | ~m1_subset_1(sK10(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))),
% 2.34/0.66    inference(subsumption_resolution,[],[f306,f72])).
% 2.34/0.66  fof(f306,plain,(
% 2.34/0.66    ~v1_funct_2(sK10(sK8,sK7,sK6),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(sK10(sK8,sK7,sK6)) | ~m1_pre_topc(sK7,sK6) | v2_struct_0(sK7) | ~l1_pre_topc(sK9(sK8,sK7,sK6)) | ~v2_pre_topc(sK9(sK8,sK7,sK6)) | v2_struct_0(sK9(sK8,sK7,sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | ~m1_subset_1(sK10(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))),
% 2.34/0.66    inference(subsumption_resolution,[],[f305,f73])).
% 2.34/0.66  fof(f305,plain,(
% 2.34/0.66    ~v1_funct_2(sK10(sK8,sK7,sK6),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(sK10(sK8,sK7,sK6)) | v2_struct_0(sK8) | ~m1_pre_topc(sK7,sK6) | v2_struct_0(sK7) | ~l1_pre_topc(sK9(sK8,sK7,sK6)) | ~v2_pre_topc(sK9(sK8,sK7,sK6)) | v2_struct_0(sK9(sK8,sK7,sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | ~m1_subset_1(sK10(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))),
% 2.34/0.66    inference(subsumption_resolution,[],[f304,f74])).
% 2.34/0.66  fof(f304,plain,(
% 2.34/0.66    ~v1_funct_2(sK10(sK8,sK7,sK6),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(sK10(sK8,sK7,sK6)) | ~m1_pre_topc(sK8,sK6) | v2_struct_0(sK8) | ~m1_pre_topc(sK7,sK6) | v2_struct_0(sK7) | ~l1_pre_topc(sK9(sK8,sK7,sK6)) | ~v2_pre_topc(sK9(sK8,sK7,sK6)) | v2_struct_0(sK9(sK8,sK7,sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | ~m1_subset_1(sK10(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | sP1(sK8,sK7,sK6) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))),
% 2.34/0.66    inference(resolution,[],[f273,f247])).
% 2.34/0.66  fof(f247,plain,(
% 2.34/0.66    ( ! [X0,X1] : (v1_funct_1(k10_tmap_1(sK6,sK9(sK8,sK7,X1),sK7,sK8,X0,k3_tmap_1(X1,sK9(sK8,sK7,X1),k1_tsep_1(X1,sK7,sK8),sK8,sK10(sK8,sK7,X1)))) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,X1))))) | ~v1_funct_2(X0,u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,X1))) | ~v1_funct_2(k3_tmap_1(X1,sK9(sK8,sK7,X1),k1_tsep_1(X1,sK7,sK8),sK8,sK10(sK8,sK7,X1)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,X1))) | sP1(sK8,sK7,X1) | ~v1_funct_1(k3_tmap_1(X1,sK9(sK8,sK7,X1),k1_tsep_1(X1,sK7,sK8),sK8,sK10(sK8,sK7,X1)))) )),
% 2.34/0.66    inference(subsumption_resolution,[],[f246,f134])).
% 2.34/0.66  fof(f246,plain,(
% 2.34/0.66    ( ! [X0,X1] : (~v1_funct_2(X0,u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,X1))) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,X1))))) | v1_funct_1(k10_tmap_1(sK6,sK9(sK8,sK7,X1),sK7,sK8,X0,k3_tmap_1(X1,sK9(sK8,sK7,X1),k1_tsep_1(X1,sK7,sK8),sK8,sK10(sK8,sK7,X1)))) | ~v1_funct_2(k3_tmap_1(X1,sK9(sK8,sK7,X1),k1_tsep_1(X1,sK7,sK8),sK8,sK10(sK8,sK7,X1)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,X1))) | sP1(sK8,sK7,X1) | ~v1_funct_1(k3_tmap_1(X1,sK9(sK8,sK7,X1),k1_tsep_1(X1,sK7,sK8),sK8,sK10(sK8,sK7,X1))) | ~r1_tsep_1(sK7,sK8)) )),
% 2.34/0.66    inference(duplicate_literal_removal,[],[f245])).
% 2.34/0.66  fof(f245,plain,(
% 2.34/0.66    ( ! [X0,X1] : (~v1_funct_2(X0,u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,X1))) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,X1))))) | v1_funct_1(k10_tmap_1(sK6,sK9(sK8,sK7,X1),sK7,sK8,X0,k3_tmap_1(X1,sK9(sK8,sK7,X1),k1_tsep_1(X1,sK7,sK8),sK8,sK10(sK8,sK7,X1)))) | ~v1_funct_2(k3_tmap_1(X1,sK9(sK8,sK7,X1),k1_tsep_1(X1,sK7,sK8),sK8,sK10(sK8,sK7,X1)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,X1))) | sP1(sK8,sK7,X1) | ~v1_funct_1(k3_tmap_1(X1,sK9(sK8,sK7,X1),k1_tsep_1(X1,sK7,sK8),sK8,sK10(sK8,sK7,X1))) | sP1(sK8,sK7,X1) | ~r1_tsep_1(sK7,sK8)) )),
% 2.34/0.66    inference(resolution,[],[f244,f102])).
% 2.34/0.66  fof(f244,plain,(
% 2.34/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,X1))))) | ~v1_funct_2(X0,u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,X1))) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,X1))))) | v1_funct_1(k10_tmap_1(sK6,sK9(sK8,sK7,X1),sK7,sK8,X0,X2)) | ~v1_funct_2(X2,u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,X1))) | sP1(sK8,sK7,X1) | ~v1_funct_1(X2)) )),
% 2.34/0.66    inference(resolution,[],[f209,f134])).
% 2.34/0.66  fof(f209,plain,(
% 2.34/0.66    ( ! [X10,X8,X7,X11,X9] : (~r1_tsep_1(X10,X9) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(X9,X10,X11))))) | ~v1_funct_2(X8,u1_struct_0(sK7),u1_struct_0(sK9(X9,X10,X11))) | ~v1_funct_1(X8) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(X9,X10,X11))))) | v1_funct_1(k10_tmap_1(sK6,sK9(X9,X10,X11),sK7,sK8,X8,X7)) | ~v1_funct_2(X7,u1_struct_0(sK8),u1_struct_0(sK9(X9,X10,X11))) | sP1(X9,X10,X11) | ~v1_funct_1(X7)) )),
% 2.34/0.66    inference(subsumption_resolution,[],[f208,f89])).
% 2.34/0.66  fof(f208,plain,(
% 2.34/0.66    ( ! [X10,X8,X7,X11,X9] : (~v1_funct_1(X7) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(X9,X10,X11))))) | ~v1_funct_2(X8,u1_struct_0(sK7),u1_struct_0(sK9(X9,X10,X11))) | ~v1_funct_1(X8) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(X9,X10,X11))))) | v1_funct_1(k10_tmap_1(sK6,sK9(X9,X10,X11),sK7,sK8,X8,X7)) | ~v1_funct_2(X7,u1_struct_0(sK8),u1_struct_0(sK9(X9,X10,X11))) | v2_struct_0(sK9(X9,X10,X11)) | sP1(X9,X10,X11) | ~r1_tsep_1(X10,X9)) )),
% 2.34/0.66    inference(subsumption_resolution,[],[f203,f90])).
% 2.34/0.66  fof(f203,plain,(
% 2.34/0.66    ( ! [X10,X8,X7,X11,X9] : (~v1_funct_1(X7) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(X9,X10,X11))))) | ~v1_funct_2(X8,u1_struct_0(sK7),u1_struct_0(sK9(X9,X10,X11))) | ~v1_funct_1(X8) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(X9,X10,X11))))) | v1_funct_1(k10_tmap_1(sK6,sK9(X9,X10,X11),sK7,sK8,X8,X7)) | ~v1_funct_2(X7,u1_struct_0(sK8),u1_struct_0(sK9(X9,X10,X11))) | ~v2_pre_topc(sK9(X9,X10,X11)) | v2_struct_0(sK9(X9,X10,X11)) | sP1(X9,X10,X11) | ~r1_tsep_1(X10,X9)) )),
% 2.34/0.66    inference(resolution,[],[f191,f91])).
% 2.34/0.66  fof(f191,plain,(
% 2.34/0.66    ( ! [X4,X5,X3] : (~l1_pre_topc(X4) | ~v1_funct_1(X3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X4)))) | ~v1_funct_2(X5,u1_struct_0(sK7),u1_struct_0(X4)) | ~v1_funct_1(X5) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(X4)))) | v1_funct_1(k10_tmap_1(sK6,X4,sK7,sK8,X5,X3)) | ~v1_funct_2(X3,u1_struct_0(sK8),u1_struct_0(X4)) | ~v2_pre_topc(X4) | v2_struct_0(X4)) )),
% 2.34/0.66    inference(subsumption_resolution,[],[f189,f73])).
% 2.34/0.66  fof(f189,plain,(
% 2.34/0.66    ( ! [X4,X5,X3] : (~v1_funct_2(X3,u1_struct_0(sK8),u1_struct_0(X4)) | ~v1_funct_1(X3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X4)))) | ~v1_funct_2(X5,u1_struct_0(sK7),u1_struct_0(X4)) | ~v1_funct_1(X5) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(X4)))) | v2_struct_0(sK8) | v1_funct_1(k10_tmap_1(sK6,X4,sK7,sK8,X5,X3)) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) )),
% 2.34/0.66    inference(resolution,[],[f183,f74])).
% 2.34/0.66  fof(f183,plain,(
% 2.34/0.66    ( ! [X2,X0,X3,X1] : (~m1_pre_topc(X1,sK6) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(sK7),u1_struct_0(X2)) | ~v1_funct_1(X3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | v2_struct_0(X1) | v1_funct_1(k10_tmap_1(sK6,X2,sK7,X1,X3,X0)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 2.34/0.66    inference(subsumption_resolution,[],[f182,f68])).
% 2.34/0.66  fof(f182,plain,(
% 2.34/0.66    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(sK7),u1_struct_0(X2)) | ~v1_funct_1(X3) | ~m1_pre_topc(X1,sK6) | v2_struct_0(X1) | v1_funct_1(k10_tmap_1(sK6,X2,sK7,X1,X3,X0)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | v2_struct_0(sK6)) )),
% 2.34/0.66    inference(subsumption_resolution,[],[f181,f69])).
% 2.34/0.66  fof(f181,plain,(
% 2.34/0.66    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(sK7),u1_struct_0(X2)) | ~v1_funct_1(X3) | ~m1_pre_topc(X1,sK6) | v2_struct_0(X1) | v1_funct_1(k10_tmap_1(sK6,X2,sK7,X1,X3,X0)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)) )),
% 2.34/0.66    inference(subsumption_resolution,[],[f180,f70])).
% 2.34/0.66  fof(f180,plain,(
% 2.34/0.66    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(sK7),u1_struct_0(X2)) | ~v1_funct_1(X3) | ~m1_pre_topc(X1,sK6) | v2_struct_0(X1) | v1_funct_1(k10_tmap_1(sK6,X2,sK7,X1,X3,X0)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)) )),
% 2.34/0.66    inference(subsumption_resolution,[],[f178,f71])).
% 2.34/0.66  fof(f178,plain,(
% 2.34/0.66    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(sK7),u1_struct_0(X2)) | ~v1_funct_1(X3) | ~m1_pre_topc(X1,sK6) | v2_struct_0(X1) | v1_funct_1(k10_tmap_1(sK6,X2,sK7,X1,X3,X0)) | v2_struct_0(sK7) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)) )),
% 2.34/0.66    inference(resolution,[],[f110,f72])).
% 2.34/0.66  fof(f110,plain,(
% 2.34/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_pre_topc(X2,X0) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.34/0.66    inference(cnf_transformation,[],[f22])).
% 2.34/0.66  fof(f22,plain,(
% 2.34/0.66    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.34/0.66    inference(flattening,[],[f21])).
% 2.34/0.66  fof(f21,plain,(
% 2.34/0.66    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.34/0.66    inference(ennf_transformation,[],[f2])).
% 2.34/0.66  fof(f2,axiom,(
% 2.34/0.66    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 2.34/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_tmap_1)).
% 2.34/0.66  fof(f273,plain,(
% 2.34/0.66    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(k10_tmap_1(X1,X4,X2,X3,k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X2,X0),k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X3,X0))) | ~v1_funct_2(X0,u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4)) | ~v1_funct_1(X0) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | k10_tmap_1(X1,X4,X2,X3,k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X2,X0),k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X3,X0)) = X0 | ~m1_subset_1(k10_tmap_1(X1,X4,X2,X3,k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X2,X0),k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X3,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4)))) | ~v1_funct_2(k10_tmap_1(X1,X4,X2,X3,k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X2,X0),k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X3,X0)),u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4))))) )),
% 2.34/0.66    inference(duplicate_literal_removal,[],[f272])).
% 2.34/0.66  fof(f272,plain,(
% 2.34/0.66    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4)))) | ~v1_funct_2(X0,u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4)) | ~v1_funct_1(X0) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | k10_tmap_1(X1,X4,X2,X3,k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X2,X0),k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X3,X0)) = X0 | ~m1_subset_1(k10_tmap_1(X1,X4,X2,X3,k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X2,X0),k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X3,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4)))) | ~v1_funct_2(k10_tmap_1(X1,X4,X2,X3,k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X2,X0),k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X3,X0)),u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4)) | ~v1_funct_1(k10_tmap_1(X1,X4,X2,X3,k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X2,X0),k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X3,X0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4)))) | ~v1_funct_2(X0,u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4)) | ~v1_funct_1(X0)) )),
% 2.34/0.66    inference(resolution,[],[f81,f108])).
% 2.34/0.66  fof(f108,plain,(
% 2.34/0.66    ( ! [X2,X0,X3,X1] : (~r2_funct_2(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.34/0.66    inference(cnf_transformation,[],[f50])).
% 2.34/0.66  fof(f50,plain,(
% 2.34/0.66    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.34/0.66    inference(nnf_transformation,[],[f20])).
% 2.34/0.66  fof(f20,plain,(
% 2.34/0.66    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.34/0.66    inference(flattening,[],[f19])).
% 2.34/0.66  fof(f19,plain,(
% 2.34/0.66    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.34/0.66    inference(ennf_transformation,[],[f1])).
% 2.34/0.66  fof(f1,axiom,(
% 2.34/0.66    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 2.34/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 2.34/0.66  fof(f81,plain,(
% 2.34/0.66    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.34/0.66    inference(cnf_transformation,[],[f14])).
% 2.34/0.66  fof(f14,plain,(
% 2.34/0.66    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.34/0.66    inference(flattening,[],[f13])).
% 2.34/0.66  fof(f13,plain,(
% 2.34/0.66    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.34/0.66    inference(ennf_transformation,[],[f4])).
% 2.34/0.66  fof(f4,axiom,(
% 2.34/0.66    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) => r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))))))))),
% 2.34/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_tmap_1)).
% 2.34/0.66  fof(f515,plain,(
% 2.34/0.66    sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~r3_tsep_1(sK6,sK7,sK8)),
% 2.34/0.66    inference(resolution,[],[f514,f76])).
% 2.34/0.66  fof(f514,plain,(
% 2.34/0.66    sP0(sK8,sK7,sK6) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))),
% 2.34/0.66    inference(subsumption_resolution,[],[f513,f134])).
% 2.34/0.66  fof(f513,plain,(
% 2.34/0.66    sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(duplicate_literal_removal,[],[f512])).
% 2.34/0.66  fof(f512,plain,(
% 2.34/0.66    sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | sP0(sK8,sK7,sK6) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(resolution,[],[f511,f59])).
% 2.34/0.66  fof(f59,plain,(
% 2.34/0.66    ( ! [X2,X0,X1] : (v1_funct_1(sK4(X0,X1,X2)) | sP0(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 2.34/0.66    inference(cnf_transformation,[],[f34])).
% 2.34/0.66  fof(f511,plain,(
% 2.34/0.66    ~v1_funct_1(sK4(sK8,sK7,sK6)) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | sP0(sK8,sK7,sK6)),
% 2.34/0.66    inference(subsumption_resolution,[],[f510,f134])).
% 2.34/0.66  fof(f510,plain,(
% 2.34/0.66    sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(duplicate_literal_removal,[],[f509])).
% 2.34/0.66  fof(f509,plain,(
% 2.34/0.66    sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(resolution,[],[f508,f63])).
% 2.34/0.66  fof(f63,plain,(
% 2.34/0.66    ( ! [X2,X0,X1] : (v1_funct_1(sK5(X0,X1,X2)) | sP0(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 2.34/0.66    inference(cnf_transformation,[],[f34])).
% 2.34/0.66  fof(f508,plain,(
% 2.34/0.66    ~v1_funct_1(sK5(sK8,sK7,sK6)) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6)),
% 2.34/0.66    inference(subsumption_resolution,[],[f507,f134])).
% 2.34/0.66  fof(f507,plain,(
% 2.34/0.66    ~v1_funct_1(sK4(sK8,sK7,sK6)) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(duplicate_literal_removal,[],[f506])).
% 2.34/0.66  fof(f506,plain,(
% 2.34/0.66    ~v1_funct_1(sK4(sK8,sK7,sK6)) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(resolution,[],[f505,f56])).
% 2.34/0.66  fof(f56,plain,(
% 2.34/0.66    ( ! [X2,X0,X1] : (~v2_struct_0(sK3(X0,X1,X2)) | sP0(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 2.34/0.66    inference(cnf_transformation,[],[f34])).
% 2.34/0.66  fof(f505,plain,(
% 2.34/0.66    v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6)),
% 2.34/0.66    inference(subsumption_resolution,[],[f504,f134])).
% 2.34/0.66  fof(f504,plain,(
% 2.34/0.66    ~v1_funct_1(sK4(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(duplicate_literal_removal,[],[f503])).
% 2.34/0.66  fof(f503,plain,(
% 2.34/0.66    ~v1_funct_1(sK4(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(resolution,[],[f502,f60])).
% 2.34/0.66  fof(f60,plain,(
% 2.34/0.66    ( ! [X2,X0,X1] : (v1_funct_2(sK4(X0,X1,X2),u1_struct_0(X1),u1_struct_0(sK3(X0,X1,X2))) | sP0(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 2.34/0.66    inference(cnf_transformation,[],[f34])).
% 2.34/0.66  fof(f502,plain,(
% 2.34/0.66    ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6)),
% 2.34/0.66    inference(subsumption_resolution,[],[f501,f134])).
% 2.34/0.66  fof(f501,plain,(
% 2.34/0.66    v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(duplicate_literal_removal,[],[f500])).
% 2.34/0.66  fof(f500,plain,(
% 2.34/0.66    v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(resolution,[],[f499,f64])).
% 2.34/0.66  fof(f64,plain,(
% 2.34/0.66    ( ! [X2,X0,X1] : (v1_funct_2(sK5(X0,X1,X2),u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2))) | sP0(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 2.34/0.66    inference(cnf_transformation,[],[f34])).
% 2.34/0.66  fof(f499,plain,(
% 2.34/0.66    ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6)),
% 2.34/0.66    inference(subsumption_resolution,[],[f498,f134])).
% 2.34/0.66  fof(f498,plain,(
% 2.34/0.66    v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(duplicate_literal_removal,[],[f497])).
% 2.34/0.66  fof(f497,plain,(
% 2.34/0.66    v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(resolution,[],[f496,f62])).
% 2.34/0.66  fof(f62,plain,(
% 2.34/0.66    ( ! [X2,X0,X1] : (m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3(X0,X1,X2))))) | sP0(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 2.34/0.66    inference(cnf_transformation,[],[f34])).
% 2.34/0.66  fof(f496,plain,(
% 2.34/0.66    ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6)),
% 2.34/0.66    inference(subsumption_resolution,[],[f495,f134])).
% 2.34/0.66  fof(f495,plain,(
% 2.34/0.66    ~v1_funct_1(sK4(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(duplicate_literal_removal,[],[f494])).
% 2.34/0.66  fof(f494,plain,(
% 2.34/0.66    ~v1_funct_1(sK4(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(resolution,[],[f493,f66])).
% 2.34/0.66  fof(f66,plain,(
% 2.34/0.66    ( ! [X2,X0,X1] : (m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2))))) | sP0(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 2.34/0.66    inference(cnf_transformation,[],[f34])).
% 2.34/0.66  fof(f493,plain,(
% 2.34/0.66    ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6)),
% 2.34/0.66    inference(subsumption_resolution,[],[f492,f134])).
% 2.34/0.66  fof(f492,plain,(
% 2.34/0.66    ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(resolution,[],[f491,f57])).
% 2.34/0.66  fof(f57,plain,(
% 2.34/0.66    ( ! [X2,X0,X1] : (v2_pre_topc(sK3(X0,X1,X2)) | sP0(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 2.34/0.66    inference(cnf_transformation,[],[f34])).
% 2.34/0.66  fof(f491,plain,(
% 2.34/0.66    ~v2_pre_topc(sK3(sK8,sK7,sK6)) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))),
% 2.34/0.66    inference(global_subsumption,[],[f76,f402,f490])).
% 2.34/0.66  fof(f490,plain,(
% 2.34/0.66    v2_struct_0(sK3(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v2_pre_topc(sK3(sK8,sK7,sK6))),
% 2.34/0.66    inference(subsumption_resolution,[],[f489,f134])).
% 2.34/0.66  fof(f489,plain,(
% 2.34/0.66    v2_struct_0(sK3(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(duplicate_literal_removal,[],[f488])).
% 2.34/0.66  fof(f488,plain,(
% 2.34/0.66    v2_struct_0(sK3(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.66    inference(resolution,[],[f487,f58])).
% 2.34/0.66  fof(f58,plain,(
% 2.34/0.66    ( ! [X2,X0,X1] : (l1_pre_topc(sK3(X0,X1,X2)) | sP0(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 2.34/0.66    inference(cnf_transformation,[],[f34])).
% 2.34/0.66  fof(f487,plain,(
% 2.34/0.66    ~l1_pre_topc(sK3(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v2_pre_topc(sK3(sK8,sK7,sK6))),
% 2.34/0.66    inference(subsumption_resolution,[],[f486,f68])).
% 2.34/0.66  fof(f486,plain,(
% 2.34/0.66    sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | v2_struct_0(sK6)),
% 2.34/0.66    inference(subsumption_resolution,[],[f485,f69])).
% 2.34/0.66  fof(f485,plain,(
% 2.34/0.66    sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)),
% 2.34/0.66    inference(subsumption_resolution,[],[f484,f70])).
% 2.34/0.66  fof(f484,plain,(
% 2.34/0.66    sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)),
% 2.34/0.66    inference(subsumption_resolution,[],[f483,f71])).
% 2.34/0.66  fof(f483,plain,(
% 2.34/0.66    sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | v2_struct_0(sK7) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)),
% 2.34/0.66    inference(subsumption_resolution,[],[f482,f72])).
% 2.34/0.66  fof(f482,plain,(
% 2.34/0.66    sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~m1_pre_topc(sK7,sK6) | v2_struct_0(sK7) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)),
% 2.34/0.66    inference(subsumption_resolution,[],[f481,f73])).
% 2.34/0.66  fof(f481,plain,(
% 2.34/0.66    sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | v2_struct_0(sK8) | ~m1_pre_topc(sK7,sK6) | v2_struct_0(sK7) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)),
% 2.34/0.66    inference(subsumption_resolution,[],[f480,f74])).
% 2.34/0.66  fof(f480,plain,(
% 2.34/0.66    sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~m1_pre_topc(sK8,sK6) | v2_struct_0(sK8) | ~m1_pre_topc(sK7,sK6) | v2_struct_0(sK7) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)),
% 2.34/0.66    inference(duplicate_literal_removal,[],[f477])).
% 2.34/0.67  fof(f477,plain,(
% 2.34/0.67    sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~m1_pre_topc(sK8,sK6) | v2_struct_0(sK8) | ~m1_pre_topc(sK7,sK6) | v2_struct_0(sK7) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)),
% 2.34/0.67    inference(resolution,[],[f476,f111])).
% 2.34/0.67  fof(f111,plain,(
% 2.34/0.67    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.34/0.67    inference(cnf_transformation,[],[f22])).
% 2.34/0.67  fof(f476,plain,(
% 2.34/0.67    ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f475,f134])).
% 2.34/0.67  fof(f475,plain,(
% 2.34/0.67    sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(duplicate_literal_removal,[],[f474])).
% 2.34/0.67  fof(f474,plain,(
% 2.34/0.67    sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(resolution,[],[f473,f59])).
% 2.34/0.67  fof(f473,plain,(
% 2.34/0.67    ~v1_funct_1(sK4(sK8,sK7,sK6)) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f472,f134])).
% 2.34/0.67  fof(f472,plain,(
% 2.34/0.67    v2_struct_0(sK3(sK8,sK7,sK6)) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(duplicate_literal_removal,[],[f471])).
% 2.34/0.67  fof(f471,plain,(
% 2.34/0.67    v2_struct_0(sK3(sK8,sK7,sK6)) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(resolution,[],[f470,f63])).
% 2.34/0.67  fof(f470,plain,(
% 2.34/0.67    ~v1_funct_1(sK5(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f469,f134])).
% 2.34/0.67  fof(f469,plain,(
% 2.34/0.67    ~v1_funct_1(sK5(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(duplicate_literal_removal,[],[f468])).
% 2.34/0.67  fof(f468,plain,(
% 2.34/0.67    ~v1_funct_1(sK5(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(resolution,[],[f467,f60])).
% 2.34/0.67  fof(f467,plain,(
% 2.34/0.67    ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f466,f134])).
% 2.34/0.67  fof(f466,plain,(
% 2.34/0.67    v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(duplicate_literal_removal,[],[f465])).
% 2.34/0.67  fof(f465,plain,(
% 2.34/0.67    v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(resolution,[],[f464,f64])).
% 2.34/0.67  fof(f464,plain,(
% 2.34/0.67    ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f463,f134])).
% 2.34/0.67  fof(f463,plain,(
% 2.34/0.67    ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(duplicate_literal_removal,[],[f462])).
% 2.34/0.67  fof(f462,plain,(
% 2.34/0.67    ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(resolution,[],[f461,f62])).
% 2.34/0.67  fof(f461,plain,(
% 2.34/0.67    ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f460,f134])).
% 2.34/0.67  fof(f460,plain,(
% 2.34/0.67    ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(duplicate_literal_removal,[],[f459])).
% 2.34/0.67  fof(f459,plain,(
% 2.34/0.67    ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(resolution,[],[f458,f66])).
% 2.34/0.67  fof(f458,plain,(
% 2.34/0.67    ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f457,f134])).
% 2.34/0.67  fof(f457,plain,(
% 2.34/0.67    ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(resolution,[],[f456,f57])).
% 2.34/0.67  fof(f456,plain,(
% 2.34/0.67    ~v2_pre_topc(sK3(sK8,sK7,sK6)) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))),
% 2.34/0.67    inference(global_subsumption,[],[f76,f402,f455])).
% 2.34/0.67  fof(f455,plain,(
% 2.34/0.67    v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | sP0(sK8,sK7,sK6) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v2_pre_topc(sK3(sK8,sK7,sK6))),
% 2.34/0.67    inference(subsumption_resolution,[],[f454,f134])).
% 2.34/0.67  fof(f454,plain,(
% 2.34/0.67    v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | sP0(sK8,sK7,sK6) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(duplicate_literal_removal,[],[f453])).
% 2.34/0.67  fof(f453,plain,(
% 2.34/0.67    v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | sP0(sK8,sK7,sK6) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(resolution,[],[f452,f58])).
% 2.34/0.67  fof(f452,plain,(
% 2.34/0.67    ~l1_pre_topc(sK3(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | sP0(sK8,sK7,sK6) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v2_pre_topc(sK3(sK8,sK7,sK6))),
% 2.34/0.67    inference(subsumption_resolution,[],[f451,f68])).
% 2.34/0.67  fof(f451,plain,(
% 2.34/0.67    sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | sP0(sK8,sK7,sK6) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | v2_struct_0(sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f450,f69])).
% 2.34/0.67  fof(f450,plain,(
% 2.34/0.67    sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | sP0(sK8,sK7,sK6) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f449,f70])).
% 2.34/0.67  fof(f449,plain,(
% 2.34/0.67    sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | sP0(sK8,sK7,sK6) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f448,f71])).
% 2.34/0.67  fof(f448,plain,(
% 2.34/0.67    sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | sP0(sK8,sK7,sK6) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | v2_struct_0(sK7) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f447,f72])).
% 2.34/0.67  fof(f447,plain,(
% 2.34/0.67    sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | sP0(sK8,sK7,sK6) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~m1_pre_topc(sK7,sK6) | v2_struct_0(sK7) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f446,f73])).
% 2.34/0.67  fof(f446,plain,(
% 2.34/0.67    sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | sP0(sK8,sK7,sK6) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | v2_struct_0(sK8) | ~m1_pre_topc(sK7,sK6) | v2_struct_0(sK7) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f445,f74])).
% 2.34/0.67  fof(f445,plain,(
% 2.34/0.67    sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | sP0(sK8,sK7,sK6) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~m1_pre_topc(sK8,sK6) | v2_struct_0(sK8) | ~m1_pre_topc(sK7,sK6) | v2_struct_0(sK7) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)),
% 2.34/0.67    inference(duplicate_literal_removal,[],[f442])).
% 2.34/0.67  fof(f442,plain,(
% 2.34/0.67    sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | sP0(sK8,sK7,sK6) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~m1_pre_topc(sK8,sK6) | v2_struct_0(sK8) | ~m1_pre_topc(sK7,sK6) | v2_struct_0(sK7) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)),
% 2.34/0.67    inference(resolution,[],[f441,f112])).
% 2.34/0.67  fof(f112,plain,(
% 2.34/0.67    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.34/0.67    inference(cnf_transformation,[],[f22])).
% 2.34/0.67  fof(f441,plain,(
% 2.34/0.67    ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | sP0(sK8,sK7,sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f440,f134])).
% 2.34/0.67  fof(f440,plain,(
% 2.34/0.67    ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(duplicate_literal_removal,[],[f439])).
% 2.34/0.67  fof(f439,plain,(
% 2.34/0.67    ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(resolution,[],[f438,f59])).
% 2.34/0.67  fof(f438,plain,(
% 2.34/0.67    ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f437,f134])).
% 2.34/0.67  fof(f437,plain,(
% 2.34/0.67    ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(duplicate_literal_removal,[],[f436])).
% 2.34/0.67  fof(f436,plain,(
% 2.34/0.67    ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(resolution,[],[f435,f63])).
% 2.34/0.67  fof(f435,plain,(
% 2.34/0.67    ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f434,f134])).
% 2.34/0.67  fof(f434,plain,(
% 2.34/0.67    ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(duplicate_literal_removal,[],[f433])).
% 2.34/0.67  fof(f433,plain,(
% 2.34/0.67    ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(resolution,[],[f432,f60])).
% 2.34/0.67  fof(f432,plain,(
% 2.34/0.67    ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f431,f134])).
% 2.34/0.67  fof(f431,plain,(
% 2.34/0.67    ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(duplicate_literal_removal,[],[f430])).
% 2.34/0.67  fof(f430,plain,(
% 2.34/0.67    ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(resolution,[],[f429,f64])).
% 2.34/0.67  fof(f429,plain,(
% 2.34/0.67    ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f428,f134])).
% 2.34/0.67  fof(f428,plain,(
% 2.34/0.67    ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(duplicate_literal_removal,[],[f427])).
% 2.34/0.67  fof(f427,plain,(
% 2.34/0.67    ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(resolution,[],[f426,f62])).
% 2.34/0.67  fof(f426,plain,(
% 2.34/0.67    ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f425,f134])).
% 2.34/0.67  fof(f425,plain,(
% 2.34/0.67    ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(duplicate_literal_removal,[],[f424])).
% 2.34/0.67  fof(f424,plain,(
% 2.34/0.67    ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(resolution,[],[f423,f66])).
% 2.34/0.67  fof(f423,plain,(
% 2.34/0.67    ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f422,f134])).
% 2.34/0.67  fof(f422,plain,(
% 2.34/0.67    ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(duplicate_literal_removal,[],[f421])).
% 2.34/0.67  fof(f421,plain,(
% 2.34/0.67    ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(resolution,[],[f420,f57])).
% 2.34/0.67  fof(f420,plain,(
% 2.34/0.67    ~v2_pre_topc(sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f419,f134])).
% 2.34/0.67  fof(f419,plain,(
% 2.34/0.67    sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(duplicate_literal_removal,[],[f418])).
% 2.34/0.67  fof(f418,plain,(
% 2.34/0.67    sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(resolution,[],[f417,f58])).
% 2.34/0.67  fof(f417,plain,(
% 2.34/0.67    ~l1_pre_topc(sK3(sK8,sK7,sK6)) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f416,f134])).
% 2.34/0.67  fof(f416,plain,(
% 2.34/0.67    ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(duplicate_literal_removal,[],[f415])).
% 2.34/0.67  fof(f415,plain,(
% 2.34/0.67    ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(resolution,[],[f414,f61])).
% 2.34/0.67  fof(f61,plain,(
% 2.34/0.67    ( ! [X2,X0,X1] : (v5_pre_topc(sK4(X0,X1,X2),X1,sK3(X0,X1,X2)) | sP0(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 2.34/0.67    inference(cnf_transformation,[],[f34])).
% 2.34/0.67  fof(f414,plain,(
% 2.34/0.67    ~v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6)) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f413,f134])).
% 2.34/0.67  fof(f413,plain,(
% 2.34/0.67    ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(resolution,[],[f404,f65])).
% 2.34/0.67  fof(f65,plain,(
% 2.34/0.67    ( ! [X2,X0,X1] : (v5_pre_topc(sK5(X0,X1,X2),X0,sK3(X0,X1,X2)) | sP0(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 2.34/0.67    inference(cnf_transformation,[],[f34])).
% 2.34/0.67  fof(f404,plain,(
% 2.34/0.67    ~v5_pre_topc(sK5(sK8,sK7,sK6),sK8,sK3(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))),
% 2.34/0.67    inference(resolution,[],[f402,f320])).
% 2.34/0.67  fof(f320,plain,(
% 2.34/0.67    ~r3_tsep_1(sK6,sK7,sK8) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v5_pre_topc(sK5(sK8,sK7,sK6),sK8,sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))),
% 2.34/0.67    inference(subsumption_resolution,[],[f319,f76])).
% 2.34/0.67  fof(f319,plain,(
% 2.34/0.67    ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v5_pre_topc(sK5(sK8,sK7,sK6),sK8,sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~r3_tsep_1(sK6,sK7,sK8)),
% 2.34/0.67    inference(subsumption_resolution,[],[f318,f68])).
% 2.34/0.67  fof(f318,plain,(
% 2.34/0.67    ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v5_pre_topc(sK5(sK8,sK7,sK6),sK8,sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~r3_tsep_1(sK6,sK7,sK8) | v2_struct_0(sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f317,f69])).
% 2.34/0.67  fof(f317,plain,(
% 2.34/0.67    ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v5_pre_topc(sK5(sK8,sK7,sK6),sK8,sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~r3_tsep_1(sK6,sK7,sK8) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f316,f70])).
% 2.34/0.67  fof(f316,plain,(
% 2.34/0.67    ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v5_pre_topc(sK5(sK8,sK7,sK6),sK8,sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~r3_tsep_1(sK6,sK7,sK8) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f315,f71])).
% 2.34/0.67  fof(f315,plain,(
% 2.34/0.67    ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v5_pre_topc(sK5(sK8,sK7,sK6),sK8,sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~r3_tsep_1(sK6,sK7,sK8) | v2_struct_0(sK7) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f314,f72])).
% 2.34/0.67  fof(f314,plain,(
% 2.34/0.67    ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v5_pre_topc(sK5(sK8,sK7,sK6),sK8,sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~r3_tsep_1(sK6,sK7,sK8) | ~m1_pre_topc(sK7,sK6) | v2_struct_0(sK7) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f313,f73])).
% 2.34/0.67  fof(f313,plain,(
% 2.34/0.67    ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v5_pre_topc(sK5(sK8,sK7,sK6),sK8,sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~r3_tsep_1(sK6,sK7,sK8) | v2_struct_0(sK8) | ~m1_pre_topc(sK7,sK6) | v2_struct_0(sK7) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f312,f74])).
% 2.34/0.67  fof(f312,plain,(
% 2.34/0.67    ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v5_pre_topc(sK5(sK8,sK7,sK6),sK8,sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~r3_tsep_1(sK6,sK7,sK8) | ~m1_pre_topc(sK8,sK6) | v2_struct_0(sK8) | ~m1_pre_topc(sK7,sK6) | v2_struct_0(sK7) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)),
% 2.34/0.67    inference(resolution,[],[f303,f107])).
% 2.34/0.67  fof(f107,plain,(
% 2.34/0.67    ( ! [X2,X0,X1] : (r4_tsep_1(X0,X1,X2) | ~r3_tsep_1(X0,X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.34/0.67    inference(cnf_transformation,[],[f49])).
% 2.34/0.67  fof(f49,plain,(
% 2.34/0.67    ! [X0] : (! [X1] : (! [X2] : ((((r4_tsep_1(X0,X1,X2) & r1_tsep_1(X1,X2)) | ~r3_tsep_1(X0,X1,X2)) & (r3_tsep_1(X0,X1,X2) | ~r4_tsep_1(X0,X1,X2) | ~r1_tsep_1(X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.34/0.67    inference(flattening,[],[f48])).
% 2.34/0.67  fof(f48,plain,(
% 2.34/0.67    ! [X0] : (! [X1] : (! [X2] : ((((r4_tsep_1(X0,X1,X2) & r1_tsep_1(X1,X2)) | ~r3_tsep_1(X0,X1,X2)) & (r3_tsep_1(X0,X1,X2) | (~r4_tsep_1(X0,X1,X2) | ~r1_tsep_1(X1,X2)))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.34/0.67    inference(nnf_transformation,[],[f18])).
% 2.34/0.67  fof(f18,plain,(
% 2.34/0.67    ! [X0] : (! [X1] : (! [X2] : (((r4_tsep_1(X0,X1,X2) & r1_tsep_1(X1,X2)) <=> r3_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.34/0.67    inference(flattening,[],[f17])).
% 2.34/0.67  fof(f17,plain,(
% 2.34/0.67    ! [X0] : (! [X1] : (! [X2] : (((r4_tsep_1(X0,X1,X2) & r1_tsep_1(X1,X2)) <=> r3_tsep_1(X0,X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.34/0.67    inference(ennf_transformation,[],[f6])).
% 2.34/0.67  fof(f6,axiom,(
% 2.34/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ((r4_tsep_1(X0,X1,X2) & r1_tsep_1(X1,X2)) <=> r3_tsep_1(X0,X1,X2)))))),
% 2.34/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_tsep_1)).
% 2.34/0.67  fof(f303,plain,(
% 2.34/0.67    ~r4_tsep_1(sK6,sK7,sK8) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v5_pre_topc(sK5(sK8,sK7,sK6),sK8,sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6))),
% 2.34/0.67    inference(subsumption_resolution,[],[f302,f68])).
% 2.34/0.67  fof(f302,plain,(
% 2.34/0.67    ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6) | ~r4_tsep_1(sK6,sK7,sK8) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v5_pre_topc(sK5(sK8,sK7,sK6),sK8,sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | v2_struct_0(sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f301,f69])).
% 2.34/0.67  fof(f301,plain,(
% 2.34/0.67    ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6) | ~r4_tsep_1(sK6,sK7,sK8) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v5_pre_topc(sK5(sK8,sK7,sK6),sK8,sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f300,f70])).
% 2.34/0.67  fof(f300,plain,(
% 2.34/0.67    ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6) | ~r4_tsep_1(sK6,sK7,sK8) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v5_pre_topc(sK5(sK8,sK7,sK6),sK8,sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f299,f71])).
% 2.34/0.67  fof(f299,plain,(
% 2.34/0.67    ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6) | ~r4_tsep_1(sK6,sK7,sK8) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v5_pre_topc(sK5(sK8,sK7,sK6),sK8,sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | v2_struct_0(sK7) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f298,f72])).
% 2.34/0.67  fof(f298,plain,(
% 2.34/0.67    ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6) | ~r4_tsep_1(sK6,sK7,sK8) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v5_pre_topc(sK5(sK8,sK7,sK6),sK8,sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~m1_pre_topc(sK7,sK6) | v2_struct_0(sK7) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f297,f73])).
% 2.34/0.67  fof(f297,plain,(
% 2.34/0.67    ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6) | ~r4_tsep_1(sK6,sK7,sK8) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v5_pre_topc(sK5(sK8,sK7,sK6),sK8,sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | v2_struct_0(sK8) | ~m1_pre_topc(sK7,sK6) | v2_struct_0(sK7) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f296,f74])).
% 2.34/0.67  fof(f296,plain,(
% 2.34/0.67    ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6) | ~r4_tsep_1(sK6,sK7,sK8) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v5_pre_topc(sK5(sK8,sK7,sK6),sK8,sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~m1_pre_topc(sK8,sK6) | v2_struct_0(sK8) | ~m1_pre_topc(sK7,sK6) | v2_struct_0(sK7) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f294,f134])).
% 2.34/0.67  fof(f294,plain,(
% 2.34/0.67    ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6) | ~r4_tsep_1(sK6,sK7,sK8) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v5_pre_topc(sK5(sK8,sK7,sK6),sK8,sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~r1_tsep_1(sK7,sK8) | ~m1_pre_topc(sK8,sK6) | v2_struct_0(sK8) | ~m1_pre_topc(sK7,sK6) | v2_struct_0(sK7) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)),
% 2.34/0.67    inference(resolution,[],[f293,f79])).
% 2.34/0.67  fof(f79,plain,(
% 2.34/0.67    ( ! [X4,X2,X0,X5,X3,X1] : (v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) | ~r4_tsep_1(X0,X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(X5,X3,X1) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(X4,X2,X1) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r1_tsep_1(X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.34/0.67    inference(cnf_transformation,[],[f12])).
% 2.34/0.67  fof(f12,plain,(
% 2.34/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~r4_tsep_1(X0,X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(X5,X3,X1) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(X4,X2,X1) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r1_tsep_1(X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.34/0.67    inference(flattening,[],[f11])).
% 2.34/0.67  fof(f11,plain,(
% 2.34/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (! [X5] : (((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~r4_tsep_1(X0,X2,X3)) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(X5,X3,X1) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(X4,X2,X1) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~r1_tsep_1(X2,X3)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.34/0.67    inference(ennf_transformation,[],[f5])).
% 2.34/0.67  fof(f5,axiom,(
% 2.34/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (r1_tsep_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => (r4_tsep_1(X0,X2,X3) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)))))))))))),
% 2.34/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_tmap_1)).
% 2.34/0.67  fof(f293,plain,(
% 2.34/0.67    ~v5_pre_topc(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_tsep_1(sK6,sK7,sK8),sK3(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f292,f134])).
% 2.34/0.67  fof(f292,plain,(
% 2.34/0.67    ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v5_pre_topc(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_tsep_1(sK6,sK7,sK8),sK3(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(duplicate_literal_removal,[],[f291])).
% 2.34/0.67  fof(f291,plain,(
% 2.34/0.67    ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v5_pre_topc(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_tsep_1(sK6,sK7,sK8),sK3(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(resolution,[],[f290,f59])).
% 2.34/0.67  fof(f290,plain,(
% 2.34/0.67    ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v5_pre_topc(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_tsep_1(sK6,sK7,sK8),sK3(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f289,f134])).
% 2.34/0.67  fof(f289,plain,(
% 2.34/0.67    ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v5_pre_topc(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_tsep_1(sK6,sK7,sK8),sK3(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(duplicate_literal_removal,[],[f288])).
% 2.34/0.67  fof(f288,plain,(
% 2.34/0.67    ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v5_pre_topc(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_tsep_1(sK6,sK7,sK8),sK3(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(resolution,[],[f287,f63])).
% 2.34/0.67  fof(f287,plain,(
% 2.34/0.67    ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v5_pre_topc(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_tsep_1(sK6,sK7,sK8),sK3(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f286,f134])).
% 2.34/0.67  fof(f286,plain,(
% 2.34/0.67    sP0(sK8,sK7,sK6) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v5_pre_topc(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_tsep_1(sK6,sK7,sK8),sK3(sK8,sK7,sK6)) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(duplicate_literal_removal,[],[f285])).
% 2.34/0.67  fof(f285,plain,(
% 2.34/0.67    sP0(sK8,sK7,sK6) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v5_pre_topc(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_tsep_1(sK6,sK7,sK8),sK3(sK8,sK7,sK6)) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(resolution,[],[f284,f60])).
% 2.34/0.67  fof(f284,plain,(
% 2.34/0.67    ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | sP0(sK8,sK7,sK6) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v5_pre_topc(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_tsep_1(sK6,sK7,sK8),sK3(sK8,sK7,sK6)) | ~v1_funct_1(sK5(sK8,sK7,sK6))),
% 2.34/0.67    inference(subsumption_resolution,[],[f283,f134])).
% 2.34/0.67  fof(f283,plain,(
% 2.34/0.67    ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | sP0(sK8,sK7,sK6) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v5_pre_topc(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_tsep_1(sK6,sK7,sK8),sK3(sK8,sK7,sK6)) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(duplicate_literal_removal,[],[f282])).
% 2.34/0.67  fof(f282,plain,(
% 2.34/0.67    ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | sP0(sK8,sK7,sK6) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v5_pre_topc(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_tsep_1(sK6,sK7,sK8),sK3(sK8,sK7,sK6)) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(resolution,[],[f281,f64])).
% 2.34/0.67  fof(f281,plain,(
% 2.34/0.67    ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | sP0(sK8,sK7,sK6) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v5_pre_topc(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_tsep_1(sK6,sK7,sK8),sK3(sK8,sK7,sK6)) | ~v1_funct_1(sK5(sK8,sK7,sK6))),
% 2.34/0.67    inference(subsumption_resolution,[],[f280,f134])).
% 2.34/0.67  fof(f280,plain,(
% 2.34/0.67    ~v5_pre_topc(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_tsep_1(sK6,sK7,sK8),sK3(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | sP0(sK8,sK7,sK6) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(duplicate_literal_removal,[],[f279])).
% 2.34/0.67  fof(f279,plain,(
% 2.34/0.67    ~v5_pre_topc(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_tsep_1(sK6,sK7,sK8),sK3(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | sP0(sK8,sK7,sK6) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(resolution,[],[f278,f62])).
% 2.34/0.67  fof(f278,plain,(
% 2.34/0.67    ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v5_pre_topc(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_tsep_1(sK6,sK7,sK8),sK3(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | sP0(sK8,sK7,sK6) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6))),
% 2.34/0.67    inference(subsumption_resolution,[],[f277,f134])).
% 2.34/0.67  fof(f277,plain,(
% 2.34/0.67    ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v5_pre_topc(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_tsep_1(sK6,sK7,sK8),sK3(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6))),
% 2.34/0.67    inference(duplicate_literal_removal,[],[f276])).
% 2.34/0.67  fof(f276,plain,(
% 2.34/0.67    ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v5_pre_topc(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_tsep_1(sK6,sK7,sK8),sK3(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | sP0(sK8,sK7,sK6) | ~v1_funct_1(sK5(sK8,sK7,sK6))),
% 2.34/0.67    inference(resolution,[],[f67,f243])).
% 2.34/0.67  fof(f243,plain,(
% 2.34/0.67    ( ! [X0,X1] : (v1_funct_1(k10_tmap_1(sK6,sK3(sK8,sK7,X1),sK7,sK8,X0,sK5(sK8,sK7,X1))) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,X1))))) | ~v1_funct_2(X0,u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,X1))) | ~v1_funct_2(sK5(sK8,sK7,X1),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,X1))) | sP0(sK8,sK7,X1) | ~v1_funct_1(sK5(sK8,sK7,X1))) )),
% 2.34/0.67    inference(subsumption_resolution,[],[f242,f134])).
% 2.34/0.67  fof(f242,plain,(
% 2.34/0.67    ( ! [X0,X1] : (~v1_funct_2(X0,u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,X1))) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,X1))))) | v1_funct_1(k10_tmap_1(sK6,sK3(sK8,sK7,X1),sK7,sK8,X0,sK5(sK8,sK7,X1))) | ~v1_funct_2(sK5(sK8,sK7,X1),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,X1))) | sP0(sK8,sK7,X1) | ~v1_funct_1(sK5(sK8,sK7,X1)) | ~r1_tsep_1(sK7,sK8)) )),
% 2.34/0.67    inference(duplicate_literal_removal,[],[f241])).
% 2.34/0.67  fof(f241,plain,(
% 2.34/0.67    ( ! [X0,X1] : (~v1_funct_2(X0,u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,X1))) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,X1))))) | v1_funct_1(k10_tmap_1(sK6,sK3(sK8,sK7,X1),sK7,sK8,X0,sK5(sK8,sK7,X1))) | ~v1_funct_2(sK5(sK8,sK7,X1),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,X1))) | sP0(sK8,sK7,X1) | ~v1_funct_1(sK5(sK8,sK7,X1)) | sP0(sK8,sK7,X1) | ~r1_tsep_1(sK7,sK8)) )),
% 2.34/0.67    inference(resolution,[],[f240,f66])).
% 2.34/0.67  fof(f240,plain,(
% 2.34/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,X1))))) | ~v1_funct_2(X0,u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,X1))) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,X1))))) | v1_funct_1(k10_tmap_1(sK6,sK3(sK8,sK7,X1),sK7,sK8,X0,X2)) | ~v1_funct_2(X2,u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,X1))) | sP0(sK8,sK7,X1) | ~v1_funct_1(X2)) )),
% 2.34/0.67    inference(resolution,[],[f207,f134])).
% 2.34/0.67  fof(f207,plain,(
% 2.34/0.67    ( ! [X6,X4,X2,X5,X3] : (~r1_tsep_1(X5,X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(X4,X5,X6))))) | ~v1_funct_2(X3,u1_struct_0(sK7),u1_struct_0(sK3(X4,X5,X6))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(X4,X5,X6))))) | v1_funct_1(k10_tmap_1(sK6,sK3(X4,X5,X6),sK7,sK8,X3,X2)) | ~v1_funct_2(X2,u1_struct_0(sK8),u1_struct_0(sK3(X4,X5,X6))) | sP0(X4,X5,X6) | ~v1_funct_1(X2)) )),
% 2.34/0.67    inference(subsumption_resolution,[],[f206,f56])).
% 2.34/0.67  fof(f206,plain,(
% 2.34/0.67    ( ! [X6,X4,X2,X5,X3] : (~v1_funct_1(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(X4,X5,X6))))) | ~v1_funct_2(X3,u1_struct_0(sK7),u1_struct_0(sK3(X4,X5,X6))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(X4,X5,X6))))) | v1_funct_1(k10_tmap_1(sK6,sK3(X4,X5,X6),sK7,sK8,X3,X2)) | ~v1_funct_2(X2,u1_struct_0(sK8),u1_struct_0(sK3(X4,X5,X6))) | v2_struct_0(sK3(X4,X5,X6)) | sP0(X4,X5,X6) | ~r1_tsep_1(X5,X4)) )),
% 2.34/0.67    inference(subsumption_resolution,[],[f202,f57])).
% 2.34/0.67  fof(f202,plain,(
% 2.34/0.67    ( ! [X6,X4,X2,X5,X3] : (~v1_funct_1(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(X4,X5,X6))))) | ~v1_funct_2(X3,u1_struct_0(sK7),u1_struct_0(sK3(X4,X5,X6))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(X4,X5,X6))))) | v1_funct_1(k10_tmap_1(sK6,sK3(X4,X5,X6),sK7,sK8,X3,X2)) | ~v1_funct_2(X2,u1_struct_0(sK8),u1_struct_0(sK3(X4,X5,X6))) | ~v2_pre_topc(sK3(X4,X5,X6)) | v2_struct_0(sK3(X4,X5,X6)) | sP0(X4,X5,X6) | ~r1_tsep_1(X5,X4)) )),
% 2.34/0.67    inference(resolution,[],[f191,f58])).
% 2.34/0.67  fof(f67,plain,(
% 2.34/0.67    ( ! [X2,X0,X1] : (~v1_funct_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),sK5(X0,X1,X2))) | ~m1_subset_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),sK5(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2))))) | ~v5_pre_topc(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),sK5(X0,X1,X2)),k1_tsep_1(X2,X1,X0),sK3(X0,X1,X2)) | ~v1_funct_2(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),sK5(X0,X1,X2)),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2))) | sP0(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 2.34/0.67    inference(cnf_transformation,[],[f34])).
% 2.34/0.67  fof(f54,plain,(
% 2.34/0.67    ( ! [X6,X2,X0,X8,X7,X1] : (v5_pre_topc(k10_tmap_1(X2,X6,X1,X0,X7,X8),k1_tsep_1(X2,X1,X0),X6) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X6)))) | ~v5_pre_topc(X8,X0,X6) | ~v1_funct_2(X8,u1_struct_0(X0),u1_struct_0(X6)) | ~v1_funct_1(X8) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X6)))) | ~v5_pre_topc(X7,X1,X6) | ~v1_funct_2(X7,u1_struct_0(X1),u1_struct_0(X6)) | ~v1_funct_1(X7) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6) | ~sP0(X0,X1,X2)) )),
% 2.34/0.67    inference(cnf_transformation,[],[f34])).
% 2.34/0.67  fof(f76,plain,(
% 2.34/0.67    ~sP0(sK8,sK7,sK6) | ~r3_tsep_1(sK6,sK7,sK8)),
% 2.34/0.67    inference(cnf_transformation,[],[f40])).
% 2.34/0.67  fof(f726,plain,(
% 2.34/0.67    sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(resolution,[],[f725,f59])).
% 2.34/0.67  fof(f725,plain,(
% 2.34/0.67    ~v1_funct_1(sK4(sK8,sK7,sK6))),
% 2.34/0.67    inference(subsumption_resolution,[],[f724,f134])).
% 2.34/0.67  fof(f724,plain,(
% 2.34/0.67    ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(subsumption_resolution,[],[f723,f666])).
% 2.34/0.67  fof(f723,plain,(
% 2.34/0.67    ~v1_funct_1(sK4(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(resolution,[],[f722,f63])).
% 2.34/0.67  fof(f722,plain,(
% 2.34/0.67    ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~v1_funct_1(sK4(sK8,sK7,sK6))),
% 2.34/0.67    inference(subsumption_resolution,[],[f721,f134])).
% 2.34/0.67  fof(f721,plain,(
% 2.34/0.67    ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(subsumption_resolution,[],[f720,f666])).
% 2.34/0.67  fof(f720,plain,(
% 2.34/0.67    ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(resolution,[],[f719,f56])).
% 2.34/0.67  fof(f719,plain,(
% 2.34/0.67    v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_1(sK5(sK8,sK7,sK6))),
% 2.34/0.67    inference(subsumption_resolution,[],[f718,f134])).
% 2.34/0.67  fof(f718,plain,(
% 2.34/0.67    ~v1_funct_1(sK4(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(subsumption_resolution,[],[f717,f666])).
% 2.34/0.67  fof(f717,plain,(
% 2.34/0.67    ~v1_funct_1(sK4(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(resolution,[],[f716,f60])).
% 2.34/0.67  fof(f716,plain,(
% 2.34/0.67    ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_1(sK5(sK8,sK7,sK6))),
% 2.34/0.67    inference(subsumption_resolution,[],[f715,f134])).
% 2.34/0.67  fof(f715,plain,(
% 2.34/0.67    ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(subsumption_resolution,[],[f714,f666])).
% 2.34/0.67  fof(f714,plain,(
% 2.34/0.67    ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(resolution,[],[f713,f64])).
% 2.34/0.67  fof(f713,plain,(
% 2.34/0.67    ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_1(sK5(sK8,sK7,sK6))),
% 2.34/0.67    inference(subsumption_resolution,[],[f712,f134])).
% 2.34/0.67  fof(f712,plain,(
% 2.34/0.67    ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(subsumption_resolution,[],[f711,f666])).
% 2.34/0.67  fof(f711,plain,(
% 2.34/0.67    ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(resolution,[],[f710,f62])).
% 2.34/0.67  fof(f710,plain,(
% 2.34/0.67    ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))),
% 2.34/0.67    inference(subsumption_resolution,[],[f709,f134])).
% 2.34/0.67  fof(f709,plain,(
% 2.34/0.67    ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(subsumption_resolution,[],[f708,f666])).
% 2.34/0.67  fof(f708,plain,(
% 2.34/0.67    ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(resolution,[],[f707,f66])).
% 2.34/0.67  fof(f707,plain,(
% 2.34/0.67    ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))),
% 2.34/0.67    inference(subsumption_resolution,[],[f706,f134])).
% 2.34/0.67  fof(f706,plain,(
% 2.34/0.67    ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(subsumption_resolution,[],[f705,f666])).
% 2.34/0.67  fof(f705,plain,(
% 2.34/0.67    ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(resolution,[],[f704,f57])).
% 2.34/0.67  fof(f704,plain,(
% 2.34/0.67    ~v2_pre_topc(sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))),
% 2.34/0.67    inference(subsumption_resolution,[],[f703,f134])).
% 2.34/0.67  fof(f703,plain,(
% 2.34/0.67    ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(subsumption_resolution,[],[f702,f666])).
% 2.34/0.67  fof(f702,plain,(
% 2.34/0.67    ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(resolution,[],[f701,f58])).
% 2.34/0.67  fof(f701,plain,(
% 2.34/0.67    ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6))),
% 2.34/0.67    inference(subsumption_resolution,[],[f700,f68])).
% 2.34/0.67  fof(f700,plain,(
% 2.34/0.67    v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | v2_struct_0(sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f699,f69])).
% 2.34/0.67  fof(f699,plain,(
% 2.34/0.67    v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f698,f70])).
% 2.34/0.67  fof(f698,plain,(
% 2.34/0.67    v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f697,f71])).
% 2.34/0.67  fof(f697,plain,(
% 2.34/0.67    v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | v2_struct_0(sK7) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f696,f72])).
% 2.34/0.67  fof(f696,plain,(
% 2.34/0.67    v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~m1_pre_topc(sK7,sK6) | v2_struct_0(sK7) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f695,f73])).
% 2.34/0.67  fof(f695,plain,(
% 2.34/0.67    v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | v2_struct_0(sK8) | ~m1_pre_topc(sK7,sK6) | v2_struct_0(sK7) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f694,f74])).
% 2.34/0.67  fof(f694,plain,(
% 2.34/0.67    v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~m1_pre_topc(sK8,sK6) | v2_struct_0(sK8) | ~m1_pre_topc(sK7,sK6) | v2_struct_0(sK7) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)),
% 2.34/0.67    inference(duplicate_literal_removal,[],[f691])).
% 2.34/0.67  fof(f691,plain,(
% 2.34/0.67    v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~m1_pre_topc(sK8,sK6) | v2_struct_0(sK8) | ~m1_pre_topc(sK7,sK6) | v2_struct_0(sK7) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)),
% 2.34/0.67    inference(resolution,[],[f690,f111])).
% 2.34/0.67  fof(f690,plain,(
% 2.34/0.67    ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6))),
% 2.34/0.67    inference(subsumption_resolution,[],[f689,f134])).
% 2.34/0.67  fof(f689,plain,(
% 2.34/0.67    ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(subsumption_resolution,[],[f688,f666])).
% 2.34/0.67  fof(f688,plain,(
% 2.34/0.67    ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(resolution,[],[f687,f59])).
% 2.34/0.67  fof(f687,plain,(
% 2.34/0.67    ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6))),
% 2.34/0.67    inference(subsumption_resolution,[],[f686,f134])).
% 2.34/0.67  fof(f686,plain,(
% 2.34/0.67    ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(subsumption_resolution,[],[f685,f666])).
% 2.34/0.67  fof(f685,plain,(
% 2.34/0.67    ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(resolution,[],[f684,f63])).
% 2.34/0.67  fof(f684,plain,(
% 2.34/0.67    ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6))),
% 2.34/0.67    inference(subsumption_resolution,[],[f683,f134])).
% 2.34/0.67  fof(f683,plain,(
% 2.34/0.67    ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(subsumption_resolution,[],[f682,f666])).
% 2.34/0.67  fof(f682,plain,(
% 2.34/0.67    ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(resolution,[],[f681,f60])).
% 2.34/0.67  fof(f681,plain,(
% 2.34/0.67    ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6))),
% 2.34/0.67    inference(subsumption_resolution,[],[f680,f134])).
% 2.34/0.67  fof(f680,plain,(
% 2.34/0.67    ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(subsumption_resolution,[],[f679,f666])).
% 2.34/0.67  fof(f679,plain,(
% 2.34/0.67    ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(resolution,[],[f678,f64])).
% 2.34/0.67  fof(f678,plain,(
% 2.34/0.67    ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6))),
% 2.34/0.67    inference(subsumption_resolution,[],[f677,f134])).
% 2.34/0.67  fof(f677,plain,(
% 2.34/0.67    ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(subsumption_resolution,[],[f676,f666])).
% 2.34/0.67  fof(f676,plain,(
% 2.34/0.67    ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(resolution,[],[f675,f62])).
% 2.34/0.67  fof(f675,plain,(
% 2.34/0.67    ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6))),
% 2.34/0.67    inference(subsumption_resolution,[],[f674,f134])).
% 2.34/0.67  fof(f674,plain,(
% 2.34/0.67    ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(subsumption_resolution,[],[f673,f666])).
% 2.34/0.67  fof(f673,plain,(
% 2.34/0.67    ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(resolution,[],[f672,f66])).
% 2.34/0.67  fof(f672,plain,(
% 2.34/0.67    ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6))),
% 2.34/0.67    inference(subsumption_resolution,[],[f671,f134])).
% 2.34/0.67  fof(f671,plain,(
% 2.34/0.67    ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(subsumption_resolution,[],[f670,f666])).
% 2.34/0.67  fof(f670,plain,(
% 2.34/0.67    ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(resolution,[],[f669,f57])).
% 2.34/0.67  fof(f669,plain,(
% 2.34/0.67    ~v2_pre_topc(sK3(sK8,sK7,sK6)) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6))),
% 2.34/0.67    inference(subsumption_resolution,[],[f668,f134])).
% 2.34/0.67  fof(f668,plain,(
% 2.34/0.67    v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(subsumption_resolution,[],[f667,f666])).
% 2.34/0.67  fof(f667,plain,(
% 2.34/0.67    v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(resolution,[],[f664,f58])).
% 2.34/0.67  fof(f664,plain,(
% 2.34/0.67    ~l1_pre_topc(sK3(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v2_pre_topc(sK3(sK8,sK7,sK6))),
% 2.34/0.67    inference(subsumption_resolution,[],[f663,f68])).
% 2.34/0.67  fof(f663,plain,(
% 2.34/0.67    ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | v2_struct_0(sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f662,f69])).
% 2.34/0.67  fof(f662,plain,(
% 2.34/0.67    ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f661,f70])).
% 2.34/0.67  fof(f661,plain,(
% 2.34/0.67    ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f660,f71])).
% 2.34/0.67  fof(f660,plain,(
% 2.34/0.67    ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | v2_struct_0(sK7) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f659,f72])).
% 2.34/0.67  fof(f659,plain,(
% 2.34/0.67    ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~m1_pre_topc(sK7,sK6) | v2_struct_0(sK7) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f658,f73])).
% 2.34/0.67  fof(f658,plain,(
% 2.34/0.67    ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | v2_struct_0(sK8) | ~m1_pre_topc(sK7,sK6) | v2_struct_0(sK7) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f657,f74])).
% 2.34/0.67  fof(f657,plain,(
% 2.34/0.67    ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~m1_pre_topc(sK8,sK6) | v2_struct_0(sK8) | ~m1_pre_topc(sK7,sK6) | v2_struct_0(sK7) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)),
% 2.34/0.67    inference(duplicate_literal_removal,[],[f654])).
% 2.34/0.67  fof(f654,plain,(
% 2.34/0.67    ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~m1_pre_topc(sK8,sK6) | v2_struct_0(sK8) | ~m1_pre_topc(sK7,sK6) | v2_struct_0(sK7) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)),
% 2.34/0.67    inference(resolution,[],[f653,f112])).
% 2.34/0.67  fof(f653,plain,(
% 2.34/0.67    ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6))),
% 2.34/0.67    inference(global_subsumption,[],[f76,f613,f652])).
% 2.34/0.67  fof(f652,plain,(
% 2.34/0.67    ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | v2_struct_0(sK3(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f651,f134])).
% 2.34/0.67  fof(f651,plain,(
% 2.34/0.67    ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | v2_struct_0(sK3(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(resolution,[],[f650,f59])).
% 2.34/0.67  fof(f650,plain,(
% 2.34/0.67    ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | v2_struct_0(sK3(sK8,sK7,sK6))),
% 2.34/0.67    inference(global_subsumption,[],[f76,f613,f649])).
% 2.34/0.67  fof(f649,plain,(
% 2.34/0.67    ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f648,f134])).
% 2.34/0.67  fof(f648,plain,(
% 2.34/0.67    ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(resolution,[],[f647,f63])).
% 2.34/0.67  fof(f647,plain,(
% 2.34/0.67    ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6))),
% 2.34/0.67    inference(global_subsumption,[],[f76,f613,f646])).
% 2.34/0.67  fof(f646,plain,(
% 2.34/0.67    ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f645,f134])).
% 2.34/0.67  fof(f645,plain,(
% 2.34/0.67    ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(resolution,[],[f644,f60])).
% 2.34/0.67  fof(f644,plain,(
% 2.34/0.67    ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_1(sK4(sK8,sK7,sK6))),
% 2.34/0.67    inference(global_subsumption,[],[f76,f613,f643])).
% 2.34/0.67  fof(f643,plain,(
% 2.34/0.67    ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | sP0(sK8,sK7,sK6)),
% 2.34/0.67    inference(subsumption_resolution,[],[f642,f134])).
% 2.34/0.67  fof(f642,plain,(
% 2.34/0.67    ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.67    inference(resolution,[],[f641,f64])).
% 2.34/0.68  fof(f641,plain,(
% 2.34/0.68    ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))),
% 2.34/0.68    inference(global_subsumption,[],[f76,f613,f640])).
% 2.34/0.68  fof(f640,plain,(
% 2.34/0.68    ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | sP0(sK8,sK7,sK6)),
% 2.34/0.68    inference(subsumption_resolution,[],[f639,f134])).
% 2.34/0.68  fof(f639,plain,(
% 2.34/0.68    ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.68    inference(resolution,[],[f638,f62])).
% 2.34/0.68  fof(f638,plain,(
% 2.34/0.68    ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))),
% 2.34/0.68    inference(global_subsumption,[],[f76,f613,f637])).
% 2.34/0.68  fof(f637,plain,(
% 2.34/0.68    ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | sP0(sK8,sK7,sK6)),
% 2.34/0.68    inference(subsumption_resolution,[],[f636,f134])).
% 2.34/0.68  fof(f636,plain,(
% 2.34/0.68    ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.68    inference(resolution,[],[f635,f66])).
% 2.34/0.68  fof(f635,plain,(
% 2.34/0.68    ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))),
% 2.34/0.68    inference(global_subsumption,[],[f76,f613,f634])).
% 2.34/0.68  fof(f634,plain,(
% 2.34/0.68    v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6)),
% 2.34/0.68    inference(subsumption_resolution,[],[f633,f134])).
% 2.34/0.68  fof(f633,plain,(
% 2.34/0.68    v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.68    inference(resolution,[],[f632,f57])).
% 2.34/0.68  fof(f632,plain,(
% 2.34/0.68    ~v2_pre_topc(sK3(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))),
% 2.34/0.68    inference(global_subsumption,[],[f76,f613,f631])).
% 2.34/0.68  fof(f631,plain,(
% 2.34/0.68    ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | sP0(sK8,sK7,sK6)),
% 2.34/0.68    inference(subsumption_resolution,[],[f630,f134])).
% 2.34/0.68  fof(f630,plain,(
% 2.34/0.68    ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.68    inference(resolution,[],[f629,f58])).
% 2.34/0.68  fof(f629,plain,(
% 2.34/0.68    ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))),
% 2.34/0.68    inference(global_subsumption,[],[f76,f613,f628])).
% 2.34/0.68  fof(f628,plain,(
% 2.34/0.68    v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6)),
% 2.34/0.68    inference(subsumption_resolution,[],[f627,f134])).
% 2.34/0.68  fof(f627,plain,(
% 2.34/0.68    v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.68    inference(resolution,[],[f626,f61])).
% 2.34/0.68  fof(f626,plain,(
% 2.34/0.68    ~v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_1(sK5(sK8,sK7,sK6))),
% 2.34/0.68    inference(global_subsumption,[],[f76,f613,f625])).
% 2.34/0.68  fof(f625,plain,(
% 2.34/0.68    ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6)),
% 2.34/0.68    inference(subsumption_resolution,[],[f624,f134])).
% 2.34/0.68  fof(f624,plain,(
% 2.34/0.68    ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8)),
% 2.34/0.68    inference(resolution,[],[f615,f65])).
% 2.34/0.68  fof(f615,plain,(
% 2.34/0.68    ~v5_pre_topc(sK5(sK8,sK7,sK6),sK8,sK3(sK8,sK7,sK6)) | ~m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK5(sK8,sK7,sK6)) | ~m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6)) | ~v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~v1_funct_1(sK4(sK8,sK7,sK6)) | ~l1_pre_topc(sK3(sK8,sK7,sK6)) | ~v2_pre_topc(sK3(sK8,sK7,sK6)) | v2_struct_0(sK3(sK8,sK7,sK6)) | ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))),
% 2.34/0.68    inference(resolution,[],[f613,f320])).
% 2.34/0.68  % SZS output end Proof for theBenchmark
% 2.34/0.68  % (13597)------------------------------
% 2.34/0.68  % (13597)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.34/0.68  % (13597)Termination reason: Refutation
% 2.34/0.68  
% 2.34/0.68  % (13597)Memory used [KB]: 7675
% 2.34/0.68  % (13597)Time elapsed: 0.251 s
% 2.34/0.68  % (13597)------------------------------
% 2.34/0.68  % (13597)------------------------------
% 2.34/0.68  % (13575)Success in time 0.317 s
%------------------------------------------------------------------------------
