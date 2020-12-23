%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  140 (2849 expanded)
%              Number of leaves         :   12 (1378 expanded)
%              Depth                    :   66
%              Number of atoms          : 1025 (54577 expanded)
%              Number of equality atoms :   36 ( 252 expanded)
%              Maximal formula depth    :   19 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f148,plain,(
    $false ),
    inference(subsumption_resolution,[],[f147,f29])).

fof(f29,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1)
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4)) )
    & m1_pre_topc(sK3,sK2)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    & v5_pre_topc(sK4,sK2,sK1)
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    & v1_funct_1(sK4)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f10,f26,f25,f24,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1)
                          | ~ v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
                        & m1_pre_topc(X3,X2)
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v5_pre_topc(X4,X2,X1)
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
                      ( ( ~ m1_subset_1(k3_tmap_1(sK0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k3_tmap_1(sK0,X1,X2,X3,X4),X3,X1)
                        | ~ v1_funct_2(k3_tmap_1(sK0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k3_tmap_1(sK0,X1,X2,X3,X4)) )
                      & m1_pre_topc(X3,X2)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ( ~ m1_subset_1(k3_tmap_1(sK0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v5_pre_topc(k3_tmap_1(sK0,X1,X2,X3,X4),X3,X1)
                      | ~ v1_funct_2(k3_tmap_1(sK0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(k3_tmap_1(sK0,X1,X2,X3,X4)) )
                    & m1_pre_topc(X3,X2)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    & v5_pre_topc(X4,X2,X1)
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,X2,X3,X4),X3,sK1)
                    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(sK1))
                    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X2,X3,X4)) )
                  & m1_pre_topc(X3,X2)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
                  & v5_pre_topc(X4,X2,sK1)
                  & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK1))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                  | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,X2,X3,X4),X3,sK1)
                  | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(sK1))
                  | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X2,X3,X4)) )
                & m1_pre_topc(X3,X2)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
                & v5_pre_topc(X4,X2,sK1)
                & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,X3,X4),X3,sK1)
                | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,X3,X4),u1_struct_0(X3),u1_struct_0(sK1))
                | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,X3,X4)) )
              & m1_pre_topc(X3,sK2)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
              & v5_pre_topc(X4,sK2,sK1)
              & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
              | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,X3,X4),X3,sK1)
              | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,X3,X4),u1_struct_0(X3),u1_struct_0(sK1))
              | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,X3,X4)) )
            & m1_pre_topc(X3,sK2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
            & v5_pre_topc(X4,sK2,sK1)
            & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
            | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,X4),sK3,sK1)
            | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,X4),u1_struct_0(sK3),u1_struct_0(sK1))
            | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,X4)) )
          & m1_pre_topc(sK3,sK2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
          & v5_pre_topc(X4,sK2,sK1)
          & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X4] :
        ( ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
          | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,X4),sK3,sK1)
          | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,X4),u1_struct_0(sK3),u1_struct_0(sK1))
          | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,X4)) )
        & m1_pre_topc(sK3,sK2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        & v5_pre_topc(X4,sK2,sK1)
        & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1))
        & v1_funct_1(X4) )
   => ( ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1)
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4)) )
      & m1_pre_topc(sK3,sK2)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      & v5_pre_topc(sK4,sK2,sK1)
      & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1)
                        | ~ v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
                      & m1_pre_topc(X3,X2)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1)
                        | ~ v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
                      & m1_pre_topc(X3,X2)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(X4,X2,X1)
                          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( m1_pre_topc(X3,X2)
                         => ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) ) ) ) ) ) ) ) ),
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
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v5_pre_topc(X4,X2,X1)
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_tmap_1)).

fof(f147,plain,(
    ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f146,f30])).

fof(f30,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f146,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f145,f35])).

fof(f35,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f145,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f144,f30])).

fof(f144,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f143,f35])).

fof(f143,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK2,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(resolution,[],[f142,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f142,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK2)
      | ~ m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f141,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f141,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f140,f34])).

fof(f34,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f140,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f139,f31])).

fof(f31,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f139,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f138,f32])).

fof(f32,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f138,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f137,f33])).

fof(f33,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f137,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f136,f38])).

fof(f38,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f136,plain,
    ( ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f135,f39])).

fof(f39,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f135,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f134,f40])).

fof(f40,plain,(
    v5_pre_topc(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f134,plain,
    ( ~ v5_pre_topc(sK4,sK2,sK1)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f133,f41])).

fof(f41,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f27])).

fof(f133,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(sK4,sK2,sK1)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f132,f36])).

fof(f36,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f132,plain,
    ( v2_struct_0(sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(sK4,sK2,sK1)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f131,f42])).

fof(f42,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f131,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(sK4,sK2,sK1)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f130,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_pre_topc(X3,X0)
        & ~ v2_struct_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v5_pre_topc(X2,X0,X1)
        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(X2)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tmap_1)).

fof(f130,plain,(
    ~ v5_pre_topc(k2_tmap_1(sK2,sK1,sK4,sK3),sK3,sK1) ),
    inference(subsumption_resolution,[],[f118,f129])).

fof(f129,plain,(
    v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) ),
    inference(subsumption_resolution,[],[f128,f28])).

fof(f28,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f128,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f127,f29])).

fof(f127,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f126,f30])).

fof(f126,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f125,f31])).

fof(f125,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f124,f32])).

fof(f124,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f123,f33])).

fof(f123,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f122,f35])).

fof(f122,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f121,f37])).

fof(f37,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f121,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f120,f38])).

fof(f120,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f119,f39])).

fof(f119,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f94,f41])).

fof(f94,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f51,f86])).

fof(f86,plain,(
    k3_tmap_1(sK0,sK1,sK2,sK3,sK4) = k2_tmap_1(sK2,sK1,sK4,sK3) ),
    inference(subsumption_resolution,[],[f85,f29])).

fof(f85,plain,
    ( k3_tmap_1(sK0,sK1,sK2,sK3,sK4) = k2_tmap_1(sK2,sK1,sK4,sK3)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f84,f30])).

fof(f84,plain,
    ( k3_tmap_1(sK0,sK1,sK2,sK3,sK4) = k2_tmap_1(sK2,sK1,sK4,sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f83,f35])).

fof(f83,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK2,X0)
      | k3_tmap_1(sK0,sK1,sK2,sK3,sK4) = k2_tmap_1(sK2,sK1,sK4,sK3)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f82,f30])).

fof(f82,plain,(
    ! [X0] :
      ( k3_tmap_1(sK0,sK1,sK2,sK3,sK4) = k2_tmap_1(sK2,sK1,sK4,sK3)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f81,f35])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(sK2,X0)
      | k3_tmap_1(sK0,sK1,sK2,sK3,sK4) = k2_tmap_1(sK2,sK1,sK4,sK3)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK2,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(resolution,[],[f80,f47])).

fof(f80,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK2)
      | k3_tmap_1(sK0,sK1,sK2,sK3,sK4) = k2_tmap_1(sK2,sK1,sK4,sK3)
      | ~ m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f79,f44])).

fof(f79,plain,
    ( ~ l1_pre_topc(sK2)
    | k3_tmap_1(sK0,sK1,sK2,sK3,sK4) = k2_tmap_1(sK2,sK1,sK4,sK3)
    | ~ v2_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f78,f34])).

fof(f78,plain,
    ( k3_tmap_1(sK0,sK1,sK2,sK3,sK4) = k2_tmap_1(sK2,sK1,sK4,sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f77,f31])).

fof(f77,plain,
    ( k3_tmap_1(sK0,sK1,sK2,sK3,sK4) = k2_tmap_1(sK2,sK1,sK4,sK3)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f76,f32])).

fof(f76,plain,
    ( k3_tmap_1(sK0,sK1,sK2,sK3,sK4) = k2_tmap_1(sK2,sK1,sK4,sK3)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f75,f33])).

fof(f75,plain,
    ( k3_tmap_1(sK0,sK1,sK2,sK3,sK4) = k2_tmap_1(sK2,sK1,sK4,sK3)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f74,f38])).

fof(f74,plain,
    ( k3_tmap_1(sK0,sK1,sK2,sK3,sK4) = k2_tmap_1(sK2,sK1,sK4,sK3)
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f73,f39])).

fof(f73,plain,
    ( k3_tmap_1(sK0,sK1,sK2,sK3,sK4) = k2_tmap_1(sK2,sK1,sK4,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f72,f41])).

fof(f72,plain,
    ( k3_tmap_1(sK0,sK1,sK2,sK3,sK4) = k2_tmap_1(sK2,sK1,sK4,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f70,f42])).

fof(f70,plain,
    ( k3_tmap_1(sK0,sK1,sK2,sK3,sK4) = k2_tmap_1(sK2,sK1,sK4,sK3)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(superposition,[],[f69,f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f69,plain,(
    k3_tmap_1(sK0,sK1,sK2,sK3,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f68,f37])).

fof(f68,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | k3_tmap_1(sK0,sK1,sK2,sK3,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) ),
    inference(resolution,[],[f67,f42])).

fof(f67,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | ~ m1_pre_topc(X0,sK0)
      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK2,X0,sK4) ) ),
    inference(subsumption_resolution,[],[f66,f28])).

fof(f66,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK2,X0,sK4)
      | ~ m1_pre_topc(X0,sK0)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f65,f29])).

fof(f65,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK2,X0,sK4)
      | ~ m1_pre_topc(X0,sK0)
      | ~ m1_pre_topc(X0,sK2)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f64,f30])).

fof(f64,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK2,X0,sK4)
      | ~ m1_pre_topc(X0,sK0)
      | ~ m1_pre_topc(X0,sK2)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f61,f35])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(sK2,X1)
      | k3_tmap_1(X1,sK1,sK2,X0,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(X0,sK2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f60,f31])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | k3_tmap_1(X1,sK1,sK2,X0,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK2,X1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f59,f32])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | k3_tmap_1(X1,sK1,sK2,X0,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK2,X1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f58,f33])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | k3_tmap_1(X1,sK1,sK2,X0,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK2,X1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f57,f38])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | k3_tmap_1(X1,sK1,sK2,X0,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0))
      | ~ v1_funct_1(sK4)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK2,X1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f54,f39])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | k3_tmap_1(X1,sK1,sK2,X0,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0))
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ v1_funct_1(sK4)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK2,X1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f45,f41])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X2)
      | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
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
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(X4)
        & m1_pre_topc(X3,X0)
        & m1_pre_topc(X2,X0)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_tmap_1)).

fof(f118,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK1,sK4,sK3),sK3,sK1) ),
    inference(subsumption_resolution,[],[f106,f117])).

fof(f117,plain,(
    v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f116,f28])).

fof(f116,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f115,f29])).

fof(f115,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f114,f30])).

fof(f114,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f113,f31])).

fof(f113,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f112,f32])).

fof(f112,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f111,f33])).

fof(f111,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f110,f35])).

fof(f110,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f109,f37])).

fof(f109,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f108,f38])).

fof(f108,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f107,f39])).

fof(f107,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f93,f41])).

fof(f93,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f52,f86])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f106,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK1,sK4,sK3),sK3,sK1) ),
    inference(subsumption_resolution,[],[f91,f105])).

fof(f105,plain,(
    m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f104,f28])).

fof(f104,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f103,f29])).

fof(f103,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f102,f30])).

fof(f102,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f101,f31])).

fof(f101,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f100,f32])).

fof(f100,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f99,f33])).

fof(f99,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f98,f35])).

fof(f98,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f97,f37])).

fof(f97,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f96,f38])).

fof(f96,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f95,f39])).

fof(f95,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f92,f41])).

fof(f92,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f53,f86])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f91,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK1,sK4,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(forward_demodulation,[],[f90,f86])).

fof(f90,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK1,sK4,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4)) ),
    inference(forward_demodulation,[],[f89,f86])).

fof(f89,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK2,sK1,sK4,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4)) ),
    inference(forward_demodulation,[],[f87,f86])).

fof(f87,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4)) ),
    inference(backward_demodulation,[],[f43,f86])).

fof(f43,plain,
    ( ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:34:12 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.21/0.45  % (24567)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.46  % (24575)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.47  % (24558)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.47  % (24575)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f148,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(subsumption_resolution,[],[f147,f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    v2_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    (((((~m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4))) & m1_pre_topc(sK3,sK2) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(sK4,sK2,sK1) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f10,f26,f25,f24,f23,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) & m1_pre_topc(X3,X2) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k3_tmap_1(sK0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(sK0,X1,X2,X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(sK0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(sK0,X1,X2,X3,X4))) & m1_pre_topc(X3,X2) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k3_tmap_1(sK0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(sK0,X1,X2,X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(sK0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(sK0,X1,X2,X3,X4))) & m1_pre_topc(X3,X2) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k3_tmap_1(sK0,sK1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,X2,X3,X4),X3,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,X2,X3,X4))) & m1_pre_topc(X3,X2) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v5_pre_topc(X4,X2,sK1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k3_tmap_1(sK0,sK1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,X2,X3,X4),X3,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,X2,X3,X4))) & m1_pre_topc(X3,X2) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v5_pre_topc(X4,X2,sK1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : ((~m1_subset_1(k3_tmap_1(sK0,sK1,sK2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,X3,X4),X3,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK2,X3,X4),u1_struct_0(X3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK2,X3,X4))) & m1_pre_topc(X3,sK2) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(X4,sK2,sK1) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ? [X3] : (? [X4] : ((~m1_subset_1(k3_tmap_1(sK0,sK1,sK2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,X3,X4),X3,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK2,X3,X4),u1_struct_0(X3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK2,X3,X4))) & m1_pre_topc(X3,sK2) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(X4,sK2,sK1) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (? [X4] : ((~m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,X4),sK3,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,X4),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,X4))) & m1_pre_topc(sK3,sK2) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(X4,sK2,sK1) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ? [X4] : ((~m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,X4),sK3,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,X4),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,X4))) & m1_pre_topc(sK3,sK2) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(X4,sK2,sK1) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X4)) => ((~m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4))) & m1_pre_topc(sK3,sK2) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(sK4,sK2,sK1) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK4))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) & m1_pre_topc(X3,X2) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((~m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) & m1_pre_topc(X3,X2)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)))))))))),
% 0.21/0.48    inference(negated_conjecture,[],[f7])).
% 0.21/0.48  fof(f7,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)))))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_tmap_1)).
% 0.21/0.48  fof(f147,plain,(
% 0.21/0.48    ~v2_pre_topc(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f146,f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    l1_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f146,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.48    inference(resolution,[],[f145,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    m1_pre_topc(sK2,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f145,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f144,f30])).
% 0.21/0.48  fof(f144,plain,(
% 0.21/0.48    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.48    inference(resolution,[],[f143,f35])).
% 0.21/0.48  fof(f143,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK2,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 0.21/0.48    inference(resolution,[],[f142,f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.21/0.48  fof(f142,plain,(
% 0.21/0.48    ( ! [X0] : (~v2_pre_topc(sK2) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(resolution,[],[f141,f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f140,f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ~v2_struct_0(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f140,plain,(
% 0.21/0.48    ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f139,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ~v2_struct_0(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f139,plain,(
% 0.21/0.48    v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f138,f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    v2_pre_topc(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f138,plain,(
% 0.21/0.48    ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f137,f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    l1_pre_topc(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f137,plain,(
% 0.21/0.48    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f136,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    v1_funct_1(sK4)),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f136,plain,(
% 0.21/0.48    ~v1_funct_1(sK4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f135,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f134,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    v5_pre_topc(sK4,sK2,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    ~v5_pre_topc(sK4,sK2,sK1) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f133,f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f133,plain,(
% 0.21/0.48    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v5_pre_topc(sK4,sK2,sK1) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f132,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ~v2_struct_0(sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f132,plain,(
% 0.21/0.48    v2_struct_0(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v5_pre_topc(sK4,sK2,sK1) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f131,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    m1_pre_topc(sK3,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    ~m1_pre_topc(sK3,sK2) | v2_struct_0(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v5_pre_topc(sK4,sK2,sK1) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.21/0.48    inference(resolution,[],[f130,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tmap_1)).
% 0.21/0.48  fof(f130,plain,(
% 0.21/0.48    ~v5_pre_topc(k2_tmap_1(sK2,sK1,sK4,sK3),sK3,sK1)),
% 0.21/0.48    inference(subsumption_resolution,[],[f118,f129])).
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))),
% 0.21/0.48    inference(subsumption_resolution,[],[f128,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ~v2_struct_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f127,f29])).
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f126,f30])).
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f125,f31])).
% 0.21/0.48  fof(f125,plain,(
% 0.21/0.48    v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f124,f32])).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f123,f33])).
% 0.21/0.48  fof(f123,plain,(
% 0.21/0.48    v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f122,f35])).
% 0.21/0.48  fof(f122,plain,(
% 0.21/0.48    v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f121,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    m1_pre_topc(sK3,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f121,plain,(
% 0.21/0.48    v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f120,f38])).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f119,f39])).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f94,f41])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(superposition,[],[f51,f86])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    k3_tmap_1(sK0,sK1,sK2,sK3,sK4) = k2_tmap_1(sK2,sK1,sK4,sK3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f85,f29])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    k3_tmap_1(sK0,sK1,sK2,sK3,sK4) = k2_tmap_1(sK2,sK1,sK4,sK3) | ~v2_pre_topc(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f84,f30])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    k3_tmap_1(sK0,sK1,sK2,sK3,sK4) = k2_tmap_1(sK2,sK1,sK4,sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.48    inference(resolution,[],[f83,f35])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_pre_topc(sK2,X0) | k3_tmap_1(sK0,sK1,sK2,sK3,sK4) = k2_tmap_1(sK2,sK1,sK4,sK3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f82,f30])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    ( ! [X0] : (k3_tmap_1(sK0,sK1,sK2,sK3,sK4) = k2_tmap_1(sK2,sK1,sK4,sK3) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.48    inference(resolution,[],[f81,f35])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_pre_topc(sK2,X0) | k3_tmap_1(sK0,sK1,sK2,sK3,sK4) = k2_tmap_1(sK2,sK1,sK4,sK3) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK2,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 0.21/0.48    inference(resolution,[],[f80,f47])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    ( ! [X0] : (~v2_pre_topc(sK2) | k3_tmap_1(sK0,sK1,sK2,sK3,sK4) = k2_tmap_1(sK2,sK1,sK4,sK3) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(resolution,[],[f79,f44])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    ~l1_pre_topc(sK2) | k3_tmap_1(sK0,sK1,sK2,sK3,sK4) = k2_tmap_1(sK2,sK1,sK4,sK3) | ~v2_pre_topc(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f78,f34])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    k3_tmap_1(sK0,sK1,sK2,sK3,sK4) = k2_tmap_1(sK2,sK1,sK4,sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f77,f31])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    k3_tmap_1(sK0,sK1,sK2,sK3,sK4) = k2_tmap_1(sK2,sK1,sK4,sK3) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f76,f32])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    k3_tmap_1(sK0,sK1,sK2,sK3,sK4) = k2_tmap_1(sK2,sK1,sK4,sK3) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f75,f33])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    k3_tmap_1(sK0,sK1,sK2,sK3,sK4) = k2_tmap_1(sK2,sK1,sK4,sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f74,f38])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    k3_tmap_1(sK0,sK1,sK2,sK3,sK4) = k2_tmap_1(sK2,sK1,sK4,sK3) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f73,f39])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    k3_tmap_1(sK0,sK1,sK2,sK3,sK4) = k2_tmap_1(sK2,sK1,sK4,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f72,f41])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    k3_tmap_1(sK0,sK1,sK2,sK3,sK4) = k2_tmap_1(sK2,sK1,sK4,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f70,f42])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    k3_tmap_1(sK0,sK1,sK2,sK3,sK4) = k2_tmap_1(sK2,sK1,sK4,sK3) | ~m1_pre_topc(sK3,sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.21/0.48    inference(superposition,[],[f69,f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    k3_tmap_1(sK0,sK1,sK2,sK3,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3))),
% 0.21/0.48    inference(subsumption_resolution,[],[f68,f37])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ~m1_pre_topc(sK3,sK0) | k3_tmap_1(sK0,sK1,sK2,sK3,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3))),
% 0.21/0.48    inference(resolution,[],[f67,f42])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_pre_topc(X0,sK2) | ~m1_pre_topc(X0,sK0) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK2,X0,sK4)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f66,f28])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ( ! [X0] : (k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK2,X0,sK4) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X0,sK2) | v2_struct_0(sK0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f65,f29])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ( ! [X0] : (k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK2,X0,sK4) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X0,sK2) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f64,f30])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    ( ! [X0] : (k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK2,X0,sK4) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X0,sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.48    inference(resolution,[],[f61,f35])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_pre_topc(sK2,X1) | k3_tmap_1(X1,sK1,sK2,X0,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,sK2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f60,f31])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | k3_tmap_1(X1,sK1,sK2,X0,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f59,f32])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | k3_tmap_1(X1,sK1,sK2,X0,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f58,f33])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | k3_tmap_1(X1,sK1,sK2,X0,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f57,f38])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | k3_tmap_1(X1,sK1,sK2,X0,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | ~v1_funct_1(sK4) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f54,f39])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | k3_tmap_1(X1,sK1,sK2,X0,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.21/0.48    inference(resolution,[],[f45,f41])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_tmap_1)).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    ~v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) | ~v5_pre_topc(k2_tmap_1(sK2,sK1,sK4,sK3),sK3,sK1)),
% 0.21/0.48    inference(subsumption_resolution,[],[f106,f117])).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f116,f28])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f115,f29])).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f114,f30])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f113,f31])).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f112,f32])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f111,f33])).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f110,f35])).
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f109,f37])).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f108,f38])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f107,f39])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f93,f41])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(superposition,[],[f52,f86])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    ~v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) | ~v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK2,sK1,sK4,sK3),sK3,sK1)),
% 0.21/0.48    inference(subsumption_resolution,[],[f91,f105])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.21/0.48    inference(subsumption_resolution,[],[f104,f28])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f103,f29])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f102,f30])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f101,f31])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f100,f32])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f99,f33])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f98,f35])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f97,f37])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f96,f38])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f95,f39])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f92,f41])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(superposition,[],[f53,f86])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    ~v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) | ~v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK2,sK1,sK4,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.21/0.48    inference(forward_demodulation,[],[f90,f86])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    ~v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK2,sK1,sK4,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4))),
% 0.21/0.48    inference(forward_demodulation,[],[f89,f86])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    ~v5_pre_topc(k2_tmap_1(sK2,sK1,sK4,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4))),
% 0.21/0.48    inference(forward_demodulation,[],[f87,f86])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    ~m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4))),
% 0.21/0.48    inference(backward_demodulation,[],[f43,f86])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4))),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (24575)------------------------------
% 0.21/0.48  % (24575)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (24575)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (24575)Memory used [KB]: 6268
% 0.21/0.48  % (24575)Time elapsed: 0.073 s
% 0.21/0.48  % (24575)------------------------------
% 0.21/0.48  % (24575)------------------------------
% 0.21/0.48  % (24555)Success in time 0.127 s
%------------------------------------------------------------------------------
