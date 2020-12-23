%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tmap_1__t50_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:16 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  122 (23648 expanded)
%              Number of leaves         :   16 (12868 expanded)
%              Depth                    :   22
%              Number of atoms          :  942 (477552 expanded)
%              Number of equality atoms :   19 (20266 expanded)
%              Maximal formula depth    :   22 (   9 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f641,plain,(
    $false ),
    inference(global_subsumption,[],[f552,f637])).

fof(f637,plain,(
    ~ r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK7(sK0,sK1,sK3,sK5,sK6(sK0,sK2,sK3,sK5))),sK6(sK0,sK2,sK3,sK5)) ),
    inference(unit_resulting_resolution,[],[f78,f79,f80,f89,f450,f90,f91,f551,f550,f549,f218])).

fof(f218,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X1,X2),sK6(X0,sK2,X1,X3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
      | r1_tmap_1(X0,sK2,X1,X3)
      | ~ r2_hidden(X3,X2)
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f217,f87])).

fof(f87,plain,(
    u1_struct_0(sK1) = u1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,
    ( ~ r1_tmap_1(sK0,sK2,sK4,sK5)
    & r1_tmap_1(sK0,sK1,sK3,sK5)
    & m1_subset_1(sK5,u1_struct_0(sK0))
    & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),sK3,sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
    & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK2))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK3)
    & r1_tarski(u1_pre_topc(sK2),u1_pre_topc(sK1))
    & u1_struct_0(sK1) = u1_struct_0(sK2)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f36,f64,f63,f62,f61,f60,f59])).

fof(f59,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ~ r1_tmap_1(X0,X2,X4,X5)
                            & r1_tmap_1(X0,X1,X3,X5)
                            & m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),X3,X4)
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X2))
                        & v1_funct_1(X4) )
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                & r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1))
                & u1_struct_0(X1) = u1_struct_0(X2)
                & l1_pre_topc(X2)
                & v2_pre_topc(X2)
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
                      ( ? [X5] :
                          ( ~ r1_tmap_1(sK0,X2,X4,X5)
                          & r1_tmap_1(sK0,X1,X3,X5)
                          & m1_subset_1(X5,u1_struct_0(sK0)) )
                      & r1_funct_2(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(sK0),u1_struct_0(X2),X3,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2))))
                      & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X2))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1))
              & u1_struct_0(X1) = u1_struct_0(X2)
              & l1_pre_topc(X2)
              & v2_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r1_tmap_1(X0,X2,X4,X5)
                          & r1_tmap_1(X0,X1,X3,X5)
                          & m1_subset_1(X5,u1_struct_0(X0)) )
                      & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),X3,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X2))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1))
              & u1_struct_0(X1) = u1_struct_0(X2)
              & l1_pre_topc(X2)
              & v2_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ~ r1_tmap_1(X0,X2,X4,X5)
                        & r1_tmap_1(X0,sK1,X3,X5)
                        & m1_subset_1(X5,u1_struct_0(X0)) )
                    & r1_funct_2(u1_struct_0(X0),u1_struct_0(sK1),u1_struct_0(X0),u1_struct_0(X2),X3,X4)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                    & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X2))
                    & v1_funct_1(X4) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
                & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(sK1))
                & v1_funct_1(X3) )
            & r1_tarski(u1_pre_topc(X2),u1_pre_topc(sK1))
            & u1_struct_0(sK1) = u1_struct_0(X2)
            & l1_pre_topc(X2)
            & v2_pre_topc(X2)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ~ r1_tmap_1(X0,X2,X4,X5)
                      & r1_tmap_1(X0,X1,X3,X5)
                      & m1_subset_1(X5,u1_struct_0(X0)) )
                  & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),X3,X4)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                  & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X2))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X3) )
          & r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1))
          & u1_struct_0(X1) = u1_struct_0(X2)
          & l1_pre_topc(X2)
          & v2_pre_topc(X2)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ~ r1_tmap_1(X0,sK2,X4,X5)
                    & r1_tmap_1(X0,X1,X3,X5)
                    & m1_subset_1(X5,u1_struct_0(X0)) )
                & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(sK2),X3,X4)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
                & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK2))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
            & v1_funct_1(X3) )
        & r1_tarski(u1_pre_topc(sK2),u1_pre_topc(X1))
        & u1_struct_0(sK2) = u1_struct_0(X1)
        & l1_pre_topc(sK2)
        & v2_pre_topc(sK2)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ~ r1_tmap_1(X0,X2,X4,X5)
                  & r1_tmap_1(X0,X1,X3,X5)
                  & m1_subset_1(X5,u1_struct_0(X0)) )
              & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),X3,X4)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
              & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X2))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ~ r1_tmap_1(X0,X2,X4,X5)
                & r1_tmap_1(X0,X1,sK3,X5)
                & m1_subset_1(X5,u1_struct_0(X0)) )
            & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),sK3,X4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X2))
            & v1_funct_1(X4) )
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ~ r1_tmap_1(X0,X2,X4,X5)
              & r1_tmap_1(X0,X1,X3,X5)
              & m1_subset_1(X5,u1_struct_0(X0)) )
          & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),X3,X4)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X2))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ~ r1_tmap_1(X0,X2,sK4,X5)
            & r1_tmap_1(X0,X1,X3,X5)
            & m1_subset_1(X5,u1_struct_0(X0)) )
        & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),X3,sK4)
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
        & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X2))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ~ r1_tmap_1(X0,X2,X4,X5)
          & r1_tmap_1(X0,X1,X3,X5)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ~ r1_tmap_1(X0,X2,X4,sK5)
        & r1_tmap_1(X0,X1,X3,sK5)
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r1_tmap_1(X0,X2,X4,X5)
                          & r1_tmap_1(X0,X1,X3,X5)
                          & m1_subset_1(X5,u1_struct_0(X0)) )
                      & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),X3,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X2))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1))
              & u1_struct_0(X1) = u1_struct_0(X2)
              & l1_pre_topc(X2)
              & v2_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r1_tmap_1(X0,X2,X4,X5)
                          & r1_tmap_1(X0,X1,X3,X5)
                          & m1_subset_1(X5,u1_struct_0(X0)) )
                      & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),X3,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X2))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1))
              & u1_struct_0(X1) = u1_struct_0(X2)
              & l1_pre_topc(X2)
              & v2_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( l1_pre_topc(X2)
                  & v2_pre_topc(X2)
                  & ~ v2_struct_0(X2) )
               => ( ( r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1))
                    & u1_struct_0(X1) = u1_struct_0(X2) )
                 => ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X3) )
                     => ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X2))
                            & v1_funct_1(X4) )
                         => ( r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),X3,X4)
                           => ! [X5] :
                                ( m1_subset_1(X5,u1_struct_0(X0))
                               => ( r1_tmap_1(X0,X1,X3,X5)
                                 => r1_tmap_1(X0,X2,X4,X5) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ( ( r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1))
                  & u1_struct_0(X1) = u1_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X2))
                          & v1_funct_1(X4) )
                       => ( r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),X3,X4)
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X0))
                             => ( r1_tmap_1(X0,X1,X3,X5)
                               => r1_tmap_1(X0,X2,X4,X5) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t50_tmap_1.p',t50_tmap_1)).

fof(f217,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
      | ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X1,X2),sK6(X0,sK2,X1,X3))
      | r1_tmap_1(X0,sK2,X1,X3)
      | ~ r2_hidden(X3,X2)
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK2))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f216,f87])).

fof(f216,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X1,X2),sK6(X0,sK2,X1,X3))
      | r1_tmap_1(X0,sK2,X1,X3)
      | ~ r2_hidden(X3,X2)
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK2))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f215,f84])).

fof(f84,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f215,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X1,X2),sK6(X0,sK2,X1,X3))
      | r1_tmap_1(X0,sK2,X1,X3)
      | ~ r2_hidden(X3,X2)
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK2))
      | ~ v1_funct_1(X1)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f214,f85])).

fof(f85,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f214,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X1,X2),sK6(X0,sK2,X1,X3))
      | r1_tmap_1(X0,sK2,X1,X3)
      | ~ r2_hidden(X3,X2)
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK2))
      | ~ v1_funct_1(X1)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f207,f86])).

fof(f86,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f207,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X1,X2),sK6(X0,sK2,X1,X3))
      | r1_tmap_1(X0,sK2,X1,X3)
      | ~ r2_hidden(X3,X2)
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK2))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f205,f87])).

fof(f205,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),sK6(X0,X1,X2,X3))
      | r1_tmap_1(X0,X1,X2,X3)
      | ~ r2_hidden(X3,X5)
      | ~ v3_pre_topc(X5,X0)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f106,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t50_tmap_1.p',t4_subset)).

fof(f106,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X0,X1,X2,X3)
      | ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),sK6(X0,X1,X2,X3))
      | ~ r2_hidden(X3,X5)
      | ~ v3_pre_topc(X5,X0)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r1_tmap_1(X0,X1,X2,X3)
                      | ( ! [X5] :
                            ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),sK6(X0,X1,X2,X3))
                            | ~ r2_hidden(X3,X5)
                            | ~ v3_pre_topc(X5,X0)
                            | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                        & r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),sK6(X0,X1,X2,X3))
                        & v3_pre_topc(sK6(X0,X1,X2,X3),X1)
                        & m1_subset_1(sK6(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1))) ) )
                    & ( ! [X6] :
                          ( ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK7(X0,X1,X2,X3,X6)),X6)
                            & r2_hidden(X3,sK7(X0,X1,X2,X3,X6))
                            & v3_pre_topc(sK7(X0,X1,X2,X3,X6),X0)
                            & m1_subset_1(sK7(X0,X1,X2,X3,X6),k1_zfmisc_1(u1_struct_0(X0))) )
                          | ~ r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X6)
                          | ~ v3_pre_topc(X6,X1)
                          | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) )
                      | ~ r1_tmap_1(X0,X1,X2,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f67,f69,f68])).

fof(f68,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
              | ~ r2_hidden(X3,X5)
              | ~ v3_pre_topc(X5,X0)
              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
          & r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X4)
          & v3_pre_topc(X4,X1)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ! [X5] :
            ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),sK6(X0,X1,X2,X3))
            | ~ r2_hidden(X3,X5)
            | ~ v3_pre_topc(X5,X0)
            | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
        & r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),sK6(X0,X1,X2,X3))
        & v3_pre_topc(sK6(X0,X1,X2,X3),X1)
        & m1_subset_1(sK6(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ! [X6,X3,X2,X1,X0] :
      ( ? [X7] :
          ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X7),X6)
          & r2_hidden(X3,X7)
          & v3_pre_topc(X7,X0)
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK7(X0,X1,X2,X3,X6)),X6)
        & r2_hidden(X3,sK7(X0,X1,X2,X3,X6))
        & v3_pre_topc(sK7(X0,X1,X2,X3,X6),X0)
        & m1_subset_1(sK7(X0,X1,X2,X3,X6),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r1_tmap_1(X0,X1,X2,X3)
                      | ? [X4] :
                          ( ! [X5] :
                              ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                              | ~ r2_hidden(X3,X5)
                              | ~ v3_pre_topc(X5,X0)
                              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                          & r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X4)
                          & v3_pre_topc(X4,X1)
                          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) ) )
                    & ( ! [X6] :
                          ( ? [X7] :
                              ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X7),X6)
                              & r2_hidden(X3,X7)
                              & v3_pre_topc(X7,X0)
                              & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0))) )
                          | ~ r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X6)
                          | ~ v3_pre_topc(X6,X1)
                          | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) )
                      | ~ r1_tmap_1(X0,X1,X2,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r1_tmap_1(X0,X1,X2,X3)
                      | ? [X4] :
                          ( ! [X5] :
                              ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                              | ~ r2_hidden(X3,X5)
                              | ~ v3_pre_topc(X5,X0)
                              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                          & r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X4)
                          & v3_pre_topc(X4,X1)
                          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) ) )
                    & ( ! [X4] :
                          ( ? [X5] :
                              ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                              & r2_hidden(X3,X5)
                              & v3_pre_topc(X5,X0)
                              & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                          | ~ r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X4)
                          | ~ v3_pre_topc(X4,X1)
                          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                      | ~ r1_tmap_1(X0,X1,X2,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r1_tmap_1(X0,X1,X2,X3)
                  <=> ! [X4] :
                        ( ? [X5] :
                            ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                            & r2_hidden(X3,X5)
                            & v3_pre_topc(X5,X0)
                            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X4)
                        | ~ v3_pre_topc(X4,X1)
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r1_tmap_1(X0,X1,X2,X3)
                  <=> ! [X4] :
                        ( ? [X5] :
                            ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                            & r2_hidden(X3,X5)
                            & v3_pre_topc(X5,X0)
                            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X4)
                        | ~ v3_pre_topc(X4,X1)
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
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
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r1_tmap_1(X0,X1,X2,X3)
                  <=> ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ~ ( ! [X5] :
                                ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
                               => ~ ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                                    & r2_hidden(X3,X5)
                                    & v3_pre_topc(X5,X0) ) )
                            & r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X4)
                            & v3_pre_topc(X4,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t50_tmap_1.p',t48_tmap_1)).

fof(f549,plain,(
    m1_subset_1(sK7(sK0,sK1,sK3,sK5,sK6(sK0,sK2,sK3,sK5)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f78,f79,f80,f81,f82,f83,f89,f96,f97,f90,f91,f458,f460,f538,f99])).

fof(f99,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( ~ r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X6)
      | m1_subset_1(sK7(X0,X1,X2,X3,X6),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X6,X1)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_tmap_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f538,plain,(
    v3_pre_topc(sK6(sK0,sK2,sK3,sK5),sK1) ),
    inference(unit_resulting_resolution,[],[f83,f458,f525,f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t50_tmap_1.p',d5_pre_topc)).

fof(f525,plain,(
    r2_hidden(sK6(sK0,sK2,sK3,sK5),u1_pre_topc(sK1)) ),
    inference(unit_resulting_resolution,[],[f315,f510,f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t50_tmap_1.p',t2_subset)).

fof(f510,plain,(
    m1_subset_1(sK6(sK0,sK2,sK3,sK5),u1_pre_topc(sK1)) ),
    inference(unit_resulting_resolution,[],[f135,f459,f119])).

fof(f459,plain,(
    r2_hidden(sK6(sK0,sK2,sK3,sK5),u1_pre_topc(sK2)) ),
    inference(backward_demodulation,[],[f432,f304])).

fof(f304,plain,(
    r2_hidden(sK6(sK0,sK2,sK4,sK5),u1_pre_topc(sK2)) ),
    inference(unit_resulting_resolution,[],[f219,f291,f155])).

fof(f155,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v3_pre_topc(X0,sK2)
      | r2_hidden(X0,u1_pre_topc(sK2)) ) ),
    inference(subsumption_resolution,[],[f154,f86])).

fof(f154,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v3_pre_topc(X0,sK2)
      | r2_hidden(X0,u1_pre_topc(sK2))
      | ~ l1_pre_topc(sK2) ) ),
    inference(superposition,[],[f125,f87])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f291,plain,(
    m1_subset_1(sK6(sK0,sK2,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unit_resulting_resolution,[],[f78,f79,f80,f92,f96,f98,f129,f130,f186])).

fof(f186,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | m1_subset_1(sK6(X1,sK2,X0,X2),k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | r1_tmap_1(X1,sK2,X0,X2)
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(forward_demodulation,[],[f185,f87])).

fof(f185,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X1,sK2,X0,X2),k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | r1_tmap_1(X1,sK2,X0,X2)
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(forward_demodulation,[],[f184,f87])).

fof(f184,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | m1_subset_1(sK6(X1,sK2,X0,X2),k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | r1_tmap_1(X1,sK2,X0,X2)
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f183,f84])).

fof(f183,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | m1_subset_1(sK6(X1,sK2,X0,X2),k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | r1_tmap_1(X1,sK2,X0,X2)
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2))
      | ~ v1_funct_1(X0)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f182,f85])).

fof(f182,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | m1_subset_1(sK6(X1,sK2,X0,X2),k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | r1_tmap_1(X1,sK2,X0,X2)
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2))
      | ~ v1_funct_1(X0)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f176,f86])).

fof(f176,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | m1_subset_1(sK6(X1,sK2,X0,X2),k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | r1_tmap_1(X1,sK2,X0,X2)
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(superposition,[],[f103,f87])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | m1_subset_1(sK6(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_tmap_1(X0,X1,X2,X3)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f130,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(forward_demodulation,[],[f94,f87])).

fof(f94,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f65])).

fof(f129,plain,(
    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f93,f87])).

fof(f93,plain,(
    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f65])).

fof(f98,plain,(
    ~ r1_tmap_1(sK0,sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f65])).

fof(f92,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f65])).

fof(f219,plain,(
    v3_pre_topc(sK6(sK0,sK2,sK4,sK5),sK2) ),
    inference(unit_resulting_resolution,[],[f78,f79,f80,f92,f96,f98,f129,f130,f174])).

fof(f174,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
      | v3_pre_topc(sK6(X1,sK2,X0,X2),sK2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | r1_tmap_1(X1,sK2,X0,X2)
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(forward_demodulation,[],[f173,f87])).

fof(f173,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | v3_pre_topc(sK6(X1,sK2,X0,X2),sK2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | r1_tmap_1(X1,sK2,X0,X2)
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f172,f84])).

fof(f172,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | v3_pre_topc(sK6(X1,sK2,X0,X2),sK2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | r1_tmap_1(X1,sK2,X0,X2)
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2))
      | ~ v1_funct_1(X0)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f171,f85])).

fof(f171,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | v3_pre_topc(sK6(X1,sK2,X0,X2),sK2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | r1_tmap_1(X1,sK2,X0,X2)
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2))
      | ~ v1_funct_1(X0)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f165,f86])).

fof(f165,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | v3_pre_topc(sK6(X1,sK2,X0,X2),sK2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | r1_tmap_1(X1,sK2,X0,X2)
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(superposition,[],[f104,f87])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v3_pre_topc(sK6(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_tmap_1(X0,X1,X2,X3)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f432,plain,(
    sK3 = sK4 ),
    inference(unit_resulting_resolution,[],[f89,f92,f426,f129,f130,f131,f90,f91,f426,f107])).

fof(f107,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
      | X4 = X5
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
          | X4 != X5 )
        & ( X4 = X5
          | ~ r1_funct_2(X0,X1,X2,X3,X4,X5) ) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t50_tmap_1.p',redefinition_r1_funct_2)).

fof(f131,plain,(
    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) ),
    inference(forward_demodulation,[],[f95,f87])).

fof(f95,plain,(
    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),sK3,sK4) ),
    inference(cnf_transformation,[],[f65])).

fof(f426,plain,(
    ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(unit_resulting_resolution,[],[f291,f306,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t50_tmap_1.p',t5_subset)).

fof(f306,plain,(
    r2_hidden(k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK5),sK6(sK0,sK2,sK4,sK5)) ),
    inference(unit_resulting_resolution,[],[f78,f79,f80,f92,f96,f98,f129,f130,f199])).

fof(f199,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,X2),sK6(X0,sK2,X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
      | r1_tmap_1(X0,sK2,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f198,f87])).

fof(f198,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
      | r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,X2),sK6(X0,sK2,X1,X2))
      | r1_tmap_1(X0,sK2,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK2))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f197,f87])).

fof(f197,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,X2),sK6(X0,sK2,X1,X2))
      | r1_tmap_1(X0,sK2,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK2))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f196,f84])).

fof(f196,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,X2),sK6(X0,sK2,X1,X2))
      | r1_tmap_1(X0,sK2,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK2))
      | ~ v1_funct_1(X1)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f195,f85])).

fof(f195,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,X2),sK6(X0,sK2,X1,X2))
      | r1_tmap_1(X0,sK2,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK2))
      | ~ v1_funct_1(X1)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f188,f86])).

fof(f188,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,X2),sK6(X0,sK2,X1,X2))
      | r1_tmap_1(X0,sK2,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK2))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f105,f87])).

fof(f105,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),sK6(X0,X1,X2,X3))
      | r1_tmap_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f135,plain,(
    m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(u1_pre_topc(sK1))) ),
    inference(unit_resulting_resolution,[],[f88,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t50_tmap_1.p',t3_subset)).

fof(f88,plain,(
    r1_tarski(u1_pre_topc(sK2),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f65])).

fof(f315,plain,(
    ~ v1_xboole_0(u1_pre_topc(sK1)) ),
    inference(unit_resulting_resolution,[],[f135,f304,f118])).

fof(f460,plain,(
    r2_hidden(k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK5),sK6(sK0,sK2,sK3,sK5)) ),
    inference(backward_demodulation,[],[f432,f306])).

fof(f458,plain,(
    m1_subset_1(sK6(sK0,sK2,sK3,sK5),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(backward_demodulation,[],[f432,f291])).

fof(f97,plain,(
    r1_tmap_1(sK0,sK1,sK3,sK5) ),
    inference(cnf_transformation,[],[f65])).

fof(f96,plain,(
    m1_subset_1(sK5,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f65])).

fof(f83,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f65])).

fof(f82,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f65])).

fof(f81,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f65])).

fof(f550,plain,(
    v3_pre_topc(sK7(sK0,sK1,sK3,sK5,sK6(sK0,sK2,sK3,sK5)),sK0) ),
    inference(unit_resulting_resolution,[],[f78,f79,f80,f81,f82,f83,f89,f96,f97,f90,f91,f458,f460,f538,f100])).

fof(f100,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( ~ r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X6)
      | v3_pre_topc(sK7(X0,X1,X2,X3,X6),X0)
      | ~ v3_pre_topc(X6,X1)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_tmap_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f551,plain,(
    r2_hidden(sK5,sK7(sK0,sK1,sK3,sK5,sK6(sK0,sK2,sK3,sK5))) ),
    inference(unit_resulting_resolution,[],[f78,f79,f80,f81,f82,f83,f89,f96,f97,f90,f91,f458,f460,f538,f101])).

fof(f101,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( ~ r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X6)
      | r2_hidden(X3,sK7(X0,X1,X2,X3,X6))
      | ~ v3_pre_topc(X6,X1)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_tmap_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f91,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f65])).

fof(f90,plain,(
    v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f65])).

fof(f450,plain,(
    ~ r1_tmap_1(sK0,sK2,sK3,sK5) ),
    inference(backward_demodulation,[],[f432,f98])).

fof(f89,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f65])).

fof(f80,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f65])).

fof(f79,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f65])).

fof(f78,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f65])).

fof(f552,plain,(
    r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK7(sK0,sK1,sK3,sK5,sK6(sK0,sK2,sK3,sK5))),sK6(sK0,sK2,sK3,sK5)) ),
    inference(unit_resulting_resolution,[],[f78,f79,f80,f81,f82,f83,f89,f96,f97,f90,f91,f458,f460,f538,f102])).

fof(f102,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( ~ r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X6)
      | r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK7(X0,X1,X2,X3,X6)),X6)
      | ~ v3_pre_topc(X6,X1)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_tmap_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).
%------------------------------------------------------------------------------
