%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:06 EST 2020

% Result     : Theorem 15.33s
% Output     : CNFRefutation 15.33s
% Verified   : 
% Statistics : Number of formulae       :  245 (52945 expanded)
%              Number of clauses        :  183 (9761 expanded)
%              Number of leaves         :   15 (25617 expanded)
%              Depth                    :   35
%              Number of atoms          : 1927 (827677 expanded)
%              Number of equality atoms :  975 (76159 expanded)
%              Maximal formula depth    :   27 (   9 average)
%              Maximal clause size      :   38 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
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
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( ( r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
                                    & X5 = X6 )
                                 => r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
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
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X2))
                                 => ( ( r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
                                      & X5 = X6 )
                                   => r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6)
                              & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
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
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6)
                              & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
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
    inference(flattening,[],[f26])).

fof(f35,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ~ r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6)
          & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
          & X5 = X6
          & m1_subset_1(X6,u1_struct_0(X2)) )
     => ( ~ r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),sK6)
        & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
        & sK6 = X5
        & m1_subset_1(sK6,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ~ r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6)
              & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
              & X5 = X6
              & m1_subset_1(X6,u1_struct_0(X2)) )
          & m1_subset_1(X5,u1_struct_0(X3)) )
     => ( ? [X6] :
            ( ~ r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6)
            & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),sK5)
            & sK5 = X6
            & m1_subset_1(X6,u1_struct_0(X2)) )
        & m1_subset_1(sK5,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ~ r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6)
                  & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
                  & X5 = X6
                  & m1_subset_1(X6,u1_struct_0(X2)) )
              & m1_subset_1(X5,u1_struct_0(X3)) )
          & m1_pre_topc(X2,X3)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ~ r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,sK4,X2),X6)
                & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,sK4,X3),X5)
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(X2)) )
            & m1_subset_1(X5,u1_struct_0(X3)) )
        & m1_pre_topc(X2,X3)
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ~ r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6)
                      & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
                      & X5 = X6
                      & m1_subset_1(X6,u1_struct_0(X2)) )
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & m1_pre_topc(X2,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ~ r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6)
                    & r1_tmap_1(sK3,X1,k2_tmap_1(X0,X1,X4,sK3),X5)
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(X2)) )
                & m1_subset_1(X5,u1_struct_0(sK3)) )
            & m1_pre_topc(X2,sK3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ~ r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6)
                          & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
                          & X5 = X6
                          & m1_subset_1(X6,u1_struct_0(X2)) )
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & m1_pre_topc(X2,X3)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ~ r1_tmap_1(sK2,X1,k2_tmap_1(X0,X1,X4,sK2),X6)
                        & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(sK2)) )
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & m1_pre_topc(sK2,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6)
                              & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
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
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ~ r1_tmap_1(X2,sK1,k2_tmap_1(X0,sK1,X4,X2),X6)
                            & r1_tmap_1(X3,sK1,k2_tmap_1(X0,sK1,X4,X3),X5)
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & m1_pre_topc(X2,X3)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
                    & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ~ r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6)
                                & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
                                & X5 = X6
                                & m1_subset_1(X6,u1_struct_0(X2)) )
                            & m1_subset_1(X5,u1_struct_0(X3)) )
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
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X2,X1,k2_tmap_1(sK0,X1,X4,X2),X6)
                              & r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X4,X3),X5)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1))
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

fof(f36,plain,
    ( ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6)
    & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5)
    & sK5 = sK6
    & m1_subset_1(sK6,u1_struct_0(sK2))
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & m1_pre_topc(sK2,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f27,f35,f34,f33,f32,f31,f30,f29])).

fof(f65,plain,(
    r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) ),
    inference(cnf_transformation,[],[f36])).

fof(f64,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f36])).

fof(f57,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f60,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f36])).

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
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)
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
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)
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
    inference(flattening,[],[f15])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)
      | ~ m1_pre_topc(X3,X2)
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
    inference(cnf_transformation,[],[f16])).

fof(f51,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f52,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f53,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f58,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f59,plain,(
    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f2])).

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
    inference(flattening,[],[f13])).

fof(f39,plain,(
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
    inference(cnf_transformation,[],[f14])).

fof(f48,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f49,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f50,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f43,plain,(
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
    inference(cnf_transformation,[],[f18])).

fof(f55,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f42,plain,(
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
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
                      | ~ m1_pre_topc(X2,X3)
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
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
                      | ~ m1_pre_topc(X2,X3)
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
    inference(flattening,[],[f20])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
      | ~ m1_pre_topc(X2,X3)
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
    inference(cnf_transformation,[],[f21])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
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

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f54,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f41,plain,(
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
    inference(cnf_transformation,[],[f18])).

fof(f56,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f61,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
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
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( r1_tmap_1(X2,X1,X4,X5)
                                  & m1_pre_topc(X3,X2)
                                  & X5 = X6 )
                               => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(flattening,[],[f24])).

fof(f47,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
      | ~ r1_tmap_1(X2,X1,X4,X5)
      | ~ m1_pre_topc(X3,X2)
      | X5 != X6
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X2))
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
    inference(cnf_transformation,[],[f25])).

fof(f68,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
      | ~ r1_tmap_1(X2,X1,X4,X6)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
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
    inference(equality_resolution,[],[f47])).

fof(f62,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f36])).

fof(f66,plain,(
    ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6) ),
    inference(cnf_transformation,[],[f36])).

fof(f63,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_12,negated_conjecture,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_389,negated_conjecture,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_906,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_389])).

cnf(c_13,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_388,negated_conjecture,
    ( sK5 = sK6 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_924,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_906,c_388])).

cnf(c_20,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_381,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_913,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_381])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_384,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_910,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_384])).

cnf(c_3,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_398,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | ~ m1_pre_topc(X2_50,X3_50)
    | ~ m1_pre_topc(X2_50,X0_50)
    | ~ m1_pre_topc(X0_50,X3_50)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | v2_struct_0(X1_50)
    | v2_struct_0(X3_50)
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(X3_50)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(X3_50)
    | ~ v1_funct_1(X0_51)
    | k2_partfun1(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,u1_struct_0(X2_50)) = k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_51) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_897,plain,
    ( k2_partfun1(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,u1_struct_0(X2_50)) = k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_51)
    | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X0_50,X3_50) != iProver_top
    | m1_pre_topc(X2_50,X0_50) != iProver_top
    | m1_pre_topc(X2_50,X3_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X3_50) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X3_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X3_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_398])).

cnf(c_1857,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK0,X0_50,sK4)
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(X0_50,sK0) != iProver_top
    | m1_pre_topc(sK0,X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_910,c_897])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_33,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_34,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_35,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_40,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_41,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2068,plain,
    ( v2_pre_topc(X1_50) != iProver_top
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK0,X0_50,sK4)
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(X0_50,sK0) != iProver_top
    | m1_pre_topc(sK0,X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1857,c_33,c_34,c_35,c_40,c_41])).

cnf(c_2069,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK0,X0_50,sK4)
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(X0_50,sK0) != iProver_top
    | m1_pre_topc(sK0,X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_2068])).

cnf(c_2075,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4)
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_913,c_2069])).

cnf(c_2,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_399,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | ~ m1_pre_topc(X2_50,X0_50)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | v2_struct_0(X1_50)
    | v2_struct_0(X0_50)
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(X0_50)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(X0_50)
    | ~ v1_funct_1(X0_51)
    | k2_partfun1(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,u1_struct_0(X2_50)) = k2_tmap_1(X0_50,X1_50,X0_51,X2_50) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_896,plain,
    ( k2_partfun1(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,u1_struct_0(X2_50)) = k2_tmap_1(X0_50,X1_50,X0_51,X2_50)
    | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X2_50,X0_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_399])).

cnf(c_1571,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k2_tmap_1(sK0,sK1,sK4,X0_50)
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_50,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_910,c_896])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_30,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_31,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_32,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1749,plain,
    ( m1_pre_topc(X0_50,sK0) != iProver_top
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k2_tmap_1(sK0,sK1,sK4,X0_50) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1571,c_30,c_31,c_32,c_33,c_34,c_35,c_40,c_41])).

cnf(c_1750,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k2_tmap_1(sK0,sK1,sK4,X0_50)
    | m1_pre_topc(X0_50,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1749])).

cnf(c_1755,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
    inference(superposition,[status(thm)],[c_913,c_1750])).

cnf(c_2079,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK3,sK4) = k2_tmap_1(sK0,sK1,sK4,sK3)
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2075,c_1755])).

cnf(c_39,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_7,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_55,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_57,plain,
    ( m1_pre_topc(sK0,sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_55])).

cnf(c_2223,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK3,sK4) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2079,c_30,c_31,c_32,c_39,c_57])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_397,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | ~ m1_pre_topc(X2_50,X3_50)
    | ~ m1_pre_topc(X0_50,X3_50)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | m1_subset_1(k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50))))
    | v2_struct_0(X1_50)
    | v2_struct_0(X3_50)
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(X3_50)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(X3_50)
    | ~ v1_funct_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_898,plain,
    ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X0_50,X2_50) != iProver_top
    | m1_pre_topc(X3_50,X2_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50)))) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_397])).

cnf(c_2226,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2223,c_898])).

cnf(c_42,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2791,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2226,c_30,c_31,c_32,c_33,c_34,c_35,c_39,c_40,c_41,c_42,c_57])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_379,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_915,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_379])).

cnf(c_2076,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4)
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_915,c_2069])).

cnf(c_1756,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
    inference(superposition,[status(thm)],[c_915,c_1750])).

cnf(c_2078,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k2_tmap_1(sK0,sK1,sK4,sK2)
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2076,c_1756])).

cnf(c_37,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2137,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2078,c_30,c_31,c_32,c_37,c_57])).

cnf(c_2140,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2137,c_898])).

cnf(c_2544,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2140,c_30,c_31,c_32,c_33,c_34,c_35,c_37,c_40,c_41,c_42,c_57])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_396,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | v1_funct_2(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51),u1_struct_0(X3_50),u1_struct_0(X1_50))
    | ~ m1_pre_topc(X3_50,X2_50)
    | ~ m1_pre_topc(X0_50,X2_50)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | v2_struct_0(X1_50)
    | v2_struct_0(X2_50)
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(X2_50)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(X2_50)
    | ~ v1_funct_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_899,plain,
    ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51),u1_struct_0(X3_50),u1_struct_0(X1_50)) = iProver_top
    | m1_pre_topc(X0_50,X2_50) != iProver_top
    | m1_pre_topc(X3_50,X2_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_396])).

cnf(c_8,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,X3,X0,k2_tmap_1(X2,X1,X4,X3)),k2_tmap_1(X2,X1,X4,X0))
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_393,plain,
    ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k3_tmap_1(X2_50,X1_50,X3_50,X0_50,k2_tmap_1(X2_50,X1_50,X0_51,X3_50)),k2_tmap_1(X2_50,X1_50,X0_51,X0_50))
    | ~ v1_funct_2(X0_51,u1_struct_0(X2_50),u1_struct_0(X1_50))
    | ~ m1_pre_topc(X0_50,X3_50)
    | ~ m1_pre_topc(X3_50,X2_50)
    | ~ m1_pre_topc(X0_50,X2_50)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50))))
    | v2_struct_0(X1_50)
    | v2_struct_0(X0_50)
    | v2_struct_0(X3_50)
    | v2_struct_0(X2_50)
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(X2_50)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(X2_50)
    | ~ v1_funct_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_902,plain,
    ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k3_tmap_1(X2_50,X1_50,X3_50,X0_50,k2_tmap_1(X2_50,X1_50,X0_51,X3_50)),k2_tmap_1(X2_50,X1_50,X0_51,X0_50)) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X0_50,X2_50) != iProver_top
    | m1_pre_topc(X3_50,X2_50) != iProver_top
    | m1_pre_topc(X0_50,X3_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | v2_struct_0(X3_50) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_393])).

cnf(c_1,plain,
    ( ~ r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | X2 = X3 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_400,plain,
    ( ~ r2_funct_2(X0_52,X1_52,X0_51,X1_51)
    | ~ v1_funct_2(X1_51,X0_52,X1_52)
    | ~ v1_funct_2(X0_51,X0_52,X1_52)
    | ~ m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ v1_funct_1(X0_51)
    | ~ v1_funct_1(X1_51)
    | X0_51 = X1_51 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_895,plain,
    ( X0_51 = X1_51
    | r2_funct_2(X0_52,X1_52,X0_51,X1_51) != iProver_top
    | v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
    | v1_funct_2(X1_51,X0_52,X1_52) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_400])).

cnf(c_1945,plain,
    ( k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_51) = X1_51
    | r2_funct_2(u1_struct_0(X3_50),u1_struct_0(X1_50),k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_51),X1_51) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(X1_51,u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_51),u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X2_50,X0_50) != iProver_top
    | m1_pre_topc(X3_50,X0_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_51)) != iProver_top ),
    inference(superposition,[status(thm)],[c_898,c_895])).

cnf(c_4359,plain,
    ( k3_tmap_1(X0_50,X1_50,X2_50,X3_50,k2_tmap_1(X0_50,X1_50,X0_51,X2_50)) = k2_tmap_1(X0_50,X1_50,X0_51,X3_50)
    | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_50,X1_50,X2_50,X3_50,k2_tmap_1(X0_50,X1_50,X0_51,X2_50)),u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(k2_tmap_1(X0_50,X1_50,X0_51,X2_50),u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(k2_tmap_1(X0_50,X1_50,X0_51,X3_50),u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X2_50,X0_50) != iProver_top
    | m1_pre_topc(X3_50,X0_50) != iProver_top
    | m1_pre_topc(X3_50,X2_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(k2_tmap_1(X0_50,X1_50,X0_51,X2_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(k2_tmap_1(X0_50,X1_50,X0_51,X3_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X3_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_50,X1_50,X2_50,X3_50,k2_tmap_1(X0_50,X1_50,X0_51,X2_50))) != iProver_top
    | v1_funct_1(k2_tmap_1(X0_50,X1_50,X0_51,X2_50)) != iProver_top
    | v1_funct_1(k2_tmap_1(X0_50,X1_50,X0_51,X3_50)) != iProver_top ),
    inference(superposition,[status(thm)],[c_902,c_1945])).

cnf(c_8105,plain,
    ( k3_tmap_1(X0_50,X1_50,X2_50,X3_50,k2_tmap_1(X0_50,X1_50,X0_51,X2_50)) = k2_tmap_1(X0_50,X1_50,X0_51,X3_50)
    | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(k2_tmap_1(X0_50,X1_50,X0_51,X3_50),u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(k2_tmap_1(X0_50,X1_50,X0_51,X2_50),u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X3_50,X2_50) != iProver_top
    | m1_pre_topc(X3_50,X0_50) != iProver_top
    | m1_pre_topc(X2_50,X0_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(k2_tmap_1(X0_50,X1_50,X0_51,X3_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(k2_tmap_1(X0_50,X1_50,X0_51,X2_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | v2_struct_0(X3_50) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_50,X1_50,X2_50,X3_50,k2_tmap_1(X0_50,X1_50,X0_51,X2_50))) != iProver_top
    | v1_funct_1(k2_tmap_1(X0_50,X1_50,X0_51,X3_50)) != iProver_top
    | v1_funct_1(k2_tmap_1(X0_50,X1_50,X0_51,X2_50)) != iProver_top ),
    inference(superposition,[status(thm)],[c_899,c_4359])).

cnf(c_21644,plain,
    ( k3_tmap_1(sK0,sK1,X0_50,sK2,k2_tmap_1(sK0,sK1,sK4,X0_50)) = k2_tmap_1(sK0,sK1,sK4,sK2)
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,X0_50),u1_struct_0(X0_50),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_50,sK0) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,X0_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,X0_50,sK2,k2_tmap_1(sK0,sK1,sK4,X0_50))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,X0_50)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2544,c_8105])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_36,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2141,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2137,c_899])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_395,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | ~ m1_pre_topc(X2_50,X3_50)
    | ~ m1_pre_topc(X0_50,X3_50)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | v2_struct_0(X1_50)
    | v2_struct_0(X3_50)
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(X3_50)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(X3_50)
    | ~ v1_funct_1(X0_51)
    | v1_funct_1(k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_51)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_900,plain,
    ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X0_50,X2_50) != iProver_top
    | m1_pre_topc(X3_50,X2_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_395])).

cnf(c_1576,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(sK0,X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_50,sK1,sK0,X0_50,sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_910,c_900])).

cnf(c_2061,plain,
    ( v1_funct_1(k3_tmap_1(X1_50,sK1,sK0,X0_50,sK4)) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(sK0,X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1576,c_33,c_34,c_35,c_40,c_41])).

cnf(c_2062,plain,
    ( m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(sK0,X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_50,sK1,sK0,X0_50,sK4)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2061])).

cnf(c_2142,plain,
    ( m1_pre_topc(sK0,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2137,c_2062])).

cnf(c_41468,plain,
    ( v2_struct_0(X0_50) = iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | m1_pre_topc(X0_50,sK0) != iProver_top
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,X0_50),u1_struct_0(X0_50),u1_struct_0(sK1)) != iProver_top
    | k3_tmap_1(sK0,sK1,X0_50,sK2,k2_tmap_1(sK0,sK1,sK4,X0_50)) = k2_tmap_1(sK0,sK1,sK4,sK2)
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,X0_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,X0_50,sK2,k2_tmap_1(sK0,sK1,sK4,X0_50))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,X0_50)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21644,c_30,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_40,c_41,c_42,c_57,c_2141,c_2142])).

cnf(c_41469,plain,
    ( k3_tmap_1(sK0,sK1,X0_50,sK2,k2_tmap_1(sK0,sK1,sK4,X0_50)) = k2_tmap_1(sK0,sK1,sK4,sK2)
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,X0_50),u1_struct_0(X0_50),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_50,sK0) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,X0_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,X0_50,sK2,k2_tmap_1(sK0,sK1,sK4,X0_50))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,X0_50)) != iProver_top ),
    inference(renaming,[status(thm)],[c_41468])).

cnf(c_41472,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) = k2_tmap_1(sK0,sK1,sK4,sK2)
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2791,c_41469])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_38,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_16,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_43,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2227,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2223,c_899])).

cnf(c_2228,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2223,c_2062])).

cnf(c_999,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(sK1))
    | ~ m1_pre_topc(X1_50,X2_50)
    | ~ m1_pre_topc(X0_50,X2_50)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(sK1))))
    | v2_struct_0(X2_50)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(X2_50)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X2_50)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0_51)
    | v1_funct_1(k3_tmap_1(X2_50,sK1,X0_50,X1_50,X0_51)) ),
    inference(instantiation,[status(thm)],[c_395])).

cnf(c_3420,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,X0_50)
    | ~ m1_pre_topc(sK2,X0_50)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(X0_50)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(X0_50)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X0_50)
    | ~ l1_pre_topc(sK1)
    | v1_funct_1(k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_999])).

cnf(c_3421,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK3,X0_50) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))) = iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3420])).

cnf(c_3423,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))) = iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3421])).

cnf(c_997,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(sK1))
    | v1_funct_2(k3_tmap_1(X1_50,sK1,X0_50,X2_50,X0_51),u1_struct_0(X2_50),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_50,X1_50)
    | ~ m1_pre_topc(X2_50,X1_50)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(sK1))))
    | v2_struct_0(X1_50)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0_51) ),
    inference(instantiation,[status(thm)],[c_396])).

cnf(c_6547,plain,
    ( v1_funct_2(k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,X0_50)
    | ~ m1_pre_topc(sK2,X0_50)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(X0_50)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(X0_50)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X0_50)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_997])).

cnf(c_6552,plain,
    ( v1_funct_2(k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK3,X0_50) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6547])).

cnf(c_6554,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6552])).

cnf(c_996,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(sK1))
    | ~ m1_pre_topc(X1_50,X2_50)
    | ~ m1_pre_topc(X0_50,X2_50)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(sK1))))
    | m1_subset_1(k3_tmap_1(X2_50,sK1,X0_50,X1_50,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(sK1))))
    | v2_struct_0(X2_50)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(X2_50)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X2_50)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0_51) ),
    inference(instantiation,[status(thm)],[c_397])).

cnf(c_12267,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,X0_50)
    | ~ m1_pre_topc(sK2,X0_50)
    | m1_subset_1(k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(X0_50)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(X0_50)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X0_50)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_996])).

cnf(c_12268,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK3,X0_50) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | m1_subset_1(k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12267])).

cnf(c_12270,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_12268])).

cnf(c_3239,plain,
    ( ~ r2_funct_2(X0_52,X1_52,k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),X0_51)
    | ~ v1_funct_2(X0_51,X0_52,X1_52)
    | ~ v1_funct_2(k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),X0_52,X1_52)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ m1_subset_1(k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ v1_funct_1(X0_51)
    | ~ v1_funct_1(k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)))
    | k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) = X0_51 ),
    inference(instantiation,[status(thm)],[c_400])).

cnf(c_8190,plain,
    ( ~ r2_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k3_tmap_1(X1_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),X0_51)
    | ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(sK1))
    | ~ v1_funct_2(k3_tmap_1(X1_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(X0_50),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(sK1))))
    | ~ m1_subset_1(k3_tmap_1(X1_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_51)
    | ~ v1_funct_1(k3_tmap_1(X1_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)))
    | k3_tmap_1(X1_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) = X0_51 ),
    inference(instantiation,[status(thm)],[c_3239])).

cnf(c_10897,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),X0_51)
    | ~ v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_subset_1(k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_51)
    | ~ v1_funct_1(k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)))
    | k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) = X0_51 ),
    inference(instantiation,[status(thm)],[c_8190])).

cnf(c_13522,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ v1_funct_2(k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))
    | k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
    inference(instantiation,[status(thm)],[c_10897])).

cnf(c_13536,plain,
    ( k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) = k2_tmap_1(sK0,sK1,sK4,sK2)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13522])).

cnf(c_13538,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) = k2_tmap_1(sK0,sK1,sK4,sK2)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_13536])).

cnf(c_394,plain,
    ( m1_pre_topc(X0_50,X0_50)
    | ~ l1_pre_topc(X0_50) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_901,plain,
    ( m1_pre_topc(X0_50,X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_394])).

cnf(c_2077,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k3_tmap_1(X0_50,sK1,sK0,X0_50,sK4)
    | m1_pre_topc(X0_50,sK0) != iProver_top
    | m1_pre_topc(sK0,X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_901,c_2069])).

cnf(c_2394,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK0)) = k3_tmap_1(sK0,sK1,sK0,sK0,sK4)
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_901,c_2077])).

cnf(c_1757,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK0)) = k2_tmap_1(sK0,sK1,sK4,sK0)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_901,c_1750])).

cnf(c_56,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_998,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(sK1))
    | ~ m1_pre_topc(X1_50,X0_50)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(sK1))))
    | v2_struct_0(X0_50)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(X0_50)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X0_50)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0_51)
    | k2_partfun1(u1_struct_0(X0_50),u1_struct_0(sK1),X0_51,u1_struct_0(X1_50)) = k2_tmap_1(X0_50,sK1,X0_51,X1_50) ),
    inference(instantiation,[status(thm)],[c_399])).

cnf(c_1005,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK4)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK0)) = k2_tmap_1(sK0,sK1,sK4,sK0) ),
    inference(instantiation,[status(thm)],[c_998])).

cnf(c_2134,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK0)) = k2_tmap_1(sK0,sK1,sK4,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1757,c_29,c_28,c_27,c_26,c_25,c_24,c_19,c_18,c_17,c_56,c_1005])).

cnf(c_2395,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK0,sK4) = k2_tmap_1(sK0,sK1,sK4,sK0)
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2394,c_2134])).

cnf(c_2694,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK0,sK4) = k2_tmap_1(sK0,sK1,sK4,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2395,c_30,c_31,c_32,c_57])).

cnf(c_2697,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2694,c_898])).

cnf(c_4609,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2697,c_30,c_31,c_32,c_33,c_34,c_35,c_40,c_41,c_42,c_57])).

cnf(c_4613,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK0),u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK0,X0_50,k2_tmap_1(sK0,sK1,sK4,sK0))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK0),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(X0_50,sK0) != iProver_top
    | m1_pre_topc(sK0,X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4609,c_897])).

cnf(c_2698,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK0),u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2694,c_899])).

cnf(c_2699,plain,
    ( m1_pre_topc(sK0,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2694,c_2062])).

cnf(c_5678,plain,
    ( v2_pre_topc(X1_50) != iProver_top
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK0),u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK0,X0_50,k2_tmap_1(sK0,sK1,sK4,sK0))
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(X0_50,sK0) != iProver_top
    | m1_pre_topc(sK0,X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4613,c_30,c_31,c_32,c_33,c_34,c_35,c_40,c_41,c_42,c_57,c_2698,c_2699])).

cnf(c_5679,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK0),u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK0,X0_50,k2_tmap_1(sK0,sK1,sK4,sK0))
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(X0_50,sK0) != iProver_top
    | m1_pre_topc(sK0,X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_5678])).

cnf(c_5685,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK0),u1_struct_0(sK3)) = k3_tmap_1(sK0,sK1,sK0,sK3,k2_tmap_1(sK0,sK1,sK4,sK0))
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_913,c_5679])).

cnf(c_4615,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK0),u1_struct_0(X0_50)) = k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),X0_50)
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK0),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_50,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4609,c_896])).

cnf(c_5150,plain,
    ( m1_pre_topc(X0_50,sK0) != iProver_top
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK0),u1_struct_0(X0_50)) = k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),X0_50) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4615,c_30,c_31,c_32,c_33,c_34,c_35,c_40,c_41,c_42,c_57,c_2698,c_2699])).

cnf(c_5151,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK0),u1_struct_0(X0_50)) = k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),X0_50)
    | m1_pre_topc(X0_50,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5150])).

cnf(c_5156,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK0),u1_struct_0(sK3)) = k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),sK3) ),
    inference(superposition,[status(thm)],[c_913,c_5151])).

cnf(c_5689,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK3,k2_tmap_1(sK0,sK1,sK4,sK0)) = k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),sK3)
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5685,c_5156])).

cnf(c_6595,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK3,k2_tmap_1(sK0,sK1,sK4,sK0)) = k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5689,c_30,c_31,c_32,c_39,c_57])).

cnf(c_8106,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK3,k2_tmap_1(sK0,sK1,sK4,sK0)) = k2_tmap_1(sK0,sK1,sK4,sK3)
    | v1_funct_2(k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK0),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,k2_tmap_1(sK0,sK1,sK4,sK0))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6595,c_4359])).

cnf(c_8269,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK3,k2_tmap_1(sK0,sK1,sK4,sK0)) = k2_tmap_1(sK0,sK1,sK4,sK3)
    | v1_funct_2(k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK0),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),sK3)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8106,c_6595])).

cnf(c_8270,plain,
    ( k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),sK3) = k2_tmap_1(sK0,sK1,sK4,sK3)
    | v1_funct_2(k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK0),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),sK3)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8269,c_6595])).

cnf(c_6601,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),sK3),u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK0),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6595,c_899])).

cnf(c_4614,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK0),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(sK0,X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_50,sK1,sK0,X0_50,k2_tmap_1(sK0,sK1,sK4,sK0))) = iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4609,c_900])).

cnf(c_1943,plain,
    ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51),u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X0_50,X2_50) != iProver_top
    | m1_pre_topc(X3_50,X2_50) != iProver_top
    | m1_pre_topc(X3_50,X4_50) != iProver_top
    | m1_pre_topc(X5_50,X4_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X4_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top
    | v2_pre_topc(X4_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | l1_pre_topc(X4_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51)) != iProver_top
    | v1_funct_1(k3_tmap_1(X4_50,X1_50,X3_50,X5_50,k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51))) = iProver_top ),
    inference(superposition,[status(thm)],[c_898,c_900])).

cnf(c_434,plain,
    ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51),u1_struct_0(X3_50),u1_struct_0(X1_50)) = iProver_top
    | m1_pre_topc(X0_50,X2_50) != iProver_top
    | m1_pre_topc(X3_50,X2_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_396])).

cnf(c_437,plain,
    ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X0_50,X2_50) != iProver_top
    | m1_pre_topc(X3_50,X2_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_395])).

cnf(c_3054,plain,
    ( v1_funct_1(X0_51) != iProver_top
    | l1_pre_topc(X4_50) != iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X4_50) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | v2_struct_0(X4_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_pre_topc(X5_50,X4_50) != iProver_top
    | m1_pre_topc(X3_50,X4_50) != iProver_top
    | m1_pre_topc(X3_50,X2_50) != iProver_top
    | m1_pre_topc(X0_50,X2_50) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_1(k3_tmap_1(X4_50,X1_50,X3_50,X5_50,k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1943,c_434,c_437])).

cnf(c_3055,plain,
    ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X0_50,X2_50) != iProver_top
    | m1_pre_topc(X3_50,X2_50) != iProver_top
    | m1_pre_topc(X3_50,X4_50) != iProver_top
    | m1_pre_topc(X5_50,X4_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X4_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top
    | v2_pre_topc(X4_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | l1_pre_topc(X4_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(k3_tmap_1(X4_50,X1_50,X3_50,X5_50,k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51))) = iProver_top ),
    inference(renaming,[status(thm)],[c_3054])).

cnf(c_3060,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(sK0,X1_50) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_50,sK1,sK0,X0_50,k2_tmap_1(sK0,sK1,sK4,sK0))) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2694,c_3055])).

cnf(c_5143,plain,
    ( v1_funct_1(k3_tmap_1(X1_50,sK1,sK0,X0_50,k2_tmap_1(sK0,sK1,sK4,sK0))) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(sK0,X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4614,c_30,c_31,c_32,c_33,c_34,c_35,c_40,c_41,c_42,c_57,c_3060])).

cnf(c_5144,plain,
    ( m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(sK0,X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_50,sK1,sK0,X0_50,k2_tmap_1(sK0,sK1,sK4,sK0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_5143])).

cnf(c_6605,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6595,c_5144])).

cnf(c_9276,plain,
    ( k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),sK3) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8270,c_30,c_31,c_32,c_33,c_34,c_35,c_38,c_39,c_40,c_41,c_42,c_57,c_2226,c_2227,c_2228,c_2697,c_2698,c_2699,c_6601,c_6605])).

cnf(c_5686,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK0),u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK0,sK2,k2_tmap_1(sK0,sK1,sK4,sK0))
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_915,c_5679])).

cnf(c_5157,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK0),u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),sK2) ),
    inference(superposition,[status(thm)],[c_915,c_5151])).

cnf(c_5688,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK2,k2_tmap_1(sK0,sK1,sK4,sK0)) = k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),sK2)
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5686,c_5157])).

cnf(c_6459,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK2,k2_tmap_1(sK0,sK1,sK4,sK0)) = k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5688,c_30,c_31,c_32,c_37,c_57])).

cnf(c_8107,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK2,k2_tmap_1(sK0,sK1,sK4,sK0)) = k2_tmap_1(sK0,sK1,sK4,sK2)
    | v1_funct_2(k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK0),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k2_tmap_1(sK0,sK1,sK4,sK0))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK0)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6459,c_4359])).

cnf(c_8267,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK2,k2_tmap_1(sK0,sK1,sK4,sK0)) = k2_tmap_1(sK0,sK1,sK4,sK2)
    | v1_funct_2(k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK0),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),sK2)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK0)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8107,c_6459])).

cnf(c_8268,plain,
    ( k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),sK2) = k2_tmap_1(sK0,sK1,sK4,sK2)
    | v1_funct_2(k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK0),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),sK2)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK0)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8267,c_6459])).

cnf(c_6465,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK0),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6459,c_899])).

cnf(c_6469,plain,
    ( m1_pre_topc(sK0,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6459,c_5144])).

cnf(c_9082,plain,
    ( k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),sK2) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8268,c_30,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_40,c_41,c_42,c_57,c_2140,c_2141,c_2142,c_2697,c_2698,c_2699,c_6465,c_6469])).

cnf(c_9100,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0_50,sK2,k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),X0_50)),k2_tmap_1(sK0,sK1,sK4,sK2)) = iProver_top
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK0),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_50,sK0) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9082,c_902])).

cnf(c_30344,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0_50,sK2,k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),X0_50)),k2_tmap_1(sK0,sK1,sK4,sK2)) = iProver_top
    | m1_pre_topc(X0_50,sK0) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9100,c_30,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_40,c_41,c_42,c_57,c_2697,c_2698,c_2699])).

cnf(c_30351,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2)) = iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_9276,c_30344])).

cnf(c_41478,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_41472,c_30,c_31,c_32,c_33,c_34,c_35,c_37,c_38,c_39,c_40,c_41,c_42,c_43,c_57,c_2140,c_2141,c_2142,c_2226,c_2227,c_2228,c_3423,c_6554,c_12270,c_13538,c_30351])).

cnf(c_10,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_391,plain,
    ( ~ r1_tmap_1(X0_50,X1_50,X0_51,X1_51)
    | r1_tmap_1(X2_50,X1_50,k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_51),X1_51)
    | ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | ~ m1_pre_topc(X2_50,X3_50)
    | ~ m1_pre_topc(X2_50,X0_50)
    | ~ m1_pre_topc(X0_50,X3_50)
    | ~ m1_subset_1(X1_51,u1_struct_0(X2_50))
    | ~ m1_subset_1(X1_51,u1_struct_0(X0_50))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | v2_struct_0(X1_50)
    | v2_struct_0(X0_50)
    | v2_struct_0(X3_50)
    | v2_struct_0(X2_50)
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(X3_50)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(X3_50)
    | ~ v1_funct_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_904,plain,
    ( r1_tmap_1(X0_50,X1_50,X0_51,X1_51) != iProver_top
    | r1_tmap_1(X2_50,X1_50,k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_51),X1_51) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X0_50,X3_50) != iProver_top
    | m1_pre_topc(X2_50,X0_50) != iProver_top
    | m1_pre_topc(X2_50,X3_50) != iProver_top
    | m1_subset_1(X1_51,u1_struct_0(X2_50)) != iProver_top
    | m1_subset_1(X1_51,u1_struct_0(X0_50)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | v2_struct_0(X3_50) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X3_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X3_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_391])).

cnf(c_41498,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0_51) != iProver_top
    | r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),X0_51) = iProver_top
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_41478,c_904])).

cnf(c_42936,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0_51) != iProver_top
    | r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),X0_51) = iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_41498,c_30,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_43,c_57,c_2226,c_2227,c_2228])).

cnf(c_42942,plain,
    ( r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_924,c_42936])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_386,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_908,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_386])).

cnf(c_923,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_908,c_388])).

cnf(c_11,negated_conjecture,
    ( ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_47,plain,
    ( r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_45,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_42942,c_923,c_47,c_45])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:40:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 15.33/2.52  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.33/2.52  
% 15.33/2.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.33/2.52  
% 15.33/2.52  ------  iProver source info
% 15.33/2.52  
% 15.33/2.52  git: date: 2020-06-30 10:37:57 +0100
% 15.33/2.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.33/2.52  git: non_committed_changes: false
% 15.33/2.52  git: last_make_outside_of_git: false
% 15.33/2.52  
% 15.33/2.52  ------ 
% 15.33/2.52  
% 15.33/2.52  ------ Input Options
% 15.33/2.52  
% 15.33/2.52  --out_options                           all
% 15.33/2.52  --tptp_safe_out                         true
% 15.33/2.52  --problem_path                          ""
% 15.33/2.52  --include_path                          ""
% 15.33/2.52  --clausifier                            res/vclausify_rel
% 15.33/2.52  --clausifier_options                    ""
% 15.33/2.52  --stdin                                 false
% 15.33/2.52  --stats_out                             all
% 15.33/2.52  
% 15.33/2.52  ------ General Options
% 15.33/2.52  
% 15.33/2.52  --fof                                   false
% 15.33/2.52  --time_out_real                         305.
% 15.33/2.52  --time_out_virtual                      -1.
% 15.33/2.52  --symbol_type_check                     false
% 15.33/2.52  --clausify_out                          false
% 15.33/2.52  --sig_cnt_out                           false
% 15.33/2.52  --trig_cnt_out                          false
% 15.33/2.52  --trig_cnt_out_tolerance                1.
% 15.33/2.52  --trig_cnt_out_sk_spl                   false
% 15.33/2.52  --abstr_cl_out                          false
% 15.33/2.52  
% 15.33/2.52  ------ Global Options
% 15.33/2.52  
% 15.33/2.52  --schedule                              default
% 15.33/2.52  --add_important_lit                     false
% 15.33/2.52  --prop_solver_per_cl                    1000
% 15.33/2.52  --min_unsat_core                        false
% 15.33/2.52  --soft_assumptions                      false
% 15.33/2.52  --soft_lemma_size                       3
% 15.33/2.52  --prop_impl_unit_size                   0
% 15.33/2.52  --prop_impl_unit                        []
% 15.33/2.52  --share_sel_clauses                     true
% 15.33/2.52  --reset_solvers                         false
% 15.33/2.52  --bc_imp_inh                            [conj_cone]
% 15.33/2.52  --conj_cone_tolerance                   3.
% 15.33/2.52  --extra_neg_conj                        none
% 15.33/2.52  --large_theory_mode                     true
% 15.33/2.52  --prolific_symb_bound                   200
% 15.33/2.52  --lt_threshold                          2000
% 15.33/2.52  --clause_weak_htbl                      true
% 15.33/2.52  --gc_record_bc_elim                     false
% 15.33/2.52  
% 15.33/2.52  ------ Preprocessing Options
% 15.33/2.52  
% 15.33/2.52  --preprocessing_flag                    true
% 15.33/2.52  --time_out_prep_mult                    0.1
% 15.33/2.52  --splitting_mode                        input
% 15.33/2.52  --splitting_grd                         true
% 15.33/2.52  --splitting_cvd                         false
% 15.33/2.52  --splitting_cvd_svl                     false
% 15.33/2.52  --splitting_nvd                         32
% 15.33/2.52  --sub_typing                            true
% 15.33/2.52  --prep_gs_sim                           true
% 15.33/2.52  --prep_unflatten                        true
% 15.33/2.52  --prep_res_sim                          true
% 15.33/2.52  --prep_upred                            true
% 15.33/2.52  --prep_sem_filter                       exhaustive
% 15.33/2.52  --prep_sem_filter_out                   false
% 15.33/2.52  --pred_elim                             true
% 15.33/2.52  --res_sim_input                         true
% 15.33/2.52  --eq_ax_congr_red                       true
% 15.33/2.52  --pure_diseq_elim                       true
% 15.33/2.52  --brand_transform                       false
% 15.33/2.52  --non_eq_to_eq                          false
% 15.33/2.52  --prep_def_merge                        true
% 15.33/2.52  --prep_def_merge_prop_impl              false
% 15.33/2.52  --prep_def_merge_mbd                    true
% 15.33/2.52  --prep_def_merge_tr_red                 false
% 15.33/2.52  --prep_def_merge_tr_cl                  false
% 15.33/2.52  --smt_preprocessing                     true
% 15.33/2.52  --smt_ac_axioms                         fast
% 15.33/2.52  --preprocessed_out                      false
% 15.33/2.52  --preprocessed_stats                    false
% 15.33/2.52  
% 15.33/2.52  ------ Abstraction refinement Options
% 15.33/2.52  
% 15.33/2.52  --abstr_ref                             []
% 15.33/2.52  --abstr_ref_prep                        false
% 15.33/2.52  --abstr_ref_until_sat                   false
% 15.33/2.52  --abstr_ref_sig_restrict                funpre
% 15.33/2.52  --abstr_ref_af_restrict_to_split_sk     false
% 15.33/2.52  --abstr_ref_under                       []
% 15.33/2.52  
% 15.33/2.52  ------ SAT Options
% 15.33/2.52  
% 15.33/2.52  --sat_mode                              false
% 15.33/2.52  --sat_fm_restart_options                ""
% 15.33/2.52  --sat_gr_def                            false
% 15.33/2.52  --sat_epr_types                         true
% 15.33/2.52  --sat_non_cyclic_types                  false
% 15.33/2.52  --sat_finite_models                     false
% 15.33/2.52  --sat_fm_lemmas                         false
% 15.33/2.52  --sat_fm_prep                           false
% 15.33/2.52  --sat_fm_uc_incr                        true
% 15.33/2.52  --sat_out_model                         small
% 15.33/2.52  --sat_out_clauses                       false
% 15.33/2.52  
% 15.33/2.52  ------ QBF Options
% 15.33/2.52  
% 15.33/2.52  --qbf_mode                              false
% 15.33/2.52  --qbf_elim_univ                         false
% 15.33/2.52  --qbf_dom_inst                          none
% 15.33/2.52  --qbf_dom_pre_inst                      false
% 15.33/2.52  --qbf_sk_in                             false
% 15.33/2.52  --qbf_pred_elim                         true
% 15.33/2.52  --qbf_split                             512
% 15.33/2.52  
% 15.33/2.52  ------ BMC1 Options
% 15.33/2.52  
% 15.33/2.52  --bmc1_incremental                      false
% 15.33/2.52  --bmc1_axioms                           reachable_all
% 15.33/2.52  --bmc1_min_bound                        0
% 15.33/2.52  --bmc1_max_bound                        -1
% 15.33/2.52  --bmc1_max_bound_default                -1
% 15.33/2.52  --bmc1_symbol_reachability              true
% 15.33/2.52  --bmc1_property_lemmas                  false
% 15.33/2.52  --bmc1_k_induction                      false
% 15.33/2.52  --bmc1_non_equiv_states                 false
% 15.33/2.52  --bmc1_deadlock                         false
% 15.33/2.52  --bmc1_ucm                              false
% 15.33/2.52  --bmc1_add_unsat_core                   none
% 15.33/2.52  --bmc1_unsat_core_children              false
% 15.33/2.52  --bmc1_unsat_core_extrapolate_axioms    false
% 15.33/2.52  --bmc1_out_stat                         full
% 15.33/2.52  --bmc1_ground_init                      false
% 15.33/2.52  --bmc1_pre_inst_next_state              false
% 15.33/2.52  --bmc1_pre_inst_state                   false
% 15.33/2.52  --bmc1_pre_inst_reach_state             false
% 15.33/2.52  --bmc1_out_unsat_core                   false
% 15.33/2.52  --bmc1_aig_witness_out                  false
% 15.33/2.52  --bmc1_verbose                          false
% 15.33/2.52  --bmc1_dump_clauses_tptp                false
% 15.33/2.52  --bmc1_dump_unsat_core_tptp             false
% 15.33/2.52  --bmc1_dump_file                        -
% 15.33/2.52  --bmc1_ucm_expand_uc_limit              128
% 15.33/2.52  --bmc1_ucm_n_expand_iterations          6
% 15.33/2.52  --bmc1_ucm_extend_mode                  1
% 15.33/2.52  --bmc1_ucm_init_mode                    2
% 15.33/2.52  --bmc1_ucm_cone_mode                    none
% 15.33/2.52  --bmc1_ucm_reduced_relation_type        0
% 15.33/2.52  --bmc1_ucm_relax_model                  4
% 15.33/2.52  --bmc1_ucm_full_tr_after_sat            true
% 15.33/2.52  --bmc1_ucm_expand_neg_assumptions       false
% 15.33/2.52  --bmc1_ucm_layered_model                none
% 15.33/2.52  --bmc1_ucm_max_lemma_size               10
% 15.33/2.52  
% 15.33/2.52  ------ AIG Options
% 15.33/2.52  
% 15.33/2.52  --aig_mode                              false
% 15.33/2.52  
% 15.33/2.52  ------ Instantiation Options
% 15.33/2.52  
% 15.33/2.52  --instantiation_flag                    true
% 15.33/2.52  --inst_sos_flag                         true
% 15.33/2.52  --inst_sos_phase                        true
% 15.33/2.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.33/2.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.33/2.52  --inst_lit_sel_side                     num_symb
% 15.33/2.52  --inst_solver_per_active                1400
% 15.33/2.52  --inst_solver_calls_frac                1.
% 15.33/2.52  --inst_passive_queue_type               priority_queues
% 15.33/2.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.33/2.52  --inst_passive_queues_freq              [25;2]
% 15.33/2.52  --inst_dismatching                      true
% 15.33/2.52  --inst_eager_unprocessed_to_passive     true
% 15.33/2.52  --inst_prop_sim_given                   true
% 15.33/2.52  --inst_prop_sim_new                     false
% 15.33/2.52  --inst_subs_new                         false
% 15.33/2.52  --inst_eq_res_simp                      false
% 15.33/2.52  --inst_subs_given                       false
% 15.33/2.52  --inst_orphan_elimination               true
% 15.33/2.52  --inst_learning_loop_flag               true
% 15.33/2.52  --inst_learning_start                   3000
% 15.33/2.52  --inst_learning_factor                  2
% 15.33/2.52  --inst_start_prop_sim_after_learn       3
% 15.33/2.52  --inst_sel_renew                        solver
% 15.33/2.52  --inst_lit_activity_flag                true
% 15.33/2.52  --inst_restr_to_given                   false
% 15.33/2.52  --inst_activity_threshold               500
% 15.33/2.52  --inst_out_proof                        true
% 15.33/2.52  
% 15.33/2.52  ------ Resolution Options
% 15.33/2.52  
% 15.33/2.52  --resolution_flag                       true
% 15.33/2.52  --res_lit_sel                           adaptive
% 15.33/2.52  --res_lit_sel_side                      none
% 15.33/2.52  --res_ordering                          kbo
% 15.33/2.52  --res_to_prop_solver                    active
% 15.33/2.52  --res_prop_simpl_new                    false
% 15.33/2.52  --res_prop_simpl_given                  true
% 15.33/2.52  --res_passive_queue_type                priority_queues
% 15.33/2.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.33/2.52  --res_passive_queues_freq               [15;5]
% 15.33/2.52  --res_forward_subs                      full
% 15.33/2.52  --res_backward_subs                     full
% 15.33/2.52  --res_forward_subs_resolution           true
% 15.33/2.52  --res_backward_subs_resolution          true
% 15.33/2.52  --res_orphan_elimination                true
% 15.33/2.52  --res_time_limit                        2.
% 15.33/2.52  --res_out_proof                         true
% 15.33/2.52  
% 15.33/2.52  ------ Superposition Options
% 15.33/2.52  
% 15.33/2.52  --superposition_flag                    true
% 15.33/2.52  --sup_passive_queue_type                priority_queues
% 15.33/2.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.33/2.52  --sup_passive_queues_freq               [8;1;4]
% 15.33/2.52  --demod_completeness_check              fast
% 15.33/2.52  --demod_use_ground                      true
% 15.33/2.52  --sup_to_prop_solver                    passive
% 15.33/2.52  --sup_prop_simpl_new                    true
% 15.33/2.52  --sup_prop_simpl_given                  true
% 15.33/2.52  --sup_fun_splitting                     true
% 15.33/2.52  --sup_smt_interval                      50000
% 15.33/2.52  
% 15.33/2.52  ------ Superposition Simplification Setup
% 15.33/2.52  
% 15.33/2.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.33/2.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.33/2.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.33/2.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.33/2.52  --sup_full_triv                         [TrivRules;PropSubs]
% 15.33/2.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.33/2.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.33/2.52  --sup_immed_triv                        [TrivRules]
% 15.33/2.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.33/2.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.33/2.52  --sup_immed_bw_main                     []
% 15.33/2.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.33/2.52  --sup_input_triv                        [Unflattening;TrivRules]
% 15.33/2.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.33/2.52  --sup_input_bw                          []
% 15.33/2.52  
% 15.33/2.52  ------ Combination Options
% 15.33/2.52  
% 15.33/2.52  --comb_res_mult                         3
% 15.33/2.52  --comb_sup_mult                         2
% 15.33/2.52  --comb_inst_mult                        10
% 15.33/2.52  
% 15.33/2.52  ------ Debug Options
% 15.33/2.52  
% 15.33/2.52  --dbg_backtrace                         false
% 15.33/2.52  --dbg_dump_prop_clauses                 false
% 15.33/2.52  --dbg_dump_prop_clauses_file            -
% 15.33/2.52  --dbg_out_stat                          false
% 15.33/2.52  ------ Parsing...
% 15.33/2.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.33/2.52  
% 15.33/2.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 15.33/2.52  
% 15.33/2.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.33/2.52  
% 15.33/2.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.33/2.52  ------ Proving...
% 15.33/2.52  ------ Problem Properties 
% 15.33/2.52  
% 15.33/2.52  
% 15.33/2.52  clauses                                 30
% 15.33/2.52  conjectures                             19
% 15.33/2.52  EPR                                     15
% 15.33/2.52  Horn                                    23
% 15.33/2.52  unary                                   19
% 15.33/2.52  binary                                  1
% 15.33/2.52  lits                                    131
% 15.33/2.52  lits eq                                 4
% 15.33/2.52  fd_pure                                 0
% 15.33/2.52  fd_pseudo                               0
% 15.33/2.52  fd_cond                                 0
% 15.33/2.52  fd_pseudo_cond                          1
% 15.33/2.52  AC symbols                              0
% 15.33/2.52  
% 15.33/2.52  ------ Schedule dynamic 5 is on 
% 15.33/2.52  
% 15.33/2.52  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.33/2.52  
% 15.33/2.52  
% 15.33/2.52  ------ 
% 15.33/2.52  Current options:
% 15.33/2.52  ------ 
% 15.33/2.52  
% 15.33/2.52  ------ Input Options
% 15.33/2.52  
% 15.33/2.52  --out_options                           all
% 15.33/2.52  --tptp_safe_out                         true
% 15.33/2.52  --problem_path                          ""
% 15.33/2.52  --include_path                          ""
% 15.33/2.52  --clausifier                            res/vclausify_rel
% 15.33/2.52  --clausifier_options                    ""
% 15.33/2.52  --stdin                                 false
% 15.33/2.52  --stats_out                             all
% 15.33/2.52  
% 15.33/2.52  ------ General Options
% 15.33/2.52  
% 15.33/2.52  --fof                                   false
% 15.33/2.52  --time_out_real                         305.
% 15.33/2.52  --time_out_virtual                      -1.
% 15.33/2.52  --symbol_type_check                     false
% 15.33/2.52  --clausify_out                          false
% 15.33/2.52  --sig_cnt_out                           false
% 15.33/2.52  --trig_cnt_out                          false
% 15.33/2.52  --trig_cnt_out_tolerance                1.
% 15.33/2.52  --trig_cnt_out_sk_spl                   false
% 15.33/2.52  --abstr_cl_out                          false
% 15.33/2.52  
% 15.33/2.52  ------ Global Options
% 15.33/2.52  
% 15.33/2.52  --schedule                              default
% 15.33/2.52  --add_important_lit                     false
% 15.33/2.52  --prop_solver_per_cl                    1000
% 15.33/2.52  --min_unsat_core                        false
% 15.33/2.52  --soft_assumptions                      false
% 15.33/2.52  --soft_lemma_size                       3
% 15.33/2.52  --prop_impl_unit_size                   0
% 15.33/2.52  --prop_impl_unit                        []
% 15.33/2.52  --share_sel_clauses                     true
% 15.33/2.52  --reset_solvers                         false
% 15.33/2.52  --bc_imp_inh                            [conj_cone]
% 15.33/2.52  --conj_cone_tolerance                   3.
% 15.33/2.52  --extra_neg_conj                        none
% 15.33/2.52  --large_theory_mode                     true
% 15.33/2.52  --prolific_symb_bound                   200
% 15.33/2.52  --lt_threshold                          2000
% 15.33/2.52  --clause_weak_htbl                      true
% 15.33/2.52  --gc_record_bc_elim                     false
% 15.33/2.52  
% 15.33/2.52  ------ Preprocessing Options
% 15.33/2.52  
% 15.33/2.52  --preprocessing_flag                    true
% 15.33/2.52  --time_out_prep_mult                    0.1
% 15.33/2.52  --splitting_mode                        input
% 15.33/2.52  --splitting_grd                         true
% 15.33/2.52  --splitting_cvd                         false
% 15.33/2.52  --splitting_cvd_svl                     false
% 15.33/2.52  --splitting_nvd                         32
% 15.33/2.52  --sub_typing                            true
% 15.33/2.52  --prep_gs_sim                           true
% 15.33/2.52  --prep_unflatten                        true
% 15.33/2.52  --prep_res_sim                          true
% 15.33/2.52  --prep_upred                            true
% 15.33/2.52  --prep_sem_filter                       exhaustive
% 15.33/2.52  --prep_sem_filter_out                   false
% 15.33/2.52  --pred_elim                             true
% 15.33/2.52  --res_sim_input                         true
% 15.33/2.52  --eq_ax_congr_red                       true
% 15.33/2.52  --pure_diseq_elim                       true
% 15.33/2.52  --brand_transform                       false
% 15.33/2.52  --non_eq_to_eq                          false
% 15.33/2.52  --prep_def_merge                        true
% 15.33/2.52  --prep_def_merge_prop_impl              false
% 15.33/2.52  --prep_def_merge_mbd                    true
% 15.33/2.52  --prep_def_merge_tr_red                 false
% 15.33/2.52  --prep_def_merge_tr_cl                  false
% 15.33/2.52  --smt_preprocessing                     true
% 15.33/2.52  --smt_ac_axioms                         fast
% 15.33/2.52  --preprocessed_out                      false
% 15.33/2.52  --preprocessed_stats                    false
% 15.33/2.52  
% 15.33/2.52  ------ Abstraction refinement Options
% 15.33/2.52  
% 15.33/2.52  --abstr_ref                             []
% 15.33/2.52  --abstr_ref_prep                        false
% 15.33/2.52  --abstr_ref_until_sat                   false
% 15.33/2.52  --abstr_ref_sig_restrict                funpre
% 15.33/2.52  --abstr_ref_af_restrict_to_split_sk     false
% 15.33/2.52  --abstr_ref_under                       []
% 15.33/2.52  
% 15.33/2.52  ------ SAT Options
% 15.33/2.52  
% 15.33/2.52  --sat_mode                              false
% 15.33/2.52  --sat_fm_restart_options                ""
% 15.33/2.52  --sat_gr_def                            false
% 15.33/2.52  --sat_epr_types                         true
% 15.33/2.52  --sat_non_cyclic_types                  false
% 15.33/2.52  --sat_finite_models                     false
% 15.33/2.52  --sat_fm_lemmas                         false
% 15.33/2.52  --sat_fm_prep                           false
% 15.33/2.52  --sat_fm_uc_incr                        true
% 15.33/2.52  --sat_out_model                         small
% 15.33/2.52  --sat_out_clauses                       false
% 15.33/2.52  
% 15.33/2.52  ------ QBF Options
% 15.33/2.52  
% 15.33/2.52  --qbf_mode                              false
% 15.33/2.52  --qbf_elim_univ                         false
% 15.33/2.52  --qbf_dom_inst                          none
% 15.33/2.52  --qbf_dom_pre_inst                      false
% 15.33/2.52  --qbf_sk_in                             false
% 15.33/2.52  --qbf_pred_elim                         true
% 15.33/2.52  --qbf_split                             512
% 15.33/2.52  
% 15.33/2.52  ------ BMC1 Options
% 15.33/2.52  
% 15.33/2.52  --bmc1_incremental                      false
% 15.33/2.52  --bmc1_axioms                           reachable_all
% 15.33/2.52  --bmc1_min_bound                        0
% 15.33/2.52  --bmc1_max_bound                        -1
% 15.33/2.52  --bmc1_max_bound_default                -1
% 15.33/2.52  --bmc1_symbol_reachability              true
% 15.33/2.52  --bmc1_property_lemmas                  false
% 15.33/2.52  --bmc1_k_induction                      false
% 15.33/2.52  --bmc1_non_equiv_states                 false
% 15.33/2.52  --bmc1_deadlock                         false
% 15.33/2.52  --bmc1_ucm                              false
% 15.33/2.52  --bmc1_add_unsat_core                   none
% 15.33/2.52  --bmc1_unsat_core_children              false
% 15.33/2.52  --bmc1_unsat_core_extrapolate_axioms    false
% 15.33/2.52  --bmc1_out_stat                         full
% 15.33/2.52  --bmc1_ground_init                      false
% 15.33/2.52  --bmc1_pre_inst_next_state              false
% 15.33/2.52  --bmc1_pre_inst_state                   false
% 15.33/2.52  --bmc1_pre_inst_reach_state             false
% 15.33/2.52  --bmc1_out_unsat_core                   false
% 15.33/2.52  --bmc1_aig_witness_out                  false
% 15.33/2.52  --bmc1_verbose                          false
% 15.33/2.52  --bmc1_dump_clauses_tptp                false
% 15.33/2.52  --bmc1_dump_unsat_core_tptp             false
% 15.33/2.52  --bmc1_dump_file                        -
% 15.33/2.52  --bmc1_ucm_expand_uc_limit              128
% 15.33/2.52  --bmc1_ucm_n_expand_iterations          6
% 15.33/2.52  --bmc1_ucm_extend_mode                  1
% 15.33/2.52  --bmc1_ucm_init_mode                    2
% 15.33/2.52  --bmc1_ucm_cone_mode                    none
% 15.33/2.52  --bmc1_ucm_reduced_relation_type        0
% 15.33/2.52  --bmc1_ucm_relax_model                  4
% 15.33/2.52  --bmc1_ucm_full_tr_after_sat            true
% 15.33/2.52  --bmc1_ucm_expand_neg_assumptions       false
% 15.33/2.52  --bmc1_ucm_layered_model                none
% 15.33/2.52  --bmc1_ucm_max_lemma_size               10
% 15.33/2.52  
% 15.33/2.52  ------ AIG Options
% 15.33/2.52  
% 15.33/2.52  --aig_mode                              false
% 15.33/2.52  
% 15.33/2.52  ------ Instantiation Options
% 15.33/2.52  
% 15.33/2.52  --instantiation_flag                    true
% 15.33/2.52  --inst_sos_flag                         true
% 15.33/2.52  --inst_sos_phase                        true
% 15.33/2.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.33/2.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.33/2.52  --inst_lit_sel_side                     none
% 15.33/2.52  --inst_solver_per_active                1400
% 15.33/2.52  --inst_solver_calls_frac                1.
% 15.33/2.52  --inst_passive_queue_type               priority_queues
% 15.33/2.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.33/2.52  --inst_passive_queues_freq              [25;2]
% 15.33/2.52  --inst_dismatching                      true
% 15.33/2.52  --inst_eager_unprocessed_to_passive     true
% 15.33/2.52  --inst_prop_sim_given                   true
% 15.33/2.52  --inst_prop_sim_new                     false
% 15.33/2.52  --inst_subs_new                         false
% 15.33/2.52  --inst_eq_res_simp                      false
% 15.33/2.52  --inst_subs_given                       false
% 15.33/2.52  --inst_orphan_elimination               true
% 15.33/2.52  --inst_learning_loop_flag               true
% 15.33/2.52  --inst_learning_start                   3000
% 15.33/2.52  --inst_learning_factor                  2
% 15.33/2.52  --inst_start_prop_sim_after_learn       3
% 15.33/2.52  --inst_sel_renew                        solver
% 15.33/2.52  --inst_lit_activity_flag                true
% 15.33/2.52  --inst_restr_to_given                   false
% 15.33/2.52  --inst_activity_threshold               500
% 15.33/2.52  --inst_out_proof                        true
% 15.33/2.52  
% 15.33/2.52  ------ Resolution Options
% 15.33/2.52  
% 15.33/2.52  --resolution_flag                       false
% 15.33/2.52  --res_lit_sel                           adaptive
% 15.33/2.52  --res_lit_sel_side                      none
% 15.33/2.52  --res_ordering                          kbo
% 15.33/2.52  --res_to_prop_solver                    active
% 15.33/2.52  --res_prop_simpl_new                    false
% 15.33/2.52  --res_prop_simpl_given                  true
% 15.33/2.52  --res_passive_queue_type                priority_queues
% 15.33/2.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.33/2.52  --res_passive_queues_freq               [15;5]
% 15.33/2.52  --res_forward_subs                      full
% 15.33/2.52  --res_backward_subs                     full
% 15.33/2.52  --res_forward_subs_resolution           true
% 15.33/2.52  --res_backward_subs_resolution          true
% 15.33/2.52  --res_orphan_elimination                true
% 15.33/2.52  --res_time_limit                        2.
% 15.33/2.52  --res_out_proof                         true
% 15.33/2.52  
% 15.33/2.52  ------ Superposition Options
% 15.33/2.52  
% 15.33/2.52  --superposition_flag                    true
% 15.33/2.52  --sup_passive_queue_type                priority_queues
% 15.33/2.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.33/2.52  --sup_passive_queues_freq               [8;1;4]
% 15.33/2.52  --demod_completeness_check              fast
% 15.33/2.52  --demod_use_ground                      true
% 15.33/2.52  --sup_to_prop_solver                    passive
% 15.33/2.52  --sup_prop_simpl_new                    true
% 15.33/2.52  --sup_prop_simpl_given                  true
% 15.33/2.52  --sup_fun_splitting                     true
% 15.33/2.52  --sup_smt_interval                      50000
% 15.33/2.52  
% 15.33/2.52  ------ Superposition Simplification Setup
% 15.33/2.52  
% 15.33/2.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.33/2.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.33/2.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.33/2.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.33/2.52  --sup_full_triv                         [TrivRules;PropSubs]
% 15.33/2.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.33/2.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.33/2.52  --sup_immed_triv                        [TrivRules]
% 15.33/2.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.33/2.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.33/2.52  --sup_immed_bw_main                     []
% 15.33/2.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.33/2.52  --sup_input_triv                        [Unflattening;TrivRules]
% 15.33/2.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.33/2.52  --sup_input_bw                          []
% 15.33/2.52  
% 15.33/2.52  ------ Combination Options
% 15.33/2.52  
% 15.33/2.52  --comb_res_mult                         3
% 15.33/2.52  --comb_sup_mult                         2
% 15.33/2.52  --comb_inst_mult                        10
% 15.33/2.52  
% 15.33/2.52  ------ Debug Options
% 15.33/2.52  
% 15.33/2.52  --dbg_backtrace                         false
% 15.33/2.52  --dbg_dump_prop_clauses                 false
% 15.33/2.52  --dbg_dump_prop_clauses_file            -
% 15.33/2.52  --dbg_out_stat                          false
% 15.33/2.52  
% 15.33/2.52  
% 15.33/2.52  
% 15.33/2.52  
% 15.33/2.52  ------ Proving...
% 15.33/2.52  
% 15.33/2.52  
% 15.33/2.52  % SZS status Theorem for theBenchmark.p
% 15.33/2.52  
% 15.33/2.52  % SZS output start CNFRefutation for theBenchmark.p
% 15.33/2.52  
% 15.33/2.52  fof(f9,conjecture,(
% 15.33/2.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6) => r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6))))))))))),
% 15.33/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.33/2.52  
% 15.33/2.52  fof(f10,negated_conjecture,(
% 15.33/2.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6) => r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6))))))))))),
% 15.33/2.52    inference(negated_conjecture,[],[f9])).
% 15.33/2.52  
% 15.33/2.52  fof(f26,plain,(
% 15.33/2.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & (r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 15.33/2.52    inference(ennf_transformation,[],[f10])).
% 15.33/2.52  
% 15.33/2.52  fof(f27,plain,(
% 15.33/2.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 15.33/2.52    inference(flattening,[],[f26])).
% 15.33/2.52  
% 15.33/2.52  fof(f35,plain,(
% 15.33/2.52    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),sK6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & sK6 = X5 & m1_subset_1(sK6,u1_struct_0(X2)))) )),
% 15.33/2.52    introduced(choice_axiom,[])).
% 15.33/2.52  
% 15.33/2.52  fof(f34,plain,(
% 15.33/2.52    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),sK5) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK5,u1_struct_0(X3)))) )),
% 15.33/2.52    introduced(choice_axiom,[])).
% 15.33/2.52  
% 15.33/2.52  fof(f33,plain,(
% 15.33/2.52    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,sK4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,sK4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 15.33/2.52    introduced(choice_axiom,[])).
% 15.33/2.52  
% 15.33/2.52  fof(f32,plain,(
% 15.33/2.52    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(sK3,X1,k2_tmap_1(X0,X1,X4,sK3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_pre_topc(X2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 15.33/2.52    introduced(choice_axiom,[])).
% 15.33/2.52  
% 15.33/2.52  fof(f31,plain,(
% 15.33/2.52    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK2,X1,k2_tmap_1(X0,X1,X4,sK2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 15.33/2.52    introduced(choice_axiom,[])).
% 15.33/2.52  
% 15.33/2.52  fof(f30,plain,(
% 15.33/2.52    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,sK1,k2_tmap_1(X0,sK1,X4,X2),X6) & r1_tmap_1(X3,sK1,k2_tmap_1(X0,sK1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 15.33/2.52    introduced(choice_axiom,[])).
% 15.33/2.52  
% 15.33/2.52  fof(f29,plain,(
% 15.33/2.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(sK0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 15.33/2.52    introduced(choice_axiom,[])).
% 15.33/2.52  
% 15.33/2.52  fof(f36,plain,(
% 15.33/2.52    ((((((~r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 15.33/2.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f27,f35,f34,f33,f32,f31,f30,f29])).
% 15.33/2.52  
% 15.33/2.52  fof(f65,plain,(
% 15.33/2.52    r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5)),
% 15.33/2.52    inference(cnf_transformation,[],[f36])).
% 15.33/2.52  
% 15.33/2.52  fof(f64,plain,(
% 15.33/2.52    sK5 = sK6),
% 15.33/2.52    inference(cnf_transformation,[],[f36])).
% 15.33/2.52  
% 15.33/2.52  fof(f57,plain,(
% 15.33/2.52    m1_pre_topc(sK3,sK0)),
% 15.33/2.52    inference(cnf_transformation,[],[f36])).
% 15.33/2.52  
% 15.33/2.52  fof(f60,plain,(
% 15.33/2.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 15.33/2.52    inference(cnf_transformation,[],[f36])).
% 15.33/2.52  
% 15.33/2.52  fof(f3,axiom,(
% 15.33/2.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 15.33/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.33/2.52  
% 15.33/2.52  fof(f15,plain,(
% 15.33/2.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 15.33/2.52    inference(ennf_transformation,[],[f3])).
% 15.33/2.52  
% 15.33/2.52  fof(f16,plain,(
% 15.33/2.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 15.33/2.52    inference(flattening,[],[f15])).
% 15.33/2.52  
% 15.33/2.52  fof(f40,plain,(
% 15.33/2.52    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.33/2.52    inference(cnf_transformation,[],[f16])).
% 15.33/2.52  
% 15.33/2.52  fof(f51,plain,(
% 15.33/2.52    ~v2_struct_0(sK1)),
% 15.33/2.52    inference(cnf_transformation,[],[f36])).
% 15.33/2.52  
% 15.33/2.52  fof(f52,plain,(
% 15.33/2.52    v2_pre_topc(sK1)),
% 15.33/2.52    inference(cnf_transformation,[],[f36])).
% 15.33/2.52  
% 15.33/2.52  fof(f53,plain,(
% 15.33/2.52    l1_pre_topc(sK1)),
% 15.33/2.52    inference(cnf_transformation,[],[f36])).
% 15.33/2.52  
% 15.33/2.52  fof(f58,plain,(
% 15.33/2.52    v1_funct_1(sK4)),
% 15.33/2.52    inference(cnf_transformation,[],[f36])).
% 15.33/2.52  
% 15.33/2.52  fof(f59,plain,(
% 15.33/2.52    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))),
% 15.33/2.52    inference(cnf_transformation,[],[f36])).
% 15.33/2.52  
% 15.33/2.52  fof(f2,axiom,(
% 15.33/2.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 15.33/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.33/2.52  
% 15.33/2.52  fof(f13,plain,(
% 15.33/2.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 15.33/2.52    inference(ennf_transformation,[],[f2])).
% 15.33/2.52  
% 15.33/2.52  fof(f14,plain,(
% 15.33/2.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 15.33/2.52    inference(flattening,[],[f13])).
% 15.33/2.52  
% 15.33/2.52  fof(f39,plain,(
% 15.33/2.52    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.33/2.52    inference(cnf_transformation,[],[f14])).
% 15.33/2.52  
% 15.33/2.52  fof(f48,plain,(
% 15.33/2.52    ~v2_struct_0(sK0)),
% 15.33/2.52    inference(cnf_transformation,[],[f36])).
% 15.33/2.52  
% 15.33/2.52  fof(f49,plain,(
% 15.33/2.52    v2_pre_topc(sK0)),
% 15.33/2.52    inference(cnf_transformation,[],[f36])).
% 15.33/2.52  
% 15.33/2.52  fof(f50,plain,(
% 15.33/2.52    l1_pre_topc(sK0)),
% 15.33/2.52    inference(cnf_transformation,[],[f36])).
% 15.33/2.52  
% 15.33/2.52  fof(f5,axiom,(
% 15.33/2.52    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 15.33/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.33/2.52  
% 15.33/2.52  fof(f19,plain,(
% 15.33/2.52    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 15.33/2.52    inference(ennf_transformation,[],[f5])).
% 15.33/2.52  
% 15.33/2.52  fof(f44,plain,(
% 15.33/2.52    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 15.33/2.52    inference(cnf_transformation,[],[f19])).
% 15.33/2.52  
% 15.33/2.52  fof(f4,axiom,(
% 15.33/2.52    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 15.33/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.33/2.52  
% 15.33/2.52  fof(f17,plain,(
% 15.33/2.52    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 15.33/2.52    inference(ennf_transformation,[],[f4])).
% 15.33/2.52  
% 15.33/2.52  fof(f18,plain,(
% 15.33/2.52    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 15.33/2.52    inference(flattening,[],[f17])).
% 15.33/2.52  
% 15.33/2.52  fof(f43,plain,(
% 15.33/2.52    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.33/2.52    inference(cnf_transformation,[],[f18])).
% 15.33/2.52  
% 15.33/2.52  fof(f55,plain,(
% 15.33/2.52    m1_pre_topc(sK2,sK0)),
% 15.33/2.52    inference(cnf_transformation,[],[f36])).
% 15.33/2.52  
% 15.33/2.52  fof(f42,plain,(
% 15.33/2.52    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.33/2.52    inference(cnf_transformation,[],[f18])).
% 15.33/2.52  
% 15.33/2.52  fof(f6,axiom,(
% 15.33/2.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))))))))),
% 15.33/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.33/2.52  
% 15.33/2.52  fof(f20,plain,(
% 15.33/2.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 15.33/2.52    inference(ennf_transformation,[],[f6])).
% 15.33/2.52  
% 15.33/2.52  fof(f21,plain,(
% 15.33/2.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 15.33/2.52    inference(flattening,[],[f20])).
% 15.33/2.52  
% 15.33/2.52  fof(f45,plain,(
% 15.33/2.52    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.33/2.52    inference(cnf_transformation,[],[f21])).
% 15.33/2.52  
% 15.33/2.52  fof(f1,axiom,(
% 15.33/2.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 15.33/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.33/2.52  
% 15.33/2.52  fof(f11,plain,(
% 15.33/2.52    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 15.33/2.52    inference(ennf_transformation,[],[f1])).
% 15.33/2.52  
% 15.33/2.52  fof(f12,plain,(
% 15.33/2.52    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 15.33/2.52    inference(flattening,[],[f11])).
% 15.33/2.52  
% 15.33/2.52  fof(f28,plain,(
% 15.33/2.52    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 15.33/2.52    inference(nnf_transformation,[],[f12])).
% 15.33/2.52  
% 15.33/2.52  fof(f37,plain,(
% 15.33/2.52    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 15.33/2.52    inference(cnf_transformation,[],[f28])).
% 15.33/2.52  
% 15.33/2.52  fof(f54,plain,(
% 15.33/2.52    ~v2_struct_0(sK2)),
% 15.33/2.52    inference(cnf_transformation,[],[f36])).
% 15.33/2.52  
% 15.33/2.52  fof(f41,plain,(
% 15.33/2.52    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.33/2.52    inference(cnf_transformation,[],[f18])).
% 15.33/2.52  
% 15.33/2.52  fof(f56,plain,(
% 15.33/2.52    ~v2_struct_0(sK3)),
% 15.33/2.52    inference(cnf_transformation,[],[f36])).
% 15.33/2.52  
% 15.33/2.52  fof(f61,plain,(
% 15.33/2.52    m1_pre_topc(sK2,sK3)),
% 15.33/2.52    inference(cnf_transformation,[],[f36])).
% 15.33/2.52  
% 15.33/2.52  fof(f8,axiom,(
% 15.33/2.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((r1_tmap_1(X2,X1,X4,X5) & m1_pre_topc(X3,X2) & X5 = X6) => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)))))))))),
% 15.33/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.33/2.52  
% 15.33/2.52  fof(f24,plain,(
% 15.33/2.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | (~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 15.33/2.52    inference(ennf_transformation,[],[f8])).
% 15.33/2.52  
% 15.33/2.52  fof(f25,plain,(
% 15.33/2.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 15.33/2.52    inference(flattening,[],[f24])).
% 15.33/2.52  
% 15.33/2.52  fof(f47,plain,(
% 15.33/2.52    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.33/2.52    inference(cnf_transformation,[],[f25])).
% 15.33/2.52  
% 15.33/2.52  fof(f68,plain,(
% 15.33/2.52    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X6) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.33/2.52    inference(equality_resolution,[],[f47])).
% 15.33/2.52  
% 15.33/2.52  fof(f62,plain,(
% 15.33/2.52    m1_subset_1(sK5,u1_struct_0(sK3))),
% 15.33/2.52    inference(cnf_transformation,[],[f36])).
% 15.33/2.52  
% 15.33/2.52  fof(f66,plain,(
% 15.33/2.52    ~r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6)),
% 15.33/2.52    inference(cnf_transformation,[],[f36])).
% 15.33/2.52  
% 15.33/2.52  fof(f63,plain,(
% 15.33/2.52    m1_subset_1(sK6,u1_struct_0(sK2))),
% 15.33/2.52    inference(cnf_transformation,[],[f36])).
% 15.33/2.52  
% 15.33/2.52  cnf(c_12,negated_conjecture,
% 15.33/2.52      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) ),
% 15.33/2.52      inference(cnf_transformation,[],[f65]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_389,negated_conjecture,
% 15.33/2.52      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) ),
% 15.33/2.52      inference(subtyping,[status(esa)],[c_12]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_906,plain,
% 15.33/2.52      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) = iProver_top ),
% 15.33/2.52      inference(predicate_to_equality,[status(thm)],[c_389]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_13,negated_conjecture,
% 15.33/2.52      ( sK5 = sK6 ),
% 15.33/2.52      inference(cnf_transformation,[],[f64]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_388,negated_conjecture,
% 15.33/2.52      ( sK5 = sK6 ),
% 15.33/2.52      inference(subtyping,[status(esa)],[c_13]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_924,plain,
% 15.33/2.52      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK6) = iProver_top ),
% 15.33/2.52      inference(light_normalisation,[status(thm)],[c_906,c_388]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_20,negated_conjecture,
% 15.33/2.52      ( m1_pre_topc(sK3,sK0) ),
% 15.33/2.52      inference(cnf_transformation,[],[f57]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_381,negated_conjecture,
% 15.33/2.52      ( m1_pre_topc(sK3,sK0) ),
% 15.33/2.52      inference(subtyping,[status(esa)],[c_20]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_913,plain,
% 15.33/2.52      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 15.33/2.52      inference(predicate_to_equality,[status(thm)],[c_381]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_17,negated_conjecture,
% 15.33/2.52      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 15.33/2.52      inference(cnf_transformation,[],[f60]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_384,negated_conjecture,
% 15.33/2.52      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 15.33/2.52      inference(subtyping,[status(esa)],[c_17]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_910,plain,
% 15.33/2.52      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 15.33/2.52      inference(predicate_to_equality,[status(thm)],[c_384]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_3,plain,
% 15.33/2.52      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 15.33/2.52      | ~ m1_pre_topc(X3,X4)
% 15.33/2.52      | ~ m1_pre_topc(X3,X1)
% 15.33/2.52      | ~ m1_pre_topc(X1,X4)
% 15.33/2.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 15.33/2.52      | v2_struct_0(X4)
% 15.33/2.52      | v2_struct_0(X2)
% 15.33/2.52      | ~ v2_pre_topc(X2)
% 15.33/2.52      | ~ v2_pre_topc(X4)
% 15.33/2.52      | ~ l1_pre_topc(X2)
% 15.33/2.52      | ~ l1_pre_topc(X4)
% 15.33/2.52      | ~ v1_funct_1(X0)
% 15.33/2.52      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 15.33/2.52      inference(cnf_transformation,[],[f40]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_398,plain,
% 15.33/2.52      ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
% 15.33/2.52      | ~ m1_pre_topc(X2_50,X3_50)
% 15.33/2.52      | ~ m1_pre_topc(X2_50,X0_50)
% 15.33/2.52      | ~ m1_pre_topc(X0_50,X3_50)
% 15.33/2.52      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 15.33/2.52      | v2_struct_0(X1_50)
% 15.33/2.52      | v2_struct_0(X3_50)
% 15.33/2.52      | ~ v2_pre_topc(X1_50)
% 15.33/2.52      | ~ v2_pre_topc(X3_50)
% 15.33/2.52      | ~ l1_pre_topc(X1_50)
% 15.33/2.52      | ~ l1_pre_topc(X3_50)
% 15.33/2.52      | ~ v1_funct_1(X0_51)
% 15.33/2.52      | k2_partfun1(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,u1_struct_0(X2_50)) = k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_51) ),
% 15.33/2.52      inference(subtyping,[status(esa)],[c_3]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_897,plain,
% 15.33/2.52      ( k2_partfun1(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,u1_struct_0(X2_50)) = k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_51)
% 15.33/2.52      | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 15.33/2.52      | m1_pre_topc(X0_50,X3_50) != iProver_top
% 15.33/2.52      | m1_pre_topc(X2_50,X0_50) != iProver_top
% 15.33/2.52      | m1_pre_topc(X2_50,X3_50) != iProver_top
% 15.33/2.52      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 15.33/2.52      | v2_struct_0(X1_50) = iProver_top
% 15.33/2.52      | v2_struct_0(X3_50) = iProver_top
% 15.33/2.52      | v2_pre_topc(X1_50) != iProver_top
% 15.33/2.52      | v2_pre_topc(X3_50) != iProver_top
% 15.33/2.52      | l1_pre_topc(X1_50) != iProver_top
% 15.33/2.52      | l1_pre_topc(X3_50) != iProver_top
% 15.33/2.52      | v1_funct_1(X0_51) != iProver_top ),
% 15.33/2.52      inference(predicate_to_equality,[status(thm)],[c_398]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_1857,plain,
% 15.33/2.52      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK0,X0_50,sK4)
% 15.33/2.52      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 15.33/2.52      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 15.33/2.52      | m1_pre_topc(X0_50,sK0) != iProver_top
% 15.33/2.52      | m1_pre_topc(sK0,X1_50) != iProver_top
% 15.33/2.52      | v2_struct_0(X1_50) = iProver_top
% 15.33/2.52      | v2_struct_0(sK1) = iProver_top
% 15.33/2.52      | v2_pre_topc(X1_50) != iProver_top
% 15.33/2.52      | v2_pre_topc(sK1) != iProver_top
% 15.33/2.52      | l1_pre_topc(X1_50) != iProver_top
% 15.33/2.52      | l1_pre_topc(sK1) != iProver_top
% 15.33/2.52      | v1_funct_1(sK4) != iProver_top ),
% 15.33/2.52      inference(superposition,[status(thm)],[c_910,c_897]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_26,negated_conjecture,
% 15.33/2.52      ( ~ v2_struct_0(sK1) ),
% 15.33/2.52      inference(cnf_transformation,[],[f51]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_33,plain,
% 15.33/2.52      ( v2_struct_0(sK1) != iProver_top ),
% 15.33/2.52      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_25,negated_conjecture,
% 15.33/2.52      ( v2_pre_topc(sK1) ),
% 15.33/2.52      inference(cnf_transformation,[],[f52]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_34,plain,
% 15.33/2.52      ( v2_pre_topc(sK1) = iProver_top ),
% 15.33/2.52      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_24,negated_conjecture,
% 15.33/2.52      ( l1_pre_topc(sK1) ),
% 15.33/2.52      inference(cnf_transformation,[],[f53]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_35,plain,
% 15.33/2.52      ( l1_pre_topc(sK1) = iProver_top ),
% 15.33/2.52      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_19,negated_conjecture,
% 15.33/2.52      ( v1_funct_1(sK4) ),
% 15.33/2.52      inference(cnf_transformation,[],[f58]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_40,plain,
% 15.33/2.52      ( v1_funct_1(sK4) = iProver_top ),
% 15.33/2.52      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_18,negated_conjecture,
% 15.33/2.52      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 15.33/2.52      inference(cnf_transformation,[],[f59]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_41,plain,
% 15.33/2.52      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 15.33/2.52      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_2068,plain,
% 15.33/2.52      ( v2_pre_topc(X1_50) != iProver_top
% 15.33/2.52      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK0,X0_50,sK4)
% 15.33/2.52      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 15.33/2.52      | m1_pre_topc(X0_50,sK0) != iProver_top
% 15.33/2.52      | m1_pre_topc(sK0,X1_50) != iProver_top
% 15.33/2.52      | v2_struct_0(X1_50) = iProver_top
% 15.33/2.52      | l1_pre_topc(X1_50) != iProver_top ),
% 15.33/2.52      inference(global_propositional_subsumption,
% 15.33/2.52                [status(thm)],
% 15.33/2.52                [c_1857,c_33,c_34,c_35,c_40,c_41]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_2069,plain,
% 15.33/2.52      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK0,X0_50,sK4)
% 15.33/2.52      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 15.33/2.52      | m1_pre_topc(X0_50,sK0) != iProver_top
% 15.33/2.52      | m1_pre_topc(sK0,X1_50) != iProver_top
% 15.33/2.52      | v2_struct_0(X1_50) = iProver_top
% 15.33/2.52      | v2_pre_topc(X1_50) != iProver_top
% 15.33/2.52      | l1_pre_topc(X1_50) != iProver_top ),
% 15.33/2.52      inference(renaming,[status(thm)],[c_2068]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_2075,plain,
% 15.33/2.52      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4)
% 15.33/2.52      | m1_pre_topc(sK3,sK0) != iProver_top
% 15.33/2.52      | m1_pre_topc(sK0,sK0) != iProver_top
% 15.33/2.52      | v2_struct_0(sK0) = iProver_top
% 15.33/2.52      | v2_pre_topc(sK0) != iProver_top
% 15.33/2.52      | l1_pre_topc(sK0) != iProver_top ),
% 15.33/2.52      inference(superposition,[status(thm)],[c_913,c_2069]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_2,plain,
% 15.33/2.52      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 15.33/2.52      | ~ m1_pre_topc(X3,X1)
% 15.33/2.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 15.33/2.52      | v2_struct_0(X1)
% 15.33/2.52      | v2_struct_0(X2)
% 15.33/2.52      | ~ v2_pre_topc(X2)
% 15.33/2.52      | ~ v2_pre_topc(X1)
% 15.33/2.52      | ~ l1_pre_topc(X2)
% 15.33/2.52      | ~ l1_pre_topc(X1)
% 15.33/2.52      | ~ v1_funct_1(X0)
% 15.33/2.52      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 15.33/2.52      inference(cnf_transformation,[],[f39]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_399,plain,
% 15.33/2.52      ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
% 15.33/2.52      | ~ m1_pre_topc(X2_50,X0_50)
% 15.33/2.52      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 15.33/2.52      | v2_struct_0(X1_50)
% 15.33/2.52      | v2_struct_0(X0_50)
% 15.33/2.52      | ~ v2_pre_topc(X1_50)
% 15.33/2.52      | ~ v2_pre_topc(X0_50)
% 15.33/2.52      | ~ l1_pre_topc(X1_50)
% 15.33/2.52      | ~ l1_pre_topc(X0_50)
% 15.33/2.52      | ~ v1_funct_1(X0_51)
% 15.33/2.52      | k2_partfun1(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,u1_struct_0(X2_50)) = k2_tmap_1(X0_50,X1_50,X0_51,X2_50) ),
% 15.33/2.52      inference(subtyping,[status(esa)],[c_2]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_896,plain,
% 15.33/2.52      ( k2_partfun1(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,u1_struct_0(X2_50)) = k2_tmap_1(X0_50,X1_50,X0_51,X2_50)
% 15.33/2.52      | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 15.33/2.52      | m1_pre_topc(X2_50,X0_50) != iProver_top
% 15.33/2.52      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 15.33/2.52      | v2_struct_0(X1_50) = iProver_top
% 15.33/2.52      | v2_struct_0(X0_50) = iProver_top
% 15.33/2.52      | v2_pre_topc(X1_50) != iProver_top
% 15.33/2.52      | v2_pre_topc(X0_50) != iProver_top
% 15.33/2.52      | l1_pre_topc(X1_50) != iProver_top
% 15.33/2.52      | l1_pre_topc(X0_50) != iProver_top
% 15.33/2.52      | v1_funct_1(X0_51) != iProver_top ),
% 15.33/2.52      inference(predicate_to_equality,[status(thm)],[c_399]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_1571,plain,
% 15.33/2.52      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k2_tmap_1(sK0,sK1,sK4,X0_50)
% 15.33/2.52      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 15.33/2.52      | m1_pre_topc(X0_50,sK0) != iProver_top
% 15.33/2.52      | v2_struct_0(sK0) = iProver_top
% 15.33/2.52      | v2_struct_0(sK1) = iProver_top
% 15.33/2.52      | v2_pre_topc(sK0) != iProver_top
% 15.33/2.52      | v2_pre_topc(sK1) != iProver_top
% 15.33/2.52      | l1_pre_topc(sK0) != iProver_top
% 15.33/2.52      | l1_pre_topc(sK1) != iProver_top
% 15.33/2.52      | v1_funct_1(sK4) != iProver_top ),
% 15.33/2.52      inference(superposition,[status(thm)],[c_910,c_896]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_29,negated_conjecture,
% 15.33/2.52      ( ~ v2_struct_0(sK0) ),
% 15.33/2.52      inference(cnf_transformation,[],[f48]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_30,plain,
% 15.33/2.52      ( v2_struct_0(sK0) != iProver_top ),
% 15.33/2.52      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_28,negated_conjecture,
% 15.33/2.52      ( v2_pre_topc(sK0) ),
% 15.33/2.52      inference(cnf_transformation,[],[f49]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_31,plain,
% 15.33/2.52      ( v2_pre_topc(sK0) = iProver_top ),
% 15.33/2.52      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_27,negated_conjecture,
% 15.33/2.52      ( l1_pre_topc(sK0) ),
% 15.33/2.52      inference(cnf_transformation,[],[f50]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_32,plain,
% 15.33/2.52      ( l1_pre_topc(sK0) = iProver_top ),
% 15.33/2.52      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_1749,plain,
% 15.33/2.52      ( m1_pre_topc(X0_50,sK0) != iProver_top
% 15.33/2.52      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k2_tmap_1(sK0,sK1,sK4,X0_50) ),
% 15.33/2.52      inference(global_propositional_subsumption,
% 15.33/2.52                [status(thm)],
% 15.33/2.52                [c_1571,c_30,c_31,c_32,c_33,c_34,c_35,c_40,c_41]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_1750,plain,
% 15.33/2.52      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k2_tmap_1(sK0,sK1,sK4,X0_50)
% 15.33/2.52      | m1_pre_topc(X0_50,sK0) != iProver_top ),
% 15.33/2.52      inference(renaming,[status(thm)],[c_1749]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_1755,plain,
% 15.33/2.52      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
% 15.33/2.52      inference(superposition,[status(thm)],[c_913,c_1750]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_2079,plain,
% 15.33/2.52      ( k3_tmap_1(sK0,sK1,sK0,sK3,sK4) = k2_tmap_1(sK0,sK1,sK4,sK3)
% 15.33/2.52      | m1_pre_topc(sK3,sK0) != iProver_top
% 15.33/2.52      | m1_pre_topc(sK0,sK0) != iProver_top
% 15.33/2.52      | v2_struct_0(sK0) = iProver_top
% 15.33/2.52      | v2_pre_topc(sK0) != iProver_top
% 15.33/2.52      | l1_pre_topc(sK0) != iProver_top ),
% 15.33/2.52      inference(light_normalisation,[status(thm)],[c_2075,c_1755]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_39,plain,
% 15.33/2.52      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 15.33/2.52      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_7,plain,
% 15.33/2.52      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 15.33/2.52      inference(cnf_transformation,[],[f44]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_55,plain,
% 15.33/2.52      ( m1_pre_topc(X0,X0) = iProver_top
% 15.33/2.52      | l1_pre_topc(X0) != iProver_top ),
% 15.33/2.52      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_57,plain,
% 15.33/2.52      ( m1_pre_topc(sK0,sK0) = iProver_top
% 15.33/2.52      | l1_pre_topc(sK0) != iProver_top ),
% 15.33/2.52      inference(instantiation,[status(thm)],[c_55]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_2223,plain,
% 15.33/2.52      ( k3_tmap_1(sK0,sK1,sK0,sK3,sK4) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
% 15.33/2.52      inference(global_propositional_subsumption,
% 15.33/2.52                [status(thm)],
% 15.33/2.52                [c_2079,c_30,c_31,c_32,c_39,c_57]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_4,plain,
% 15.33/2.52      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 15.33/2.52      | ~ m1_pre_topc(X3,X4)
% 15.33/2.52      | ~ m1_pre_topc(X1,X4)
% 15.33/2.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 15.33/2.52      | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 15.33/2.52      | v2_struct_0(X4)
% 15.33/2.52      | v2_struct_0(X2)
% 15.33/2.52      | ~ v2_pre_topc(X2)
% 15.33/2.52      | ~ v2_pre_topc(X4)
% 15.33/2.52      | ~ l1_pre_topc(X2)
% 15.33/2.52      | ~ l1_pre_topc(X4)
% 15.33/2.52      | ~ v1_funct_1(X0) ),
% 15.33/2.52      inference(cnf_transformation,[],[f43]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_397,plain,
% 15.33/2.52      ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
% 15.33/2.52      | ~ m1_pre_topc(X2_50,X3_50)
% 15.33/2.52      | ~ m1_pre_topc(X0_50,X3_50)
% 15.33/2.52      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 15.33/2.52      | m1_subset_1(k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50))))
% 15.33/2.52      | v2_struct_0(X1_50)
% 15.33/2.52      | v2_struct_0(X3_50)
% 15.33/2.52      | ~ v2_pre_topc(X1_50)
% 15.33/2.52      | ~ v2_pre_topc(X3_50)
% 15.33/2.52      | ~ l1_pre_topc(X1_50)
% 15.33/2.52      | ~ l1_pre_topc(X3_50)
% 15.33/2.52      | ~ v1_funct_1(X0_51) ),
% 15.33/2.52      inference(subtyping,[status(esa)],[c_4]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_898,plain,
% 15.33/2.52      ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 15.33/2.52      | m1_pre_topc(X0_50,X2_50) != iProver_top
% 15.33/2.52      | m1_pre_topc(X3_50,X2_50) != iProver_top
% 15.33/2.52      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 15.33/2.52      | m1_subset_1(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50)))) = iProver_top
% 15.33/2.52      | v2_struct_0(X1_50) = iProver_top
% 15.33/2.52      | v2_struct_0(X2_50) = iProver_top
% 15.33/2.52      | v2_pre_topc(X1_50) != iProver_top
% 15.33/2.52      | v2_pre_topc(X2_50) != iProver_top
% 15.33/2.52      | l1_pre_topc(X1_50) != iProver_top
% 15.33/2.52      | l1_pre_topc(X2_50) != iProver_top
% 15.33/2.52      | v1_funct_1(X0_51) != iProver_top ),
% 15.33/2.52      inference(predicate_to_equality,[status(thm)],[c_397]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_2226,plain,
% 15.33/2.52      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 15.33/2.52      | m1_pre_topc(sK3,sK0) != iProver_top
% 15.33/2.52      | m1_pre_topc(sK0,sK0) != iProver_top
% 15.33/2.52      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top
% 15.33/2.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 15.33/2.52      | v2_struct_0(sK0) = iProver_top
% 15.33/2.52      | v2_struct_0(sK1) = iProver_top
% 15.33/2.52      | v2_pre_topc(sK0) != iProver_top
% 15.33/2.52      | v2_pre_topc(sK1) != iProver_top
% 15.33/2.52      | l1_pre_topc(sK0) != iProver_top
% 15.33/2.52      | l1_pre_topc(sK1) != iProver_top
% 15.33/2.52      | v1_funct_1(sK4) != iProver_top ),
% 15.33/2.52      inference(superposition,[status(thm)],[c_2223,c_898]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_42,plain,
% 15.33/2.52      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 15.33/2.52      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_2791,plain,
% 15.33/2.52      ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 15.33/2.52      inference(global_propositional_subsumption,
% 15.33/2.52                [status(thm)],
% 15.33/2.52                [c_2226,c_30,c_31,c_32,c_33,c_34,c_35,c_39,c_40,c_41,
% 15.33/2.52                 c_42,c_57]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_22,negated_conjecture,
% 15.33/2.52      ( m1_pre_topc(sK2,sK0) ),
% 15.33/2.52      inference(cnf_transformation,[],[f55]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_379,negated_conjecture,
% 15.33/2.52      ( m1_pre_topc(sK2,sK0) ),
% 15.33/2.52      inference(subtyping,[status(esa)],[c_22]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_915,plain,
% 15.33/2.52      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 15.33/2.52      inference(predicate_to_equality,[status(thm)],[c_379]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_2076,plain,
% 15.33/2.52      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4)
% 15.33/2.52      | m1_pre_topc(sK0,sK0) != iProver_top
% 15.33/2.52      | m1_pre_topc(sK2,sK0) != iProver_top
% 15.33/2.52      | v2_struct_0(sK0) = iProver_top
% 15.33/2.52      | v2_pre_topc(sK0) != iProver_top
% 15.33/2.52      | l1_pre_topc(sK0) != iProver_top ),
% 15.33/2.52      inference(superposition,[status(thm)],[c_915,c_2069]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_1756,plain,
% 15.33/2.52      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
% 15.33/2.52      inference(superposition,[status(thm)],[c_915,c_1750]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_2078,plain,
% 15.33/2.52      ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k2_tmap_1(sK0,sK1,sK4,sK2)
% 15.33/2.52      | m1_pre_topc(sK0,sK0) != iProver_top
% 15.33/2.52      | m1_pre_topc(sK2,sK0) != iProver_top
% 15.33/2.52      | v2_struct_0(sK0) = iProver_top
% 15.33/2.52      | v2_pre_topc(sK0) != iProver_top
% 15.33/2.52      | l1_pre_topc(sK0) != iProver_top ),
% 15.33/2.52      inference(light_normalisation,[status(thm)],[c_2076,c_1756]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_37,plain,
% 15.33/2.52      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 15.33/2.52      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_2137,plain,
% 15.33/2.52      ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
% 15.33/2.52      inference(global_propositional_subsumption,
% 15.33/2.52                [status(thm)],
% 15.33/2.52                [c_2078,c_30,c_31,c_32,c_37,c_57]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_2140,plain,
% 15.33/2.52      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 15.33/2.52      | m1_pre_topc(sK0,sK0) != iProver_top
% 15.33/2.52      | m1_pre_topc(sK2,sK0) != iProver_top
% 15.33/2.52      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
% 15.33/2.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 15.33/2.52      | v2_struct_0(sK0) = iProver_top
% 15.33/2.52      | v2_struct_0(sK1) = iProver_top
% 15.33/2.52      | v2_pre_topc(sK0) != iProver_top
% 15.33/2.52      | v2_pre_topc(sK1) != iProver_top
% 15.33/2.52      | l1_pre_topc(sK0) != iProver_top
% 15.33/2.52      | l1_pre_topc(sK1) != iProver_top
% 15.33/2.52      | v1_funct_1(sK4) != iProver_top ),
% 15.33/2.52      inference(superposition,[status(thm)],[c_2137,c_898]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_2544,plain,
% 15.33/2.52      ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 15.33/2.52      inference(global_propositional_subsumption,
% 15.33/2.52                [status(thm)],
% 15.33/2.52                [c_2140,c_30,c_31,c_32,c_33,c_34,c_35,c_37,c_40,c_41,
% 15.33/2.52                 c_42,c_57]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_5,plain,
% 15.33/2.52      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 15.33/2.52      | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
% 15.33/2.52      | ~ m1_pre_topc(X4,X3)
% 15.33/2.52      | ~ m1_pre_topc(X1,X3)
% 15.33/2.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 15.33/2.52      | v2_struct_0(X3)
% 15.33/2.52      | v2_struct_0(X2)
% 15.33/2.52      | ~ v2_pre_topc(X2)
% 15.33/2.52      | ~ v2_pre_topc(X3)
% 15.33/2.52      | ~ l1_pre_topc(X2)
% 15.33/2.52      | ~ l1_pre_topc(X3)
% 15.33/2.52      | ~ v1_funct_1(X0) ),
% 15.33/2.52      inference(cnf_transformation,[],[f42]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_396,plain,
% 15.33/2.52      ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
% 15.33/2.52      | v1_funct_2(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51),u1_struct_0(X3_50),u1_struct_0(X1_50))
% 15.33/2.52      | ~ m1_pre_topc(X3_50,X2_50)
% 15.33/2.52      | ~ m1_pre_topc(X0_50,X2_50)
% 15.33/2.52      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 15.33/2.52      | v2_struct_0(X1_50)
% 15.33/2.52      | v2_struct_0(X2_50)
% 15.33/2.52      | ~ v2_pre_topc(X1_50)
% 15.33/2.52      | ~ v2_pre_topc(X2_50)
% 15.33/2.52      | ~ l1_pre_topc(X1_50)
% 15.33/2.52      | ~ l1_pre_topc(X2_50)
% 15.33/2.52      | ~ v1_funct_1(X0_51) ),
% 15.33/2.52      inference(subtyping,[status(esa)],[c_5]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_899,plain,
% 15.33/2.52      ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 15.33/2.52      | v1_funct_2(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51),u1_struct_0(X3_50),u1_struct_0(X1_50)) = iProver_top
% 15.33/2.52      | m1_pre_topc(X0_50,X2_50) != iProver_top
% 15.33/2.52      | m1_pre_topc(X3_50,X2_50) != iProver_top
% 15.33/2.52      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 15.33/2.52      | v2_struct_0(X1_50) = iProver_top
% 15.33/2.52      | v2_struct_0(X2_50) = iProver_top
% 15.33/2.52      | v2_pre_topc(X1_50) != iProver_top
% 15.33/2.52      | v2_pre_topc(X2_50) != iProver_top
% 15.33/2.52      | l1_pre_topc(X1_50) != iProver_top
% 15.33/2.52      | l1_pre_topc(X2_50) != iProver_top
% 15.33/2.52      | v1_funct_1(X0_51) != iProver_top ),
% 15.33/2.52      inference(predicate_to_equality,[status(thm)],[c_396]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_8,plain,
% 15.33/2.52      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,X3,X0,k2_tmap_1(X2,X1,X4,X3)),k2_tmap_1(X2,X1,X4,X0))
% 15.33/2.52      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
% 15.33/2.52      | ~ m1_pre_topc(X3,X2)
% 15.33/2.52      | ~ m1_pre_topc(X0,X2)
% 15.33/2.52      | ~ m1_pre_topc(X0,X3)
% 15.33/2.52      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 15.33/2.52      | v2_struct_0(X2)
% 15.33/2.52      | v2_struct_0(X1)
% 15.33/2.52      | v2_struct_0(X3)
% 15.33/2.52      | v2_struct_0(X0)
% 15.33/2.52      | ~ v2_pre_topc(X1)
% 15.33/2.52      | ~ v2_pre_topc(X2)
% 15.33/2.52      | ~ l1_pre_topc(X1)
% 15.33/2.52      | ~ l1_pre_topc(X2)
% 15.33/2.52      | ~ v1_funct_1(X4) ),
% 15.33/2.52      inference(cnf_transformation,[],[f45]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_393,plain,
% 15.33/2.52      ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k3_tmap_1(X2_50,X1_50,X3_50,X0_50,k2_tmap_1(X2_50,X1_50,X0_51,X3_50)),k2_tmap_1(X2_50,X1_50,X0_51,X0_50))
% 15.33/2.52      | ~ v1_funct_2(X0_51,u1_struct_0(X2_50),u1_struct_0(X1_50))
% 15.33/2.52      | ~ m1_pre_topc(X0_50,X3_50)
% 15.33/2.52      | ~ m1_pre_topc(X3_50,X2_50)
% 15.33/2.52      | ~ m1_pre_topc(X0_50,X2_50)
% 15.33/2.52      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50))))
% 15.33/2.52      | v2_struct_0(X1_50)
% 15.33/2.52      | v2_struct_0(X0_50)
% 15.33/2.52      | v2_struct_0(X3_50)
% 15.33/2.52      | v2_struct_0(X2_50)
% 15.33/2.52      | ~ v2_pre_topc(X1_50)
% 15.33/2.52      | ~ v2_pre_topc(X2_50)
% 15.33/2.52      | ~ l1_pre_topc(X1_50)
% 15.33/2.52      | ~ l1_pre_topc(X2_50)
% 15.33/2.52      | ~ v1_funct_1(X0_51) ),
% 15.33/2.52      inference(subtyping,[status(esa)],[c_8]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_902,plain,
% 15.33/2.52      ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k3_tmap_1(X2_50,X1_50,X3_50,X0_50,k2_tmap_1(X2_50,X1_50,X0_51,X3_50)),k2_tmap_1(X2_50,X1_50,X0_51,X0_50)) = iProver_top
% 15.33/2.52      | v1_funct_2(X0_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
% 15.33/2.52      | m1_pre_topc(X0_50,X2_50) != iProver_top
% 15.33/2.52      | m1_pre_topc(X3_50,X2_50) != iProver_top
% 15.33/2.52      | m1_pre_topc(X0_50,X3_50) != iProver_top
% 15.33/2.52      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
% 15.33/2.52      | v2_struct_0(X1_50) = iProver_top
% 15.33/2.52      | v2_struct_0(X0_50) = iProver_top
% 15.33/2.52      | v2_struct_0(X2_50) = iProver_top
% 15.33/2.52      | v2_struct_0(X3_50) = iProver_top
% 15.33/2.52      | v2_pre_topc(X1_50) != iProver_top
% 15.33/2.52      | v2_pre_topc(X2_50) != iProver_top
% 15.33/2.52      | l1_pre_topc(X1_50) != iProver_top
% 15.33/2.52      | l1_pre_topc(X2_50) != iProver_top
% 15.33/2.52      | v1_funct_1(X0_51) != iProver_top ),
% 15.33/2.52      inference(predicate_to_equality,[status(thm)],[c_393]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_1,plain,
% 15.33/2.52      ( ~ r2_funct_2(X0,X1,X2,X3)
% 15.33/2.52      | ~ v1_funct_2(X3,X0,X1)
% 15.33/2.52      | ~ v1_funct_2(X2,X0,X1)
% 15.33/2.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.33/2.52      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.33/2.52      | ~ v1_funct_1(X3)
% 15.33/2.52      | ~ v1_funct_1(X2)
% 15.33/2.52      | X2 = X3 ),
% 15.33/2.52      inference(cnf_transformation,[],[f37]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_400,plain,
% 15.33/2.52      ( ~ r2_funct_2(X0_52,X1_52,X0_51,X1_51)
% 15.33/2.52      | ~ v1_funct_2(X1_51,X0_52,X1_52)
% 15.33/2.52      | ~ v1_funct_2(X0_51,X0_52,X1_52)
% 15.33/2.52      | ~ m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 15.33/2.52      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 15.33/2.52      | ~ v1_funct_1(X0_51)
% 15.33/2.52      | ~ v1_funct_1(X1_51)
% 15.33/2.52      | X0_51 = X1_51 ),
% 15.33/2.52      inference(subtyping,[status(esa)],[c_1]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_895,plain,
% 15.33/2.52      ( X0_51 = X1_51
% 15.33/2.52      | r2_funct_2(X0_52,X1_52,X0_51,X1_51) != iProver_top
% 15.33/2.52      | v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
% 15.33/2.52      | v1_funct_2(X1_51,X0_52,X1_52) != iProver_top
% 15.33/2.52      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 15.33/2.52      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 15.33/2.52      | v1_funct_1(X0_51) != iProver_top
% 15.33/2.52      | v1_funct_1(X1_51) != iProver_top ),
% 15.33/2.52      inference(predicate_to_equality,[status(thm)],[c_400]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_1945,plain,
% 15.33/2.52      ( k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_51) = X1_51
% 15.33/2.52      | r2_funct_2(u1_struct_0(X3_50),u1_struct_0(X1_50),k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_51),X1_51) != iProver_top
% 15.33/2.52      | v1_funct_2(X0_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
% 15.33/2.52      | v1_funct_2(X1_51,u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
% 15.33/2.52      | v1_funct_2(k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_51),u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
% 15.33/2.52      | m1_pre_topc(X2_50,X0_50) != iProver_top
% 15.33/2.52      | m1_pre_topc(X3_50,X0_50) != iProver_top
% 15.33/2.52      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
% 15.33/2.52      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50)))) != iProver_top
% 15.33/2.52      | v2_struct_0(X1_50) = iProver_top
% 15.33/2.52      | v2_struct_0(X0_50) = iProver_top
% 15.33/2.52      | v2_pre_topc(X1_50) != iProver_top
% 15.33/2.52      | v2_pre_topc(X0_50) != iProver_top
% 15.33/2.52      | l1_pre_topc(X1_50) != iProver_top
% 15.33/2.52      | l1_pre_topc(X0_50) != iProver_top
% 15.33/2.52      | v1_funct_1(X0_51) != iProver_top
% 15.33/2.52      | v1_funct_1(X1_51) != iProver_top
% 15.33/2.52      | v1_funct_1(k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_51)) != iProver_top ),
% 15.33/2.52      inference(superposition,[status(thm)],[c_898,c_895]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_4359,plain,
% 15.33/2.52      ( k3_tmap_1(X0_50,X1_50,X2_50,X3_50,k2_tmap_1(X0_50,X1_50,X0_51,X2_50)) = k2_tmap_1(X0_50,X1_50,X0_51,X3_50)
% 15.33/2.52      | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 15.33/2.52      | v1_funct_2(k3_tmap_1(X0_50,X1_50,X2_50,X3_50,k2_tmap_1(X0_50,X1_50,X0_51,X2_50)),u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
% 15.33/2.52      | v1_funct_2(k2_tmap_1(X0_50,X1_50,X0_51,X2_50),u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
% 15.33/2.52      | v1_funct_2(k2_tmap_1(X0_50,X1_50,X0_51,X3_50),u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
% 15.33/2.52      | m1_pre_topc(X2_50,X0_50) != iProver_top
% 15.33/2.52      | m1_pre_topc(X3_50,X0_50) != iProver_top
% 15.33/2.52      | m1_pre_topc(X3_50,X2_50) != iProver_top
% 15.33/2.52      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 15.33/2.52      | m1_subset_1(k2_tmap_1(X0_50,X1_50,X0_51,X2_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
% 15.33/2.52      | m1_subset_1(k2_tmap_1(X0_50,X1_50,X0_51,X3_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50)))) != iProver_top
% 15.33/2.52      | v2_struct_0(X1_50) = iProver_top
% 15.33/2.52      | v2_struct_0(X0_50) = iProver_top
% 15.33/2.52      | v2_struct_0(X3_50) = iProver_top
% 15.33/2.52      | v2_struct_0(X2_50) = iProver_top
% 15.33/2.52      | v2_pre_topc(X1_50) != iProver_top
% 15.33/2.52      | v2_pre_topc(X0_50) != iProver_top
% 15.33/2.52      | l1_pre_topc(X1_50) != iProver_top
% 15.33/2.52      | l1_pre_topc(X0_50) != iProver_top
% 15.33/2.52      | v1_funct_1(X0_51) != iProver_top
% 15.33/2.52      | v1_funct_1(k3_tmap_1(X0_50,X1_50,X2_50,X3_50,k2_tmap_1(X0_50,X1_50,X0_51,X2_50))) != iProver_top
% 15.33/2.52      | v1_funct_1(k2_tmap_1(X0_50,X1_50,X0_51,X2_50)) != iProver_top
% 15.33/2.52      | v1_funct_1(k2_tmap_1(X0_50,X1_50,X0_51,X3_50)) != iProver_top ),
% 15.33/2.52      inference(superposition,[status(thm)],[c_902,c_1945]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_8105,plain,
% 15.33/2.52      ( k3_tmap_1(X0_50,X1_50,X2_50,X3_50,k2_tmap_1(X0_50,X1_50,X0_51,X2_50)) = k2_tmap_1(X0_50,X1_50,X0_51,X3_50)
% 15.33/2.52      | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 15.33/2.52      | v1_funct_2(k2_tmap_1(X0_50,X1_50,X0_51,X3_50),u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
% 15.33/2.52      | v1_funct_2(k2_tmap_1(X0_50,X1_50,X0_51,X2_50),u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
% 15.33/2.52      | m1_pre_topc(X3_50,X2_50) != iProver_top
% 15.33/2.52      | m1_pre_topc(X3_50,X0_50) != iProver_top
% 15.33/2.52      | m1_pre_topc(X2_50,X0_50) != iProver_top
% 15.33/2.52      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 15.33/2.52      | m1_subset_1(k2_tmap_1(X0_50,X1_50,X0_51,X3_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50)))) != iProver_top
% 15.33/2.52      | m1_subset_1(k2_tmap_1(X0_50,X1_50,X0_51,X2_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
% 15.33/2.52      | v2_struct_0(X1_50) = iProver_top
% 15.33/2.52      | v2_struct_0(X0_50) = iProver_top
% 15.33/2.52      | v2_struct_0(X2_50) = iProver_top
% 15.33/2.52      | v2_struct_0(X3_50) = iProver_top
% 15.33/2.52      | v2_pre_topc(X1_50) != iProver_top
% 15.33/2.52      | v2_pre_topc(X0_50) != iProver_top
% 15.33/2.52      | l1_pre_topc(X1_50) != iProver_top
% 15.33/2.52      | l1_pre_topc(X0_50) != iProver_top
% 15.33/2.52      | v1_funct_1(X0_51) != iProver_top
% 15.33/2.52      | v1_funct_1(k3_tmap_1(X0_50,X1_50,X2_50,X3_50,k2_tmap_1(X0_50,X1_50,X0_51,X2_50))) != iProver_top
% 15.33/2.52      | v1_funct_1(k2_tmap_1(X0_50,X1_50,X0_51,X3_50)) != iProver_top
% 15.33/2.52      | v1_funct_1(k2_tmap_1(X0_50,X1_50,X0_51,X2_50)) != iProver_top ),
% 15.33/2.52      inference(superposition,[status(thm)],[c_899,c_4359]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_21644,plain,
% 15.33/2.52      ( k3_tmap_1(sK0,sK1,X0_50,sK2,k2_tmap_1(sK0,sK1,sK4,X0_50)) = k2_tmap_1(sK0,sK1,sK4,sK2)
% 15.33/2.52      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,X0_50),u1_struct_0(X0_50),u1_struct_0(sK1)) != iProver_top
% 15.33/2.52      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.33/2.52      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 15.33/2.52      | m1_pre_topc(X0_50,sK0) != iProver_top
% 15.33/2.52      | m1_pre_topc(sK2,X0_50) != iProver_top
% 15.33/2.52      | m1_pre_topc(sK2,sK0) != iProver_top
% 15.33/2.52      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,X0_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(sK1)))) != iProver_top
% 15.33/2.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 15.33/2.52      | v2_struct_0(X0_50) = iProver_top
% 15.33/2.52      | v2_struct_0(sK0) = iProver_top
% 15.33/2.52      | v2_struct_0(sK1) = iProver_top
% 15.33/2.52      | v2_struct_0(sK2) = iProver_top
% 15.33/2.52      | v2_pre_topc(sK0) != iProver_top
% 15.33/2.52      | v2_pre_topc(sK1) != iProver_top
% 15.33/2.52      | l1_pre_topc(sK0) != iProver_top
% 15.33/2.52      | l1_pre_topc(sK1) != iProver_top
% 15.33/2.52      | v1_funct_1(k3_tmap_1(sK0,sK1,X0_50,sK2,k2_tmap_1(sK0,sK1,sK4,X0_50))) != iProver_top
% 15.33/2.52      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,X0_50)) != iProver_top
% 15.33/2.52      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) != iProver_top
% 15.33/2.52      | v1_funct_1(sK4) != iProver_top ),
% 15.33/2.52      inference(superposition,[status(thm)],[c_2544,c_8105]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_23,negated_conjecture,
% 15.33/2.52      ( ~ v2_struct_0(sK2) ),
% 15.33/2.52      inference(cnf_transformation,[],[f54]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_36,plain,
% 15.33/2.52      ( v2_struct_0(sK2) != iProver_top ),
% 15.33/2.52      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_2141,plain,
% 15.33/2.52      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
% 15.33/2.52      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 15.33/2.52      | m1_pre_topc(sK0,sK0) != iProver_top
% 15.33/2.52      | m1_pre_topc(sK2,sK0) != iProver_top
% 15.33/2.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 15.33/2.52      | v2_struct_0(sK0) = iProver_top
% 15.33/2.52      | v2_struct_0(sK1) = iProver_top
% 15.33/2.52      | v2_pre_topc(sK0) != iProver_top
% 15.33/2.52      | v2_pre_topc(sK1) != iProver_top
% 15.33/2.52      | l1_pre_topc(sK0) != iProver_top
% 15.33/2.52      | l1_pre_topc(sK1) != iProver_top
% 15.33/2.52      | v1_funct_1(sK4) != iProver_top ),
% 15.33/2.52      inference(superposition,[status(thm)],[c_2137,c_899]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_6,plain,
% 15.33/2.52      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 15.33/2.52      | ~ m1_pre_topc(X3,X4)
% 15.33/2.52      | ~ m1_pre_topc(X1,X4)
% 15.33/2.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 15.33/2.52      | v2_struct_0(X4)
% 15.33/2.52      | v2_struct_0(X2)
% 15.33/2.52      | ~ v2_pre_topc(X2)
% 15.33/2.52      | ~ v2_pre_topc(X4)
% 15.33/2.52      | ~ l1_pre_topc(X2)
% 15.33/2.52      | ~ l1_pre_topc(X4)
% 15.33/2.52      | ~ v1_funct_1(X0)
% 15.33/2.52      | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
% 15.33/2.52      inference(cnf_transformation,[],[f41]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_395,plain,
% 15.33/2.52      ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
% 15.33/2.52      | ~ m1_pre_topc(X2_50,X3_50)
% 15.33/2.52      | ~ m1_pre_topc(X0_50,X3_50)
% 15.33/2.52      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 15.33/2.52      | v2_struct_0(X1_50)
% 15.33/2.52      | v2_struct_0(X3_50)
% 15.33/2.52      | ~ v2_pre_topc(X1_50)
% 15.33/2.52      | ~ v2_pre_topc(X3_50)
% 15.33/2.52      | ~ l1_pre_topc(X1_50)
% 15.33/2.52      | ~ l1_pre_topc(X3_50)
% 15.33/2.52      | ~ v1_funct_1(X0_51)
% 15.33/2.52      | v1_funct_1(k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_51)) ),
% 15.33/2.52      inference(subtyping,[status(esa)],[c_6]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_900,plain,
% 15.33/2.52      ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 15.33/2.52      | m1_pre_topc(X0_50,X2_50) != iProver_top
% 15.33/2.52      | m1_pre_topc(X3_50,X2_50) != iProver_top
% 15.33/2.52      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 15.33/2.52      | v2_struct_0(X1_50) = iProver_top
% 15.33/2.52      | v2_struct_0(X2_50) = iProver_top
% 15.33/2.52      | v2_pre_topc(X1_50) != iProver_top
% 15.33/2.52      | v2_pre_topc(X2_50) != iProver_top
% 15.33/2.52      | l1_pre_topc(X1_50) != iProver_top
% 15.33/2.52      | l1_pre_topc(X2_50) != iProver_top
% 15.33/2.52      | v1_funct_1(X0_51) != iProver_top
% 15.33/2.52      | v1_funct_1(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51)) = iProver_top ),
% 15.33/2.52      inference(predicate_to_equality,[status(thm)],[c_395]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_1576,plain,
% 15.33/2.52      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 15.33/2.52      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 15.33/2.52      | m1_pre_topc(sK0,X1_50) != iProver_top
% 15.33/2.52      | v2_struct_0(X1_50) = iProver_top
% 15.33/2.52      | v2_struct_0(sK1) = iProver_top
% 15.33/2.52      | v2_pre_topc(X1_50) != iProver_top
% 15.33/2.52      | v2_pre_topc(sK1) != iProver_top
% 15.33/2.52      | l1_pre_topc(X1_50) != iProver_top
% 15.33/2.52      | l1_pre_topc(sK1) != iProver_top
% 15.33/2.52      | v1_funct_1(k3_tmap_1(X1_50,sK1,sK0,X0_50,sK4)) = iProver_top
% 15.33/2.52      | v1_funct_1(sK4) != iProver_top ),
% 15.33/2.52      inference(superposition,[status(thm)],[c_910,c_900]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_2061,plain,
% 15.33/2.52      ( v1_funct_1(k3_tmap_1(X1_50,sK1,sK0,X0_50,sK4)) = iProver_top
% 15.33/2.52      | v2_pre_topc(X1_50) != iProver_top
% 15.33/2.52      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 15.33/2.52      | m1_pre_topc(sK0,X1_50) != iProver_top
% 15.33/2.52      | v2_struct_0(X1_50) = iProver_top
% 15.33/2.52      | l1_pre_topc(X1_50) != iProver_top ),
% 15.33/2.52      inference(global_propositional_subsumption,
% 15.33/2.52                [status(thm)],
% 15.33/2.52                [c_1576,c_33,c_34,c_35,c_40,c_41]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_2062,plain,
% 15.33/2.52      ( m1_pre_topc(X0_50,X1_50) != iProver_top
% 15.33/2.52      | m1_pre_topc(sK0,X1_50) != iProver_top
% 15.33/2.52      | v2_struct_0(X1_50) = iProver_top
% 15.33/2.52      | v2_pre_topc(X1_50) != iProver_top
% 15.33/2.52      | l1_pre_topc(X1_50) != iProver_top
% 15.33/2.52      | v1_funct_1(k3_tmap_1(X1_50,sK1,sK0,X0_50,sK4)) = iProver_top ),
% 15.33/2.52      inference(renaming,[status(thm)],[c_2061]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_2142,plain,
% 15.33/2.52      ( m1_pre_topc(sK0,sK0) != iProver_top
% 15.33/2.52      | m1_pre_topc(sK2,sK0) != iProver_top
% 15.33/2.52      | v2_struct_0(sK0) = iProver_top
% 15.33/2.52      | v2_pre_topc(sK0) != iProver_top
% 15.33/2.52      | l1_pre_topc(sK0) != iProver_top
% 15.33/2.52      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) = iProver_top ),
% 15.33/2.52      inference(superposition,[status(thm)],[c_2137,c_2062]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_41468,plain,
% 15.33/2.52      ( v2_struct_0(X0_50) = iProver_top
% 15.33/2.52      | m1_pre_topc(sK2,X0_50) != iProver_top
% 15.33/2.52      | m1_pre_topc(X0_50,sK0) != iProver_top
% 15.33/2.52      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,X0_50),u1_struct_0(X0_50),u1_struct_0(sK1)) != iProver_top
% 15.33/2.52      | k3_tmap_1(sK0,sK1,X0_50,sK2,k2_tmap_1(sK0,sK1,sK4,X0_50)) = k2_tmap_1(sK0,sK1,sK4,sK2)
% 15.33/2.52      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,X0_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(sK1)))) != iProver_top
% 15.33/2.52      | v1_funct_1(k3_tmap_1(sK0,sK1,X0_50,sK2,k2_tmap_1(sK0,sK1,sK4,X0_50))) != iProver_top
% 15.33/2.52      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,X0_50)) != iProver_top ),
% 15.33/2.52      inference(global_propositional_subsumption,
% 15.33/2.52                [status(thm)],
% 15.33/2.52                [c_21644,c_30,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_40,
% 15.33/2.52                 c_41,c_42,c_57,c_2141,c_2142]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_41469,plain,
% 15.33/2.52      ( k3_tmap_1(sK0,sK1,X0_50,sK2,k2_tmap_1(sK0,sK1,sK4,X0_50)) = k2_tmap_1(sK0,sK1,sK4,sK2)
% 15.33/2.52      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,X0_50),u1_struct_0(X0_50),u1_struct_0(sK1)) != iProver_top
% 15.33/2.52      | m1_pre_topc(X0_50,sK0) != iProver_top
% 15.33/2.52      | m1_pre_topc(sK2,X0_50) != iProver_top
% 15.33/2.52      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,X0_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(sK1)))) != iProver_top
% 15.33/2.52      | v2_struct_0(X0_50) = iProver_top
% 15.33/2.52      | v1_funct_1(k3_tmap_1(sK0,sK1,X0_50,sK2,k2_tmap_1(sK0,sK1,sK4,X0_50))) != iProver_top
% 15.33/2.52      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,X0_50)) != iProver_top ),
% 15.33/2.52      inference(renaming,[status(thm)],[c_41468]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_41472,plain,
% 15.33/2.52      ( k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) = k2_tmap_1(sK0,sK1,sK4,sK2)
% 15.33/2.52      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 15.33/2.52      | m1_pre_topc(sK3,sK0) != iProver_top
% 15.33/2.52      | m1_pre_topc(sK2,sK3) != iProver_top
% 15.33/2.52      | v2_struct_0(sK3) = iProver_top
% 15.33/2.52      | v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))) != iProver_top
% 15.33/2.52      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
% 15.33/2.52      inference(superposition,[status(thm)],[c_2791,c_41469]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_21,negated_conjecture,
% 15.33/2.52      ( ~ v2_struct_0(sK3) ),
% 15.33/2.52      inference(cnf_transformation,[],[f56]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_38,plain,
% 15.33/2.52      ( v2_struct_0(sK3) != iProver_top ),
% 15.33/2.52      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_16,negated_conjecture,
% 15.33/2.52      ( m1_pre_topc(sK2,sK3) ),
% 15.33/2.52      inference(cnf_transformation,[],[f61]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_43,plain,
% 15.33/2.52      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 15.33/2.52      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_2227,plain,
% 15.33/2.52      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top
% 15.33/2.52      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 15.33/2.52      | m1_pre_topc(sK3,sK0) != iProver_top
% 15.33/2.52      | m1_pre_topc(sK0,sK0) != iProver_top
% 15.33/2.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 15.33/2.52      | v2_struct_0(sK0) = iProver_top
% 15.33/2.52      | v2_struct_0(sK1) = iProver_top
% 15.33/2.52      | v2_pre_topc(sK0) != iProver_top
% 15.33/2.52      | v2_pre_topc(sK1) != iProver_top
% 15.33/2.52      | l1_pre_topc(sK0) != iProver_top
% 15.33/2.52      | l1_pre_topc(sK1) != iProver_top
% 15.33/2.52      | v1_funct_1(sK4) != iProver_top ),
% 15.33/2.52      inference(superposition,[status(thm)],[c_2223,c_899]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_2228,plain,
% 15.33/2.52      ( m1_pre_topc(sK3,sK0) != iProver_top
% 15.33/2.52      | m1_pre_topc(sK0,sK0) != iProver_top
% 15.33/2.52      | v2_struct_0(sK0) = iProver_top
% 15.33/2.52      | v2_pre_topc(sK0) != iProver_top
% 15.33/2.52      | l1_pre_topc(sK0) != iProver_top
% 15.33/2.52      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) = iProver_top ),
% 15.33/2.52      inference(superposition,[status(thm)],[c_2223,c_2062]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_999,plain,
% 15.33/2.52      ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(sK1))
% 15.33/2.52      | ~ m1_pre_topc(X1_50,X2_50)
% 15.33/2.52      | ~ m1_pre_topc(X0_50,X2_50)
% 15.33/2.52      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(sK1))))
% 15.33/2.52      | v2_struct_0(X2_50)
% 15.33/2.52      | v2_struct_0(sK1)
% 15.33/2.52      | ~ v2_pre_topc(X2_50)
% 15.33/2.52      | ~ v2_pre_topc(sK1)
% 15.33/2.52      | ~ l1_pre_topc(X2_50)
% 15.33/2.52      | ~ l1_pre_topc(sK1)
% 15.33/2.52      | ~ v1_funct_1(X0_51)
% 15.33/2.52      | v1_funct_1(k3_tmap_1(X2_50,sK1,X0_50,X1_50,X0_51)) ),
% 15.33/2.52      inference(instantiation,[status(thm)],[c_395]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_3420,plain,
% 15.33/2.52      ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
% 15.33/2.52      | ~ m1_pre_topc(sK3,X0_50)
% 15.33/2.52      | ~ m1_pre_topc(sK2,X0_50)
% 15.33/2.52      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 15.33/2.52      | v2_struct_0(X0_50)
% 15.33/2.52      | v2_struct_0(sK1)
% 15.33/2.52      | ~ v2_pre_topc(X0_50)
% 15.33/2.52      | ~ v2_pre_topc(sK1)
% 15.33/2.52      | ~ l1_pre_topc(X0_50)
% 15.33/2.52      | ~ l1_pre_topc(sK1)
% 15.33/2.52      | v1_funct_1(k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)))
% 15.33/2.52      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) ),
% 15.33/2.52      inference(instantiation,[status(thm)],[c_999]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_3421,plain,
% 15.33/2.52      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 15.33/2.52      | m1_pre_topc(sK3,X0_50) != iProver_top
% 15.33/2.52      | m1_pre_topc(sK2,X0_50) != iProver_top
% 15.33/2.52      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 15.33/2.52      | v2_struct_0(X0_50) = iProver_top
% 15.33/2.52      | v2_struct_0(sK1) = iProver_top
% 15.33/2.52      | v2_pre_topc(X0_50) != iProver_top
% 15.33/2.52      | v2_pre_topc(sK1) != iProver_top
% 15.33/2.52      | l1_pre_topc(X0_50) != iProver_top
% 15.33/2.52      | l1_pre_topc(sK1) != iProver_top
% 15.33/2.52      | v1_funct_1(k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))) = iProver_top
% 15.33/2.52      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
% 15.33/2.52      inference(predicate_to_equality,[status(thm)],[c_3420]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_3423,plain,
% 15.33/2.52      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 15.33/2.52      | m1_pre_topc(sK3,sK0) != iProver_top
% 15.33/2.52      | m1_pre_topc(sK2,sK0) != iProver_top
% 15.33/2.52      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 15.33/2.52      | v2_struct_0(sK0) = iProver_top
% 15.33/2.52      | v2_struct_0(sK1) = iProver_top
% 15.33/2.52      | v2_pre_topc(sK0) != iProver_top
% 15.33/2.52      | v2_pre_topc(sK1) != iProver_top
% 15.33/2.52      | l1_pre_topc(sK0) != iProver_top
% 15.33/2.52      | l1_pre_topc(sK1) != iProver_top
% 15.33/2.52      | v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))) = iProver_top
% 15.33/2.52      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
% 15.33/2.52      inference(instantiation,[status(thm)],[c_3421]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_997,plain,
% 15.33/2.52      ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(sK1))
% 15.33/2.52      | v1_funct_2(k3_tmap_1(X1_50,sK1,X0_50,X2_50,X0_51),u1_struct_0(X2_50),u1_struct_0(sK1))
% 15.33/2.52      | ~ m1_pre_topc(X0_50,X1_50)
% 15.33/2.52      | ~ m1_pre_topc(X2_50,X1_50)
% 15.33/2.52      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(sK1))))
% 15.33/2.52      | v2_struct_0(X1_50)
% 15.33/2.52      | v2_struct_0(sK1)
% 15.33/2.52      | ~ v2_pre_topc(X1_50)
% 15.33/2.52      | ~ v2_pre_topc(sK1)
% 15.33/2.52      | ~ l1_pre_topc(X1_50)
% 15.33/2.52      | ~ l1_pre_topc(sK1)
% 15.33/2.52      | ~ v1_funct_1(X0_51) ),
% 15.33/2.52      inference(instantiation,[status(thm)],[c_396]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_6547,plain,
% 15.33/2.52      ( v1_funct_2(k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK2),u1_struct_0(sK1))
% 15.33/2.52      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
% 15.33/2.52      | ~ m1_pre_topc(sK3,X0_50)
% 15.33/2.52      | ~ m1_pre_topc(sK2,X0_50)
% 15.33/2.52      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 15.33/2.52      | v2_struct_0(X0_50)
% 15.33/2.52      | v2_struct_0(sK1)
% 15.33/2.52      | ~ v2_pre_topc(X0_50)
% 15.33/2.52      | ~ v2_pre_topc(sK1)
% 15.33/2.52      | ~ l1_pre_topc(X0_50)
% 15.33/2.52      | ~ l1_pre_topc(sK1)
% 15.33/2.52      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) ),
% 15.33/2.52      inference(instantiation,[status(thm)],[c_997]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_6552,plain,
% 15.33/2.52      ( v1_funct_2(k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
% 15.33/2.52      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 15.33/2.52      | m1_pre_topc(sK3,X0_50) != iProver_top
% 15.33/2.52      | m1_pre_topc(sK2,X0_50) != iProver_top
% 15.33/2.52      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 15.33/2.52      | v2_struct_0(X0_50) = iProver_top
% 15.33/2.52      | v2_struct_0(sK1) = iProver_top
% 15.33/2.52      | v2_pre_topc(X0_50) != iProver_top
% 15.33/2.52      | v2_pre_topc(sK1) != iProver_top
% 15.33/2.52      | l1_pre_topc(X0_50) != iProver_top
% 15.33/2.52      | l1_pre_topc(sK1) != iProver_top
% 15.33/2.52      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
% 15.33/2.52      inference(predicate_to_equality,[status(thm)],[c_6547]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_6554,plain,
% 15.33/2.52      ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
% 15.33/2.52      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 15.33/2.52      | m1_pre_topc(sK3,sK0) != iProver_top
% 15.33/2.52      | m1_pre_topc(sK2,sK0) != iProver_top
% 15.33/2.52      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 15.33/2.52      | v2_struct_0(sK0) = iProver_top
% 15.33/2.52      | v2_struct_0(sK1) = iProver_top
% 15.33/2.52      | v2_pre_topc(sK0) != iProver_top
% 15.33/2.52      | v2_pre_topc(sK1) != iProver_top
% 15.33/2.52      | l1_pre_topc(sK0) != iProver_top
% 15.33/2.52      | l1_pre_topc(sK1) != iProver_top
% 15.33/2.52      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
% 15.33/2.52      inference(instantiation,[status(thm)],[c_6552]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_996,plain,
% 15.33/2.52      ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(sK1))
% 15.33/2.52      | ~ m1_pre_topc(X1_50,X2_50)
% 15.33/2.52      | ~ m1_pre_topc(X0_50,X2_50)
% 15.33/2.52      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(sK1))))
% 15.33/2.52      | m1_subset_1(k3_tmap_1(X2_50,sK1,X0_50,X1_50,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(sK1))))
% 15.33/2.52      | v2_struct_0(X2_50)
% 15.33/2.52      | v2_struct_0(sK1)
% 15.33/2.52      | ~ v2_pre_topc(X2_50)
% 15.33/2.52      | ~ v2_pre_topc(sK1)
% 15.33/2.52      | ~ l1_pre_topc(X2_50)
% 15.33/2.52      | ~ l1_pre_topc(sK1)
% 15.33/2.52      | ~ v1_funct_1(X0_51) ),
% 15.33/2.52      inference(instantiation,[status(thm)],[c_397]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_12267,plain,
% 15.33/2.52      ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
% 15.33/2.52      | ~ m1_pre_topc(sK3,X0_50)
% 15.33/2.52      | ~ m1_pre_topc(sK2,X0_50)
% 15.33/2.52      | m1_subset_1(k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 15.33/2.52      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 15.33/2.52      | v2_struct_0(X0_50)
% 15.33/2.52      | v2_struct_0(sK1)
% 15.33/2.52      | ~ v2_pre_topc(X0_50)
% 15.33/2.52      | ~ v2_pre_topc(sK1)
% 15.33/2.52      | ~ l1_pre_topc(X0_50)
% 15.33/2.52      | ~ l1_pre_topc(sK1)
% 15.33/2.52      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) ),
% 15.33/2.52      inference(instantiation,[status(thm)],[c_996]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_12268,plain,
% 15.33/2.52      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 15.33/2.52      | m1_pre_topc(sK3,X0_50) != iProver_top
% 15.33/2.52      | m1_pre_topc(sK2,X0_50) != iProver_top
% 15.33/2.52      | m1_subset_1(k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
% 15.33/2.52      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 15.33/2.52      | v2_struct_0(X0_50) = iProver_top
% 15.33/2.52      | v2_struct_0(sK1) = iProver_top
% 15.33/2.52      | v2_pre_topc(X0_50) != iProver_top
% 15.33/2.52      | v2_pre_topc(sK1) != iProver_top
% 15.33/2.52      | l1_pre_topc(X0_50) != iProver_top
% 15.33/2.52      | l1_pre_topc(sK1) != iProver_top
% 15.33/2.52      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
% 15.33/2.52      inference(predicate_to_equality,[status(thm)],[c_12267]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_12270,plain,
% 15.33/2.52      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 15.33/2.52      | m1_pre_topc(sK3,sK0) != iProver_top
% 15.33/2.52      | m1_pre_topc(sK2,sK0) != iProver_top
% 15.33/2.52      | m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
% 15.33/2.52      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 15.33/2.52      | v2_struct_0(sK0) = iProver_top
% 15.33/2.52      | v2_struct_0(sK1) = iProver_top
% 15.33/2.52      | v2_pre_topc(sK0) != iProver_top
% 15.33/2.52      | v2_pre_topc(sK1) != iProver_top
% 15.33/2.52      | l1_pre_topc(sK0) != iProver_top
% 15.33/2.52      | l1_pre_topc(sK1) != iProver_top
% 15.33/2.52      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
% 15.33/2.52      inference(instantiation,[status(thm)],[c_12268]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_3239,plain,
% 15.33/2.52      ( ~ r2_funct_2(X0_52,X1_52,k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),X0_51)
% 15.33/2.52      | ~ v1_funct_2(X0_51,X0_52,X1_52)
% 15.33/2.52      | ~ v1_funct_2(k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),X0_52,X1_52)
% 15.33/2.52      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 15.33/2.52      | ~ m1_subset_1(k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 15.33/2.52      | ~ v1_funct_1(X0_51)
% 15.33/2.52      | ~ v1_funct_1(k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)))
% 15.33/2.52      | k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) = X0_51 ),
% 15.33/2.52      inference(instantiation,[status(thm)],[c_400]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_8190,plain,
% 15.33/2.52      ( ~ r2_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k3_tmap_1(X1_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),X0_51)
% 15.33/2.52      | ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(sK1))
% 15.33/2.52      | ~ v1_funct_2(k3_tmap_1(X1_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(X0_50),u1_struct_0(sK1))
% 15.33/2.52      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(sK1))))
% 15.33/2.52      | ~ m1_subset_1(k3_tmap_1(X1_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(sK1))))
% 15.33/2.52      | ~ v1_funct_1(X0_51)
% 15.33/2.52      | ~ v1_funct_1(k3_tmap_1(X1_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)))
% 15.33/2.52      | k3_tmap_1(X1_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) = X0_51 ),
% 15.33/2.52      inference(instantiation,[status(thm)],[c_3239]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_10897,plain,
% 15.33/2.52      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),X0_51)
% 15.33/2.52      | ~ v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1))
% 15.33/2.52      | ~ v1_funct_2(k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK2),u1_struct_0(sK1))
% 15.33/2.52      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 15.33/2.52      | ~ m1_subset_1(k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 15.33/2.52      | ~ v1_funct_1(X0_51)
% 15.33/2.52      | ~ v1_funct_1(k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)))
% 15.33/2.52      | k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) = X0_51 ),
% 15.33/2.52      inference(instantiation,[status(thm)],[c_8190]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_13522,plain,
% 15.33/2.52      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2))
% 15.33/2.52      | ~ v1_funct_2(k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK2),u1_struct_0(sK1))
% 15.33/2.52      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
% 15.33/2.52      | ~ m1_subset_1(k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 15.33/2.52      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 15.33/2.52      | ~ v1_funct_1(k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)))
% 15.33/2.52      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))
% 15.33/2.52      | k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
% 15.33/2.52      inference(instantiation,[status(thm)],[c_10897]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_13536,plain,
% 15.33/2.52      ( k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) = k2_tmap_1(sK0,sK1,sK4,sK2)
% 15.33/2.52      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2)) != iProver_top
% 15.33/2.52      | v1_funct_2(k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.33/2.52      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.33/2.52      | m1_subset_1(k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.33/2.52      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.33/2.52      | v1_funct_1(k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))) != iProver_top
% 15.33/2.52      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) != iProver_top ),
% 15.33/2.52      inference(predicate_to_equality,[status(thm)],[c_13522]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_13538,plain,
% 15.33/2.52      ( k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) = k2_tmap_1(sK0,sK1,sK4,sK2)
% 15.33/2.52      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2)) != iProver_top
% 15.33/2.52      | v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.33/2.52      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.33/2.52      | m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.33/2.52      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.33/2.52      | v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))) != iProver_top
% 15.33/2.52      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) != iProver_top ),
% 15.33/2.52      inference(instantiation,[status(thm)],[c_13536]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_394,plain,
% 15.33/2.52      ( m1_pre_topc(X0_50,X0_50) | ~ l1_pre_topc(X0_50) ),
% 15.33/2.52      inference(subtyping,[status(esa)],[c_7]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_901,plain,
% 15.33/2.52      ( m1_pre_topc(X0_50,X0_50) = iProver_top
% 15.33/2.52      | l1_pre_topc(X0_50) != iProver_top ),
% 15.33/2.52      inference(predicate_to_equality,[status(thm)],[c_394]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_2077,plain,
% 15.33/2.52      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k3_tmap_1(X0_50,sK1,sK0,X0_50,sK4)
% 15.33/2.52      | m1_pre_topc(X0_50,sK0) != iProver_top
% 15.33/2.52      | m1_pre_topc(sK0,X0_50) != iProver_top
% 15.33/2.52      | v2_struct_0(X0_50) = iProver_top
% 15.33/2.52      | v2_pre_topc(X0_50) != iProver_top
% 15.33/2.52      | l1_pre_topc(X0_50) != iProver_top ),
% 15.33/2.52      inference(superposition,[status(thm)],[c_901,c_2069]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_2394,plain,
% 15.33/2.52      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK0)) = k3_tmap_1(sK0,sK1,sK0,sK0,sK4)
% 15.33/2.52      | m1_pre_topc(sK0,sK0) != iProver_top
% 15.33/2.52      | v2_struct_0(sK0) = iProver_top
% 15.33/2.52      | v2_pre_topc(sK0) != iProver_top
% 15.33/2.52      | l1_pre_topc(sK0) != iProver_top ),
% 15.33/2.52      inference(superposition,[status(thm)],[c_901,c_2077]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_1757,plain,
% 15.33/2.52      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK0)) = k2_tmap_1(sK0,sK1,sK4,sK0)
% 15.33/2.52      | l1_pre_topc(sK0) != iProver_top ),
% 15.33/2.52      inference(superposition,[status(thm)],[c_901,c_1750]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_56,plain,
% 15.33/2.52      ( m1_pre_topc(sK0,sK0) | ~ l1_pre_topc(sK0) ),
% 15.33/2.52      inference(instantiation,[status(thm)],[c_7]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_998,plain,
% 15.33/2.52      ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(sK1))
% 15.33/2.52      | ~ m1_pre_topc(X1_50,X0_50)
% 15.33/2.52      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(sK1))))
% 15.33/2.52      | v2_struct_0(X0_50)
% 15.33/2.52      | v2_struct_0(sK1)
% 15.33/2.52      | ~ v2_pre_topc(X0_50)
% 15.33/2.52      | ~ v2_pre_topc(sK1)
% 15.33/2.52      | ~ l1_pre_topc(X0_50)
% 15.33/2.52      | ~ l1_pre_topc(sK1)
% 15.33/2.52      | ~ v1_funct_1(X0_51)
% 15.33/2.52      | k2_partfun1(u1_struct_0(X0_50),u1_struct_0(sK1),X0_51,u1_struct_0(X1_50)) = k2_tmap_1(X0_50,sK1,X0_51,X1_50) ),
% 15.33/2.52      inference(instantiation,[status(thm)],[c_399]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_1005,plain,
% 15.33/2.52      ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 15.33/2.52      | ~ m1_pre_topc(sK0,sK0)
% 15.33/2.52      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 15.33/2.52      | v2_struct_0(sK0)
% 15.33/2.52      | v2_struct_0(sK1)
% 15.33/2.52      | ~ v2_pre_topc(sK0)
% 15.33/2.52      | ~ v2_pre_topc(sK1)
% 15.33/2.52      | ~ l1_pre_topc(sK0)
% 15.33/2.52      | ~ l1_pre_topc(sK1)
% 15.33/2.52      | ~ v1_funct_1(sK4)
% 15.33/2.52      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK0)) = k2_tmap_1(sK0,sK1,sK4,sK0) ),
% 15.33/2.52      inference(instantiation,[status(thm)],[c_998]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_2134,plain,
% 15.33/2.52      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK0)) = k2_tmap_1(sK0,sK1,sK4,sK0) ),
% 15.33/2.52      inference(global_propositional_subsumption,
% 15.33/2.52                [status(thm)],
% 15.33/2.52                [c_1757,c_29,c_28,c_27,c_26,c_25,c_24,c_19,c_18,c_17,
% 15.33/2.52                 c_56,c_1005]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_2395,plain,
% 15.33/2.52      ( k3_tmap_1(sK0,sK1,sK0,sK0,sK4) = k2_tmap_1(sK0,sK1,sK4,sK0)
% 15.33/2.52      | m1_pre_topc(sK0,sK0) != iProver_top
% 15.33/2.52      | v2_struct_0(sK0) = iProver_top
% 15.33/2.52      | v2_pre_topc(sK0) != iProver_top
% 15.33/2.52      | l1_pre_topc(sK0) != iProver_top ),
% 15.33/2.52      inference(light_normalisation,[status(thm)],[c_2394,c_2134]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_2694,plain,
% 15.33/2.52      ( k3_tmap_1(sK0,sK1,sK0,sK0,sK4) = k2_tmap_1(sK0,sK1,sK4,sK0) ),
% 15.33/2.52      inference(global_propositional_subsumption,
% 15.33/2.52                [status(thm)],
% 15.33/2.52                [c_2395,c_30,c_31,c_32,c_57]) ).
% 15.33/2.52  
% 15.33/2.52  cnf(c_2697,plain,
% 15.33/2.52      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 15.33/2.52      | m1_pre_topc(sK0,sK0) != iProver_top
% 15.33/2.52      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top
% 15.33/2.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 15.33/2.52      | v2_struct_0(sK0) = iProver_top
% 15.33/2.52      | v2_struct_0(sK1) = iProver_top
% 15.33/2.53      | v2_pre_topc(sK0) != iProver_top
% 15.33/2.53      | v2_pre_topc(sK1) != iProver_top
% 15.33/2.53      | l1_pre_topc(sK0) != iProver_top
% 15.33/2.53      | l1_pre_topc(sK1) != iProver_top
% 15.33/2.53      | v1_funct_1(sK4) != iProver_top ),
% 15.33/2.53      inference(superposition,[status(thm)],[c_2694,c_898]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_4609,plain,
% 15.33/2.53      ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 15.33/2.53      inference(global_propositional_subsumption,
% 15.33/2.53                [status(thm)],
% 15.33/2.53                [c_2697,c_30,c_31,c_32,c_33,c_34,c_35,c_40,c_41,c_42,
% 15.33/2.53                 c_57]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_4613,plain,
% 15.33/2.53      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK0),u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK0,X0_50,k2_tmap_1(sK0,sK1,sK4,sK0))
% 15.33/2.53      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK0),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 15.33/2.53      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 15.33/2.53      | m1_pre_topc(X0_50,sK0) != iProver_top
% 15.33/2.53      | m1_pre_topc(sK0,X1_50) != iProver_top
% 15.33/2.53      | v2_struct_0(X1_50) = iProver_top
% 15.33/2.53      | v2_struct_0(sK1) = iProver_top
% 15.33/2.53      | v2_pre_topc(X1_50) != iProver_top
% 15.33/2.53      | v2_pre_topc(sK1) != iProver_top
% 15.33/2.53      | l1_pre_topc(X1_50) != iProver_top
% 15.33/2.53      | l1_pre_topc(sK1) != iProver_top
% 15.33/2.53      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK0)) != iProver_top ),
% 15.33/2.53      inference(superposition,[status(thm)],[c_4609,c_897]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_2698,plain,
% 15.33/2.53      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK0),u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top
% 15.33/2.53      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 15.33/2.53      | m1_pre_topc(sK0,sK0) != iProver_top
% 15.33/2.53      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 15.33/2.53      | v2_struct_0(sK0) = iProver_top
% 15.33/2.53      | v2_struct_0(sK1) = iProver_top
% 15.33/2.53      | v2_pre_topc(sK0) != iProver_top
% 15.33/2.53      | v2_pre_topc(sK1) != iProver_top
% 15.33/2.53      | l1_pre_topc(sK0) != iProver_top
% 15.33/2.53      | l1_pre_topc(sK1) != iProver_top
% 15.33/2.53      | v1_funct_1(sK4) != iProver_top ),
% 15.33/2.53      inference(superposition,[status(thm)],[c_2694,c_899]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_2699,plain,
% 15.33/2.53      ( m1_pre_topc(sK0,sK0) != iProver_top
% 15.33/2.53      | v2_struct_0(sK0) = iProver_top
% 15.33/2.53      | v2_pre_topc(sK0) != iProver_top
% 15.33/2.53      | l1_pre_topc(sK0) != iProver_top
% 15.33/2.53      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK0)) = iProver_top ),
% 15.33/2.53      inference(superposition,[status(thm)],[c_2694,c_2062]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_5678,plain,
% 15.33/2.53      ( v2_pre_topc(X1_50) != iProver_top
% 15.33/2.53      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK0),u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK0,X0_50,k2_tmap_1(sK0,sK1,sK4,sK0))
% 15.33/2.53      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 15.33/2.53      | m1_pre_topc(X0_50,sK0) != iProver_top
% 15.33/2.53      | m1_pre_topc(sK0,X1_50) != iProver_top
% 15.33/2.53      | v2_struct_0(X1_50) = iProver_top
% 15.33/2.53      | l1_pre_topc(X1_50) != iProver_top ),
% 15.33/2.53      inference(global_propositional_subsumption,
% 15.33/2.53                [status(thm)],
% 15.33/2.53                [c_4613,c_30,c_31,c_32,c_33,c_34,c_35,c_40,c_41,c_42,
% 15.33/2.53                 c_57,c_2698,c_2699]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_5679,plain,
% 15.33/2.53      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK0),u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK0,X0_50,k2_tmap_1(sK0,sK1,sK4,sK0))
% 15.33/2.53      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 15.33/2.53      | m1_pre_topc(X0_50,sK0) != iProver_top
% 15.33/2.53      | m1_pre_topc(sK0,X1_50) != iProver_top
% 15.33/2.53      | v2_struct_0(X1_50) = iProver_top
% 15.33/2.53      | v2_pre_topc(X1_50) != iProver_top
% 15.33/2.53      | l1_pre_topc(X1_50) != iProver_top ),
% 15.33/2.53      inference(renaming,[status(thm)],[c_5678]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_5685,plain,
% 15.33/2.53      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK0),u1_struct_0(sK3)) = k3_tmap_1(sK0,sK1,sK0,sK3,k2_tmap_1(sK0,sK1,sK4,sK0))
% 15.33/2.53      | m1_pre_topc(sK3,sK0) != iProver_top
% 15.33/2.53      | m1_pre_topc(sK0,sK0) != iProver_top
% 15.33/2.53      | v2_struct_0(sK0) = iProver_top
% 15.33/2.53      | v2_pre_topc(sK0) != iProver_top
% 15.33/2.53      | l1_pre_topc(sK0) != iProver_top ),
% 15.33/2.53      inference(superposition,[status(thm)],[c_913,c_5679]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_4615,plain,
% 15.33/2.53      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK0),u1_struct_0(X0_50)) = k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),X0_50)
% 15.33/2.53      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK0),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 15.33/2.53      | m1_pre_topc(X0_50,sK0) != iProver_top
% 15.33/2.53      | v2_struct_0(sK0) = iProver_top
% 15.33/2.53      | v2_struct_0(sK1) = iProver_top
% 15.33/2.53      | v2_pre_topc(sK0) != iProver_top
% 15.33/2.53      | v2_pre_topc(sK1) != iProver_top
% 15.33/2.53      | l1_pre_topc(sK0) != iProver_top
% 15.33/2.53      | l1_pre_topc(sK1) != iProver_top
% 15.33/2.53      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK0)) != iProver_top ),
% 15.33/2.53      inference(superposition,[status(thm)],[c_4609,c_896]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_5150,plain,
% 15.33/2.53      ( m1_pre_topc(X0_50,sK0) != iProver_top
% 15.33/2.53      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK0),u1_struct_0(X0_50)) = k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),X0_50) ),
% 15.33/2.53      inference(global_propositional_subsumption,
% 15.33/2.53                [status(thm)],
% 15.33/2.53                [c_4615,c_30,c_31,c_32,c_33,c_34,c_35,c_40,c_41,c_42,
% 15.33/2.53                 c_57,c_2698,c_2699]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_5151,plain,
% 15.33/2.53      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK0),u1_struct_0(X0_50)) = k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),X0_50)
% 15.33/2.53      | m1_pre_topc(X0_50,sK0) != iProver_top ),
% 15.33/2.53      inference(renaming,[status(thm)],[c_5150]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_5156,plain,
% 15.33/2.53      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK0),u1_struct_0(sK3)) = k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),sK3) ),
% 15.33/2.53      inference(superposition,[status(thm)],[c_913,c_5151]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_5689,plain,
% 15.33/2.53      ( k3_tmap_1(sK0,sK1,sK0,sK3,k2_tmap_1(sK0,sK1,sK4,sK0)) = k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),sK3)
% 15.33/2.53      | m1_pre_topc(sK3,sK0) != iProver_top
% 15.33/2.53      | m1_pre_topc(sK0,sK0) != iProver_top
% 15.33/2.53      | v2_struct_0(sK0) = iProver_top
% 15.33/2.53      | v2_pre_topc(sK0) != iProver_top
% 15.33/2.53      | l1_pre_topc(sK0) != iProver_top ),
% 15.33/2.53      inference(light_normalisation,[status(thm)],[c_5685,c_5156]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_6595,plain,
% 15.33/2.53      ( k3_tmap_1(sK0,sK1,sK0,sK3,k2_tmap_1(sK0,sK1,sK4,sK0)) = k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),sK3) ),
% 15.33/2.53      inference(global_propositional_subsumption,
% 15.33/2.53                [status(thm)],
% 15.33/2.53                [c_5689,c_30,c_31,c_32,c_39,c_57]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_8106,plain,
% 15.33/2.53      ( k3_tmap_1(sK0,sK1,sK0,sK3,k2_tmap_1(sK0,sK1,sK4,sK0)) = k2_tmap_1(sK0,sK1,sK4,sK3)
% 15.33/2.53      | v1_funct_2(k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 15.33/2.53      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 15.33/2.53      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK0),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 15.33/2.53      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 15.33/2.53      | m1_pre_topc(sK3,sK0) != iProver_top
% 15.33/2.53      | m1_pre_topc(sK0,sK0) != iProver_top
% 15.33/2.53      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 15.33/2.53      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 15.33/2.53      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 15.33/2.53      | v2_struct_0(sK3) = iProver_top
% 15.33/2.53      | v2_struct_0(sK0) = iProver_top
% 15.33/2.53      | v2_struct_0(sK1) = iProver_top
% 15.33/2.53      | v2_pre_topc(sK0) != iProver_top
% 15.33/2.53      | v2_pre_topc(sK1) != iProver_top
% 15.33/2.53      | l1_pre_topc(sK0) != iProver_top
% 15.33/2.53      | l1_pre_topc(sK1) != iProver_top
% 15.33/2.53      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,k2_tmap_1(sK0,sK1,sK4,sK0))) != iProver_top
% 15.33/2.53      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top
% 15.33/2.53      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK0)) != iProver_top
% 15.33/2.53      | v1_funct_1(sK4) != iProver_top ),
% 15.33/2.53      inference(superposition,[status(thm)],[c_6595,c_4359]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_8269,plain,
% 15.33/2.53      ( k3_tmap_1(sK0,sK1,sK0,sK3,k2_tmap_1(sK0,sK1,sK4,sK0)) = k2_tmap_1(sK0,sK1,sK4,sK3)
% 15.33/2.53      | v1_funct_2(k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 15.33/2.53      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 15.33/2.53      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK0),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 15.33/2.53      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 15.33/2.53      | m1_pre_topc(sK3,sK0) != iProver_top
% 15.33/2.53      | m1_pre_topc(sK0,sK0) != iProver_top
% 15.33/2.53      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 15.33/2.53      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 15.33/2.53      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 15.33/2.53      | v2_struct_0(sK3) = iProver_top
% 15.33/2.53      | v2_struct_0(sK0) = iProver_top
% 15.33/2.53      | v2_struct_0(sK1) = iProver_top
% 15.33/2.53      | v2_pre_topc(sK0) != iProver_top
% 15.33/2.53      | v2_pre_topc(sK1) != iProver_top
% 15.33/2.53      | l1_pre_topc(sK0) != iProver_top
% 15.33/2.53      | l1_pre_topc(sK1) != iProver_top
% 15.33/2.53      | v1_funct_1(k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),sK3)) != iProver_top
% 15.33/2.53      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top
% 15.33/2.53      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK0)) != iProver_top
% 15.33/2.53      | v1_funct_1(sK4) != iProver_top ),
% 15.33/2.53      inference(light_normalisation,[status(thm)],[c_8106,c_6595]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_8270,plain,
% 15.33/2.53      ( k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),sK3) = k2_tmap_1(sK0,sK1,sK4,sK3)
% 15.33/2.53      | v1_funct_2(k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 15.33/2.53      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 15.33/2.53      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK0),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 15.33/2.53      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 15.33/2.53      | m1_pre_topc(sK3,sK0) != iProver_top
% 15.33/2.53      | m1_pre_topc(sK0,sK0) != iProver_top
% 15.33/2.53      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 15.33/2.53      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 15.33/2.53      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 15.33/2.53      | v2_struct_0(sK3) = iProver_top
% 15.33/2.53      | v2_struct_0(sK0) = iProver_top
% 15.33/2.53      | v2_struct_0(sK1) = iProver_top
% 15.33/2.53      | v2_pre_topc(sK0) != iProver_top
% 15.33/2.53      | v2_pre_topc(sK1) != iProver_top
% 15.33/2.53      | l1_pre_topc(sK0) != iProver_top
% 15.33/2.53      | l1_pre_topc(sK1) != iProver_top
% 15.33/2.53      | v1_funct_1(k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),sK3)) != iProver_top
% 15.33/2.53      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top
% 15.33/2.53      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK0)) != iProver_top
% 15.33/2.53      | v1_funct_1(sK4) != iProver_top ),
% 15.33/2.53      inference(demodulation,[status(thm)],[c_8269,c_6595]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_6601,plain,
% 15.33/2.53      ( v1_funct_2(k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),sK3),u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top
% 15.33/2.53      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK0),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 15.33/2.53      | m1_pre_topc(sK3,sK0) != iProver_top
% 15.33/2.53      | m1_pre_topc(sK0,sK0) != iProver_top
% 15.33/2.53      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 15.33/2.53      | v2_struct_0(sK0) = iProver_top
% 15.33/2.53      | v2_struct_0(sK1) = iProver_top
% 15.33/2.53      | v2_pre_topc(sK0) != iProver_top
% 15.33/2.53      | v2_pre_topc(sK1) != iProver_top
% 15.33/2.53      | l1_pre_topc(sK0) != iProver_top
% 15.33/2.53      | l1_pre_topc(sK1) != iProver_top
% 15.33/2.53      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK0)) != iProver_top ),
% 15.33/2.53      inference(superposition,[status(thm)],[c_6595,c_899]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_4614,plain,
% 15.33/2.53      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK0),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 15.33/2.53      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 15.33/2.53      | m1_pre_topc(sK0,X1_50) != iProver_top
% 15.33/2.53      | v2_struct_0(X1_50) = iProver_top
% 15.33/2.53      | v2_struct_0(sK1) = iProver_top
% 15.33/2.53      | v2_pre_topc(X1_50) != iProver_top
% 15.33/2.53      | v2_pre_topc(sK1) != iProver_top
% 15.33/2.53      | l1_pre_topc(X1_50) != iProver_top
% 15.33/2.53      | l1_pre_topc(sK1) != iProver_top
% 15.33/2.53      | v1_funct_1(k3_tmap_1(X1_50,sK1,sK0,X0_50,k2_tmap_1(sK0,sK1,sK4,sK0))) = iProver_top
% 15.33/2.53      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK0)) != iProver_top ),
% 15.33/2.53      inference(superposition,[status(thm)],[c_4609,c_900]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_1943,plain,
% 15.33/2.53      ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 15.33/2.53      | v1_funct_2(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51),u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
% 15.33/2.53      | m1_pre_topc(X0_50,X2_50) != iProver_top
% 15.33/2.53      | m1_pre_topc(X3_50,X2_50) != iProver_top
% 15.33/2.53      | m1_pre_topc(X3_50,X4_50) != iProver_top
% 15.33/2.53      | m1_pre_topc(X5_50,X4_50) != iProver_top
% 15.33/2.53      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 15.33/2.53      | v2_struct_0(X1_50) = iProver_top
% 15.33/2.53      | v2_struct_0(X4_50) = iProver_top
% 15.33/2.53      | v2_struct_0(X2_50) = iProver_top
% 15.33/2.53      | v2_pre_topc(X1_50) != iProver_top
% 15.33/2.53      | v2_pre_topc(X2_50) != iProver_top
% 15.33/2.53      | v2_pre_topc(X4_50) != iProver_top
% 15.33/2.53      | l1_pre_topc(X1_50) != iProver_top
% 15.33/2.53      | l1_pre_topc(X2_50) != iProver_top
% 15.33/2.53      | l1_pre_topc(X4_50) != iProver_top
% 15.33/2.53      | v1_funct_1(X0_51) != iProver_top
% 15.33/2.53      | v1_funct_1(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51)) != iProver_top
% 15.33/2.53      | v1_funct_1(k3_tmap_1(X4_50,X1_50,X3_50,X5_50,k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51))) = iProver_top ),
% 15.33/2.53      inference(superposition,[status(thm)],[c_898,c_900]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_434,plain,
% 15.33/2.53      ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 15.33/2.53      | v1_funct_2(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51),u1_struct_0(X3_50),u1_struct_0(X1_50)) = iProver_top
% 15.33/2.53      | m1_pre_topc(X0_50,X2_50) != iProver_top
% 15.33/2.53      | m1_pre_topc(X3_50,X2_50) != iProver_top
% 15.33/2.53      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 15.33/2.53      | v2_struct_0(X1_50) = iProver_top
% 15.33/2.53      | v2_struct_0(X2_50) = iProver_top
% 15.33/2.53      | v2_pre_topc(X1_50) != iProver_top
% 15.33/2.53      | v2_pre_topc(X2_50) != iProver_top
% 15.33/2.53      | l1_pre_topc(X1_50) != iProver_top
% 15.33/2.53      | l1_pre_topc(X2_50) != iProver_top
% 15.33/2.53      | v1_funct_1(X0_51) != iProver_top ),
% 15.33/2.53      inference(predicate_to_equality,[status(thm)],[c_396]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_437,plain,
% 15.33/2.53      ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 15.33/2.53      | m1_pre_topc(X0_50,X2_50) != iProver_top
% 15.33/2.53      | m1_pre_topc(X3_50,X2_50) != iProver_top
% 15.33/2.53      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 15.33/2.53      | v2_struct_0(X1_50) = iProver_top
% 15.33/2.53      | v2_struct_0(X2_50) = iProver_top
% 15.33/2.53      | v2_pre_topc(X1_50) != iProver_top
% 15.33/2.53      | v2_pre_topc(X2_50) != iProver_top
% 15.33/2.53      | l1_pre_topc(X1_50) != iProver_top
% 15.33/2.53      | l1_pre_topc(X2_50) != iProver_top
% 15.33/2.53      | v1_funct_1(X0_51) != iProver_top
% 15.33/2.53      | v1_funct_1(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51)) = iProver_top ),
% 15.33/2.53      inference(predicate_to_equality,[status(thm)],[c_395]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_3054,plain,
% 15.33/2.53      ( v1_funct_1(X0_51) != iProver_top
% 15.33/2.53      | l1_pre_topc(X4_50) != iProver_top
% 15.33/2.53      | l1_pre_topc(X2_50) != iProver_top
% 15.33/2.53      | l1_pre_topc(X1_50) != iProver_top
% 15.33/2.53      | v2_pre_topc(X4_50) != iProver_top
% 15.33/2.53      | v2_pre_topc(X2_50) != iProver_top
% 15.33/2.53      | v2_pre_topc(X1_50) != iProver_top
% 15.33/2.53      | v2_struct_0(X2_50) = iProver_top
% 15.33/2.53      | v2_struct_0(X4_50) = iProver_top
% 15.33/2.53      | v2_struct_0(X1_50) = iProver_top
% 15.33/2.53      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 15.33/2.53      | m1_pre_topc(X5_50,X4_50) != iProver_top
% 15.33/2.53      | m1_pre_topc(X3_50,X4_50) != iProver_top
% 15.33/2.53      | m1_pre_topc(X3_50,X2_50) != iProver_top
% 15.33/2.53      | m1_pre_topc(X0_50,X2_50) != iProver_top
% 15.33/2.53      | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 15.33/2.53      | v1_funct_1(k3_tmap_1(X4_50,X1_50,X3_50,X5_50,k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51))) = iProver_top ),
% 15.33/2.53      inference(global_propositional_subsumption,
% 15.33/2.53                [status(thm)],
% 15.33/2.53                [c_1943,c_434,c_437]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_3055,plain,
% 15.33/2.53      ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 15.33/2.53      | m1_pre_topc(X0_50,X2_50) != iProver_top
% 15.33/2.53      | m1_pre_topc(X3_50,X2_50) != iProver_top
% 15.33/2.53      | m1_pre_topc(X3_50,X4_50) != iProver_top
% 15.33/2.53      | m1_pre_topc(X5_50,X4_50) != iProver_top
% 15.33/2.53      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 15.33/2.53      | v2_struct_0(X1_50) = iProver_top
% 15.33/2.53      | v2_struct_0(X4_50) = iProver_top
% 15.33/2.53      | v2_struct_0(X2_50) = iProver_top
% 15.33/2.53      | v2_pre_topc(X1_50) != iProver_top
% 15.33/2.53      | v2_pre_topc(X2_50) != iProver_top
% 15.33/2.53      | v2_pre_topc(X4_50) != iProver_top
% 15.33/2.53      | l1_pre_topc(X1_50) != iProver_top
% 15.33/2.53      | l1_pre_topc(X2_50) != iProver_top
% 15.33/2.53      | l1_pre_topc(X4_50) != iProver_top
% 15.33/2.53      | v1_funct_1(X0_51) != iProver_top
% 15.33/2.53      | v1_funct_1(k3_tmap_1(X4_50,X1_50,X3_50,X5_50,k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51))) = iProver_top ),
% 15.33/2.53      inference(renaming,[status(thm)],[c_3054]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_3060,plain,
% 15.33/2.53      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 15.33/2.53      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 15.33/2.53      | m1_pre_topc(sK0,X1_50) != iProver_top
% 15.33/2.53      | m1_pre_topc(sK0,sK0) != iProver_top
% 15.33/2.53      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 15.33/2.53      | v2_struct_0(X1_50) = iProver_top
% 15.33/2.53      | v2_struct_0(sK0) = iProver_top
% 15.33/2.53      | v2_struct_0(sK1) = iProver_top
% 15.33/2.53      | v2_pre_topc(X1_50) != iProver_top
% 15.33/2.53      | v2_pre_topc(sK0) != iProver_top
% 15.33/2.53      | v2_pre_topc(sK1) != iProver_top
% 15.33/2.53      | l1_pre_topc(X1_50) != iProver_top
% 15.33/2.53      | l1_pre_topc(sK0) != iProver_top
% 15.33/2.53      | l1_pre_topc(sK1) != iProver_top
% 15.33/2.53      | v1_funct_1(k3_tmap_1(X1_50,sK1,sK0,X0_50,k2_tmap_1(sK0,sK1,sK4,sK0))) = iProver_top
% 15.33/2.53      | v1_funct_1(sK4) != iProver_top ),
% 15.33/2.53      inference(superposition,[status(thm)],[c_2694,c_3055]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_5143,plain,
% 15.33/2.53      ( v1_funct_1(k3_tmap_1(X1_50,sK1,sK0,X0_50,k2_tmap_1(sK0,sK1,sK4,sK0))) = iProver_top
% 15.33/2.53      | v2_pre_topc(X1_50) != iProver_top
% 15.33/2.53      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 15.33/2.53      | m1_pre_topc(sK0,X1_50) != iProver_top
% 15.33/2.53      | v2_struct_0(X1_50) = iProver_top
% 15.33/2.53      | l1_pre_topc(X1_50) != iProver_top ),
% 15.33/2.53      inference(global_propositional_subsumption,
% 15.33/2.53                [status(thm)],
% 15.33/2.53                [c_4614,c_30,c_31,c_32,c_33,c_34,c_35,c_40,c_41,c_42,
% 15.33/2.53                 c_57,c_3060]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_5144,plain,
% 15.33/2.53      ( m1_pre_topc(X0_50,X1_50) != iProver_top
% 15.33/2.53      | m1_pre_topc(sK0,X1_50) != iProver_top
% 15.33/2.53      | v2_struct_0(X1_50) = iProver_top
% 15.33/2.53      | v2_pre_topc(X1_50) != iProver_top
% 15.33/2.53      | l1_pre_topc(X1_50) != iProver_top
% 15.33/2.53      | v1_funct_1(k3_tmap_1(X1_50,sK1,sK0,X0_50,k2_tmap_1(sK0,sK1,sK4,sK0))) = iProver_top ),
% 15.33/2.53      inference(renaming,[status(thm)],[c_5143]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_6605,plain,
% 15.33/2.53      ( m1_pre_topc(sK3,sK0) != iProver_top
% 15.33/2.53      | m1_pre_topc(sK0,sK0) != iProver_top
% 15.33/2.53      | v2_struct_0(sK0) = iProver_top
% 15.33/2.53      | v2_pre_topc(sK0) != iProver_top
% 15.33/2.53      | l1_pre_topc(sK0) != iProver_top
% 15.33/2.53      | v1_funct_1(k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),sK3)) = iProver_top ),
% 15.33/2.53      inference(superposition,[status(thm)],[c_6595,c_5144]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_9276,plain,
% 15.33/2.53      ( k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),sK3) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
% 15.33/2.53      inference(global_propositional_subsumption,
% 15.33/2.53                [status(thm)],
% 15.33/2.53                [c_8270,c_30,c_31,c_32,c_33,c_34,c_35,c_38,c_39,c_40,
% 15.33/2.53                 c_41,c_42,c_57,c_2226,c_2227,c_2228,c_2697,c_2698,
% 15.33/2.53                 c_2699,c_6601,c_6605]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_5686,plain,
% 15.33/2.53      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK0),u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK0,sK2,k2_tmap_1(sK0,sK1,sK4,sK0))
% 15.33/2.53      | m1_pre_topc(sK0,sK0) != iProver_top
% 15.33/2.53      | m1_pre_topc(sK2,sK0) != iProver_top
% 15.33/2.53      | v2_struct_0(sK0) = iProver_top
% 15.33/2.53      | v2_pre_topc(sK0) != iProver_top
% 15.33/2.53      | l1_pre_topc(sK0) != iProver_top ),
% 15.33/2.53      inference(superposition,[status(thm)],[c_915,c_5679]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_5157,plain,
% 15.33/2.53      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK0),u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),sK2) ),
% 15.33/2.53      inference(superposition,[status(thm)],[c_915,c_5151]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_5688,plain,
% 15.33/2.53      ( k3_tmap_1(sK0,sK1,sK0,sK2,k2_tmap_1(sK0,sK1,sK4,sK0)) = k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),sK2)
% 15.33/2.53      | m1_pre_topc(sK0,sK0) != iProver_top
% 15.33/2.53      | m1_pre_topc(sK2,sK0) != iProver_top
% 15.33/2.53      | v2_struct_0(sK0) = iProver_top
% 15.33/2.53      | v2_pre_topc(sK0) != iProver_top
% 15.33/2.53      | l1_pre_topc(sK0) != iProver_top ),
% 15.33/2.53      inference(light_normalisation,[status(thm)],[c_5686,c_5157]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_6459,plain,
% 15.33/2.53      ( k3_tmap_1(sK0,sK1,sK0,sK2,k2_tmap_1(sK0,sK1,sK4,sK0)) = k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),sK2) ),
% 15.33/2.53      inference(global_propositional_subsumption,
% 15.33/2.53                [status(thm)],
% 15.33/2.53                [c_5688,c_30,c_31,c_32,c_37,c_57]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_8107,plain,
% 15.33/2.53      ( k3_tmap_1(sK0,sK1,sK0,sK2,k2_tmap_1(sK0,sK1,sK4,sK0)) = k2_tmap_1(sK0,sK1,sK4,sK2)
% 15.33/2.53      | v1_funct_2(k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.33/2.53      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK0),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 15.33/2.53      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.33/2.53      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 15.33/2.53      | m1_pre_topc(sK0,sK0) != iProver_top
% 15.33/2.53      | m1_pre_topc(sK2,sK0) != iProver_top
% 15.33/2.53      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 15.33/2.53      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.33/2.53      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 15.33/2.53      | v2_struct_0(sK0) = iProver_top
% 15.33/2.53      | v2_struct_0(sK1) = iProver_top
% 15.33/2.53      | v2_struct_0(sK2) = iProver_top
% 15.33/2.53      | v2_pre_topc(sK0) != iProver_top
% 15.33/2.53      | v2_pre_topc(sK1) != iProver_top
% 15.33/2.53      | l1_pre_topc(sK0) != iProver_top
% 15.33/2.53      | l1_pre_topc(sK1) != iProver_top
% 15.33/2.53      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k2_tmap_1(sK0,sK1,sK4,sK0))) != iProver_top
% 15.33/2.53      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK0)) != iProver_top
% 15.33/2.53      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) != iProver_top
% 15.33/2.53      | v1_funct_1(sK4) != iProver_top ),
% 15.33/2.53      inference(superposition,[status(thm)],[c_6459,c_4359]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_8267,plain,
% 15.33/2.53      ( k3_tmap_1(sK0,sK1,sK0,sK2,k2_tmap_1(sK0,sK1,sK4,sK0)) = k2_tmap_1(sK0,sK1,sK4,sK2)
% 15.33/2.53      | v1_funct_2(k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.33/2.53      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK0),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 15.33/2.53      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.33/2.53      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 15.33/2.53      | m1_pre_topc(sK0,sK0) != iProver_top
% 15.33/2.53      | m1_pre_topc(sK2,sK0) != iProver_top
% 15.33/2.53      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 15.33/2.53      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.33/2.53      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 15.33/2.53      | v2_struct_0(sK0) = iProver_top
% 15.33/2.53      | v2_struct_0(sK1) = iProver_top
% 15.33/2.53      | v2_struct_0(sK2) = iProver_top
% 15.33/2.53      | v2_pre_topc(sK0) != iProver_top
% 15.33/2.53      | v2_pre_topc(sK1) != iProver_top
% 15.33/2.53      | l1_pre_topc(sK0) != iProver_top
% 15.33/2.53      | l1_pre_topc(sK1) != iProver_top
% 15.33/2.53      | v1_funct_1(k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),sK2)) != iProver_top
% 15.33/2.53      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK0)) != iProver_top
% 15.33/2.53      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) != iProver_top
% 15.33/2.53      | v1_funct_1(sK4) != iProver_top ),
% 15.33/2.53      inference(light_normalisation,[status(thm)],[c_8107,c_6459]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_8268,plain,
% 15.33/2.53      ( k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),sK2) = k2_tmap_1(sK0,sK1,sK4,sK2)
% 15.33/2.53      | v1_funct_2(k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.33/2.53      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK0),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 15.33/2.53      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.33/2.53      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 15.33/2.53      | m1_pre_topc(sK0,sK0) != iProver_top
% 15.33/2.53      | m1_pre_topc(sK2,sK0) != iProver_top
% 15.33/2.53      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 15.33/2.53      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.33/2.53      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 15.33/2.53      | v2_struct_0(sK0) = iProver_top
% 15.33/2.53      | v2_struct_0(sK1) = iProver_top
% 15.33/2.53      | v2_struct_0(sK2) = iProver_top
% 15.33/2.53      | v2_pre_topc(sK0) != iProver_top
% 15.33/2.53      | v2_pre_topc(sK1) != iProver_top
% 15.33/2.53      | l1_pre_topc(sK0) != iProver_top
% 15.33/2.53      | l1_pre_topc(sK1) != iProver_top
% 15.33/2.53      | v1_funct_1(k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),sK2)) != iProver_top
% 15.33/2.53      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK0)) != iProver_top
% 15.33/2.53      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) != iProver_top
% 15.33/2.53      | v1_funct_1(sK4) != iProver_top ),
% 15.33/2.53      inference(demodulation,[status(thm)],[c_8267,c_6459]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_6465,plain,
% 15.33/2.53      ( v1_funct_2(k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
% 15.33/2.53      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK0),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 15.33/2.53      | m1_pre_topc(sK0,sK0) != iProver_top
% 15.33/2.53      | m1_pre_topc(sK2,sK0) != iProver_top
% 15.33/2.53      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 15.33/2.53      | v2_struct_0(sK0) = iProver_top
% 15.33/2.53      | v2_struct_0(sK1) = iProver_top
% 15.33/2.53      | v2_pre_topc(sK0) != iProver_top
% 15.33/2.53      | v2_pre_topc(sK1) != iProver_top
% 15.33/2.53      | l1_pre_topc(sK0) != iProver_top
% 15.33/2.53      | l1_pre_topc(sK1) != iProver_top
% 15.33/2.53      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK0)) != iProver_top ),
% 15.33/2.53      inference(superposition,[status(thm)],[c_6459,c_899]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_6469,plain,
% 15.33/2.53      ( m1_pre_topc(sK0,sK0) != iProver_top
% 15.33/2.53      | m1_pre_topc(sK2,sK0) != iProver_top
% 15.33/2.53      | v2_struct_0(sK0) = iProver_top
% 15.33/2.53      | v2_pre_topc(sK0) != iProver_top
% 15.33/2.53      | l1_pre_topc(sK0) != iProver_top
% 15.33/2.53      | v1_funct_1(k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),sK2)) = iProver_top ),
% 15.33/2.53      inference(superposition,[status(thm)],[c_6459,c_5144]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_9082,plain,
% 15.33/2.53      ( k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),sK2) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
% 15.33/2.53      inference(global_propositional_subsumption,
% 15.33/2.53                [status(thm)],
% 15.33/2.53                [c_8268,c_30,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_40,
% 15.33/2.53                 c_41,c_42,c_57,c_2140,c_2141,c_2142,c_2697,c_2698,
% 15.33/2.53                 c_2699,c_6465,c_6469]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_9100,plain,
% 15.33/2.53      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0_50,sK2,k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),X0_50)),k2_tmap_1(sK0,sK1,sK4,sK2)) = iProver_top
% 15.33/2.53      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK0),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 15.33/2.53      | m1_pre_topc(X0_50,sK0) != iProver_top
% 15.33/2.53      | m1_pre_topc(sK2,X0_50) != iProver_top
% 15.33/2.53      | m1_pre_topc(sK2,sK0) != iProver_top
% 15.33/2.53      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 15.33/2.53      | v2_struct_0(X0_50) = iProver_top
% 15.33/2.53      | v2_struct_0(sK0) = iProver_top
% 15.33/2.53      | v2_struct_0(sK1) = iProver_top
% 15.33/2.53      | v2_struct_0(sK2) = iProver_top
% 15.33/2.53      | v2_pre_topc(sK0) != iProver_top
% 15.33/2.53      | v2_pre_topc(sK1) != iProver_top
% 15.33/2.53      | l1_pre_topc(sK0) != iProver_top
% 15.33/2.53      | l1_pre_topc(sK1) != iProver_top
% 15.33/2.53      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK0)) != iProver_top ),
% 15.33/2.53      inference(superposition,[status(thm)],[c_9082,c_902]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_30344,plain,
% 15.33/2.53      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0_50,sK2,k2_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK4,sK0),X0_50)),k2_tmap_1(sK0,sK1,sK4,sK2)) = iProver_top
% 15.33/2.53      | m1_pre_topc(X0_50,sK0) != iProver_top
% 15.33/2.53      | m1_pre_topc(sK2,X0_50) != iProver_top
% 15.33/2.53      | v2_struct_0(X0_50) = iProver_top ),
% 15.33/2.53      inference(global_propositional_subsumption,
% 15.33/2.53                [status(thm)],
% 15.33/2.53                [c_9100,c_30,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_40,
% 15.33/2.53                 c_41,c_42,c_57,c_2697,c_2698,c_2699]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_30351,plain,
% 15.33/2.53      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2)) = iProver_top
% 15.33/2.53      | m1_pre_topc(sK3,sK0) != iProver_top
% 15.33/2.53      | m1_pre_topc(sK2,sK3) != iProver_top
% 15.33/2.53      | v2_struct_0(sK3) = iProver_top ),
% 15.33/2.53      inference(superposition,[status(thm)],[c_9276,c_30344]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_41478,plain,
% 15.33/2.53      ( k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
% 15.33/2.53      inference(global_propositional_subsumption,
% 15.33/2.53                [status(thm)],
% 15.33/2.53                [c_41472,c_30,c_31,c_32,c_33,c_34,c_35,c_37,c_38,c_39,
% 15.33/2.53                 c_40,c_41,c_42,c_43,c_57,c_2140,c_2141,c_2142,c_2226,
% 15.33/2.53                 c_2227,c_2228,c_3423,c_6554,c_12270,c_13538,c_30351]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_10,plain,
% 15.33/2.53      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 15.33/2.53      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 15.33/2.53      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 15.33/2.53      | ~ m1_pre_topc(X4,X5)
% 15.33/2.53      | ~ m1_pre_topc(X4,X0)
% 15.33/2.53      | ~ m1_pre_topc(X0,X5)
% 15.33/2.53      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 15.33/2.53      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 15.33/2.53      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 15.33/2.53      | v2_struct_0(X5)
% 15.33/2.53      | v2_struct_0(X1)
% 15.33/2.53      | v2_struct_0(X4)
% 15.33/2.53      | v2_struct_0(X0)
% 15.33/2.53      | ~ v2_pre_topc(X1)
% 15.33/2.53      | ~ v2_pre_topc(X5)
% 15.33/2.53      | ~ l1_pre_topc(X1)
% 15.33/2.53      | ~ l1_pre_topc(X5)
% 15.33/2.53      | ~ v1_funct_1(X2) ),
% 15.33/2.53      inference(cnf_transformation,[],[f68]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_391,plain,
% 15.33/2.53      ( ~ r1_tmap_1(X0_50,X1_50,X0_51,X1_51)
% 15.33/2.53      | r1_tmap_1(X2_50,X1_50,k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_51),X1_51)
% 15.33/2.53      | ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
% 15.33/2.53      | ~ m1_pre_topc(X2_50,X3_50)
% 15.33/2.53      | ~ m1_pre_topc(X2_50,X0_50)
% 15.33/2.53      | ~ m1_pre_topc(X0_50,X3_50)
% 15.33/2.53      | ~ m1_subset_1(X1_51,u1_struct_0(X2_50))
% 15.33/2.53      | ~ m1_subset_1(X1_51,u1_struct_0(X0_50))
% 15.33/2.53      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 15.33/2.53      | v2_struct_0(X1_50)
% 15.33/2.53      | v2_struct_0(X0_50)
% 15.33/2.53      | v2_struct_0(X3_50)
% 15.33/2.53      | v2_struct_0(X2_50)
% 15.33/2.53      | ~ v2_pre_topc(X1_50)
% 15.33/2.53      | ~ v2_pre_topc(X3_50)
% 15.33/2.53      | ~ l1_pre_topc(X1_50)
% 15.33/2.53      | ~ l1_pre_topc(X3_50)
% 15.33/2.53      | ~ v1_funct_1(X0_51) ),
% 15.33/2.53      inference(subtyping,[status(esa)],[c_10]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_904,plain,
% 15.33/2.53      ( r1_tmap_1(X0_50,X1_50,X0_51,X1_51) != iProver_top
% 15.33/2.53      | r1_tmap_1(X2_50,X1_50,k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_51),X1_51) = iProver_top
% 15.33/2.53      | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 15.33/2.53      | m1_pre_topc(X0_50,X3_50) != iProver_top
% 15.33/2.53      | m1_pre_topc(X2_50,X0_50) != iProver_top
% 15.33/2.53      | m1_pre_topc(X2_50,X3_50) != iProver_top
% 15.33/2.53      | m1_subset_1(X1_51,u1_struct_0(X2_50)) != iProver_top
% 15.33/2.53      | m1_subset_1(X1_51,u1_struct_0(X0_50)) != iProver_top
% 15.33/2.53      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 15.33/2.53      | v2_struct_0(X1_50) = iProver_top
% 15.33/2.53      | v2_struct_0(X0_50) = iProver_top
% 15.33/2.53      | v2_struct_0(X2_50) = iProver_top
% 15.33/2.53      | v2_struct_0(X3_50) = iProver_top
% 15.33/2.53      | v2_pre_topc(X1_50) != iProver_top
% 15.33/2.53      | v2_pre_topc(X3_50) != iProver_top
% 15.33/2.53      | l1_pre_topc(X1_50) != iProver_top
% 15.33/2.53      | l1_pre_topc(X3_50) != iProver_top
% 15.33/2.53      | v1_funct_1(X0_51) != iProver_top ),
% 15.33/2.53      inference(predicate_to_equality,[status(thm)],[c_391]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_41498,plain,
% 15.33/2.53      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0_51) != iProver_top
% 15.33/2.53      | r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),X0_51) = iProver_top
% 15.33/2.53      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 15.33/2.53      | m1_pre_topc(sK3,sK0) != iProver_top
% 15.33/2.53      | m1_pre_topc(sK2,sK3) != iProver_top
% 15.33/2.53      | m1_pre_topc(sK2,sK0) != iProver_top
% 15.33/2.53      | m1_subset_1(X0_51,u1_struct_0(sK3)) != iProver_top
% 15.33/2.53      | m1_subset_1(X0_51,u1_struct_0(sK2)) != iProver_top
% 15.33/2.53      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 15.33/2.53      | v2_struct_0(sK3) = iProver_top
% 15.33/2.53      | v2_struct_0(sK0) = iProver_top
% 15.33/2.53      | v2_struct_0(sK1) = iProver_top
% 15.33/2.53      | v2_struct_0(sK2) = iProver_top
% 15.33/2.53      | v2_pre_topc(sK0) != iProver_top
% 15.33/2.53      | v2_pre_topc(sK1) != iProver_top
% 15.33/2.53      | l1_pre_topc(sK0) != iProver_top
% 15.33/2.53      | l1_pre_topc(sK1) != iProver_top
% 15.33/2.53      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
% 15.33/2.53      inference(superposition,[status(thm)],[c_41478,c_904]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_42936,plain,
% 15.33/2.53      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0_51) != iProver_top
% 15.33/2.53      | r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),X0_51) = iProver_top
% 15.33/2.53      | m1_subset_1(X0_51,u1_struct_0(sK3)) != iProver_top
% 15.33/2.53      | m1_subset_1(X0_51,u1_struct_0(sK2)) != iProver_top ),
% 15.33/2.53      inference(global_propositional_subsumption,
% 15.33/2.53                [status(thm)],
% 15.33/2.53                [c_41498,c_30,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_38,
% 15.33/2.53                 c_39,c_40,c_41,c_42,c_43,c_57,c_2226,c_2227,c_2228]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_42942,plain,
% 15.33/2.53      ( r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6) = iProver_top
% 15.33/2.53      | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
% 15.33/2.53      | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top ),
% 15.33/2.53      inference(superposition,[status(thm)],[c_924,c_42936]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_15,negated_conjecture,
% 15.33/2.53      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 15.33/2.53      inference(cnf_transformation,[],[f62]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_386,negated_conjecture,
% 15.33/2.53      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 15.33/2.53      inference(subtyping,[status(esa)],[c_15]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_908,plain,
% 15.33/2.53      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 15.33/2.53      inference(predicate_to_equality,[status(thm)],[c_386]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_923,plain,
% 15.33/2.53      ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
% 15.33/2.53      inference(light_normalisation,[status(thm)],[c_908,c_388]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_11,negated_conjecture,
% 15.33/2.53      ( ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6) ),
% 15.33/2.53      inference(cnf_transformation,[],[f66]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_47,plain,
% 15.33/2.53      ( r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6) != iProver_top ),
% 15.33/2.53      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_14,negated_conjecture,
% 15.33/2.53      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 15.33/2.53      inference(cnf_transformation,[],[f63]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(c_45,plain,
% 15.33/2.53      ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
% 15.33/2.53      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 15.33/2.53  
% 15.33/2.53  cnf(contradiction,plain,
% 15.33/2.53      ( $false ),
% 15.33/2.53      inference(minisat,[status(thm)],[c_42942,c_923,c_47,c_45]) ).
% 15.33/2.53  
% 15.33/2.53  
% 15.33/2.53  % SZS output end CNFRefutation for theBenchmark.p
% 15.33/2.53  
% 15.33/2.53  ------                               Statistics
% 15.33/2.53  
% 15.33/2.53  ------ General
% 15.33/2.53  
% 15.33/2.53  abstr_ref_over_cycles:                  0
% 15.33/2.53  abstr_ref_under_cycles:                 0
% 15.33/2.53  gc_basic_clause_elim:                   0
% 15.33/2.53  forced_gc_time:                         0
% 15.33/2.53  parsing_time:                           0.014
% 15.33/2.53  unif_index_cands_time:                  0.
% 15.33/2.53  unif_index_add_time:                    0.
% 15.33/2.53  orderings_time:                         0.
% 15.33/2.53  out_proof_time:                         0.024
% 15.33/2.53  total_time:                             1.551
% 15.33/2.53  num_of_symbols:                         54
% 15.33/2.53  num_of_terms:                           16883
% 15.33/2.53  
% 15.33/2.53  ------ Preprocessing
% 15.33/2.53  
% 15.33/2.53  num_of_splits:                          0
% 15.33/2.53  num_of_split_atoms:                     0
% 15.33/2.53  num_of_reused_defs:                     0
% 15.33/2.53  num_eq_ax_congr_red:                    32
% 15.33/2.53  num_of_sem_filtered_clauses:            1
% 15.33/2.53  num_of_subtypes:                        4
% 15.33/2.53  monotx_restored_types:                  0
% 15.33/2.53  sat_num_of_epr_types:                   0
% 15.33/2.53  sat_num_of_non_cyclic_types:            0
% 15.33/2.53  sat_guarded_non_collapsed_types:        1
% 15.33/2.53  num_pure_diseq_elim:                    0
% 15.33/2.53  simp_replaced_by:                       0
% 15.33/2.53  res_preprocessed:                       109
% 15.33/2.53  prep_upred:                             0
% 15.33/2.53  prep_unflattend:                        8
% 15.33/2.53  smt_new_axioms:                         0
% 15.33/2.53  pred_elim_cands:                        9
% 15.33/2.53  pred_elim:                              0
% 15.33/2.53  pred_elim_cl:                           0
% 15.33/2.53  pred_elim_cycles:                       1
% 15.33/2.53  merged_defs:                            0
% 15.33/2.53  merged_defs_ncl:                        0
% 15.33/2.53  bin_hyper_res:                          0
% 15.33/2.53  prep_cycles:                            3
% 15.33/2.53  pred_elim_time:                         0.005
% 15.33/2.53  splitting_time:                         0.
% 15.33/2.53  sem_filter_time:                        0.
% 15.33/2.53  monotx_time:                            0.
% 15.33/2.53  subtype_inf_time:                       0.002
% 15.33/2.53  
% 15.33/2.53  ------ Problem properties
% 15.33/2.53  
% 15.33/2.53  clauses:                                30
% 15.33/2.53  conjectures:                            19
% 15.33/2.53  epr:                                    15
% 15.33/2.53  horn:                                   23
% 15.33/2.53  ground:                                 19
% 15.33/2.53  unary:                                  19
% 15.33/2.53  binary:                                 1
% 15.33/2.53  lits:                                   131
% 15.33/2.53  lits_eq:                                4
% 15.33/2.53  fd_pure:                                0
% 15.33/2.53  fd_pseudo:                              0
% 15.33/2.53  fd_cond:                                0
% 15.33/2.53  fd_pseudo_cond:                         1
% 15.33/2.53  ac_symbols:                             0
% 15.33/2.53  
% 15.33/2.53  ------ Propositional Solver
% 15.33/2.53  
% 15.33/2.53  prop_solver_calls:                      36
% 15.33/2.53  prop_fast_solver_calls:                 7258
% 15.33/2.53  smt_solver_calls:                       0
% 15.33/2.53  smt_fast_solver_calls:                  0
% 15.33/2.53  prop_num_of_clauses:                    9820
% 15.33/2.53  prop_preprocess_simplified:             25002
% 15.33/2.53  prop_fo_subsumed:                       2180
% 15.33/2.53  prop_solver_time:                       0.
% 15.33/2.53  smt_solver_time:                        0.
% 15.33/2.53  smt_fast_solver_time:                   0.
% 15.33/2.53  prop_fast_solver_time:                  0.
% 15.33/2.53  prop_unsat_core_time:                   0.001
% 15.33/2.53  
% 15.33/2.53  ------ QBF
% 15.33/2.53  
% 15.33/2.53  qbf_q_res:                              0
% 15.33/2.53  qbf_num_tautologies:                    0
% 15.33/2.53  qbf_prep_cycles:                        0
% 15.33/2.53  
% 15.33/2.53  ------ BMC1
% 15.33/2.53  
% 15.33/2.53  bmc1_current_bound:                     -1
% 15.33/2.53  bmc1_last_solved_bound:                 -1
% 15.33/2.53  bmc1_unsat_core_size:                   -1
% 15.33/2.53  bmc1_unsat_core_parents_size:           -1
% 15.33/2.53  bmc1_merge_next_fun:                    0
% 15.33/2.53  bmc1_unsat_core_clauses_time:           0.
% 15.33/2.53  
% 15.33/2.53  ------ Instantiation
% 15.33/2.53  
% 15.33/2.53  inst_num_of_clauses:                    4061
% 15.33/2.53  inst_num_in_passive:                    563
% 15.33/2.53  inst_num_in_active:                     2202
% 15.33/2.53  inst_num_in_unprocessed:                1296
% 15.33/2.53  inst_num_of_loops:                      2290
% 15.33/2.53  inst_num_of_learning_restarts:          0
% 15.33/2.53  inst_num_moves_active_passive:          74
% 15.33/2.53  inst_lit_activity:                      0
% 15.33/2.53  inst_lit_activity_moves:                0
% 15.33/2.53  inst_num_tautologies:                   0
% 15.33/2.53  inst_num_prop_implied:                  0
% 15.33/2.53  inst_num_existing_simplified:           0
% 15.33/2.53  inst_num_eq_res_simplified:             0
% 15.33/2.53  inst_num_child_elim:                    0
% 15.33/2.53  inst_num_of_dismatching_blockings:      4330
% 15.33/2.53  inst_num_of_non_proper_insts:           9161
% 15.33/2.53  inst_num_of_duplicates:                 0
% 15.33/2.53  inst_inst_num_from_inst_to_res:         0
% 15.33/2.53  inst_dismatching_checking_time:         0.
% 15.33/2.53  
% 15.33/2.53  ------ Resolution
% 15.33/2.53  
% 15.33/2.53  res_num_of_clauses:                     0
% 15.33/2.53  res_num_in_passive:                     0
% 15.33/2.53  res_num_in_active:                      0
% 15.33/2.53  res_num_of_loops:                       112
% 15.33/2.53  res_forward_subset_subsumed:            383
% 15.33/2.53  res_backward_subset_subsumed:           0
% 15.33/2.53  res_forward_subsumed:                   0
% 15.33/2.53  res_backward_subsumed:                  0
% 15.33/2.53  res_forward_subsumption_resolution:     1
% 15.33/2.53  res_backward_subsumption_resolution:    0
% 15.33/2.53  res_clause_to_clause_subsumption:       1540
% 15.33/2.53  res_orphan_elimination:                 0
% 15.33/2.53  res_tautology_del:                      1399
% 15.33/2.53  res_num_eq_res_simplified:              0
% 15.33/2.53  res_num_sel_changes:                    0
% 15.33/2.53  res_moves_from_active_to_pass:          0
% 15.33/2.53  
% 15.33/2.53  ------ Superposition
% 15.33/2.53  
% 15.33/2.53  sup_time_total:                         0.
% 15.33/2.53  sup_time_generating:                    0.
% 15.33/2.53  sup_time_sim_full:                      0.
% 15.33/2.53  sup_time_sim_immed:                     0.
% 15.33/2.53  
% 15.33/2.53  sup_num_of_clauses:                     486
% 15.33/2.53  sup_num_in_active:                      402
% 15.33/2.53  sup_num_in_passive:                     84
% 15.33/2.53  sup_num_of_loops:                       456
% 15.33/2.53  sup_fw_superposition:                   385
% 15.33/2.53  sup_bw_superposition:                   260
% 15.33/2.53  sup_immediate_simplified:               141
% 15.33/2.53  sup_given_eliminated:                   6
% 15.33/2.53  comparisons_done:                       0
% 15.33/2.53  comparisons_avoided:                    0
% 15.33/2.53  
% 15.33/2.53  ------ Simplifications
% 15.33/2.53  
% 15.33/2.53  
% 15.33/2.53  sim_fw_subset_subsumed:                 23
% 15.33/2.53  sim_bw_subset_subsumed:                 18
% 15.33/2.53  sim_fw_subsumed:                        28
% 15.33/2.53  sim_bw_subsumed:                        8
% 15.33/2.53  sim_fw_subsumption_res:                 0
% 15.33/2.53  sim_bw_subsumption_res:                 0
% 15.33/2.53  sim_tautology_del:                      1
% 15.33/2.53  sim_eq_tautology_del:                   22
% 15.33/2.53  sim_eq_res_simp:                        0
% 15.33/2.53  sim_fw_demodulated:                     34
% 15.33/2.53  sim_bw_demodulated:                     43
% 15.33/2.53  sim_light_normalised:                   148
% 15.33/2.53  sim_joinable_taut:                      0
% 15.33/2.53  sim_joinable_simp:                      0
% 15.33/2.53  sim_ac_normalised:                      0
% 15.33/2.53  sim_smt_subsumption:                    0
% 15.33/2.53  
%------------------------------------------------------------------------------
