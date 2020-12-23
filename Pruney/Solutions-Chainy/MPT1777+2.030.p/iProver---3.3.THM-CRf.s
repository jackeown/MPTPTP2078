%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:31 EST 2020

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.52s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_6742)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
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
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                    & X5 = X6 )
                                 => r1_tmap_1(X3,X1,X4,X5) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
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
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X2))
                                 => ( ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                      & X5 = X6 )
                                   => r1_tmap_1(X3,X1,X4,X5) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f15])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(flattening,[],[f35])).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ~ r1_tmap_1(X3,X1,X4,X5)
          & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
          & X5 = X6
          & m1_subset_1(X6,u1_struct_0(X2)) )
     => ( ~ r1_tmap_1(X3,X1,X4,X5)
        & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK10)
        & sK10 = X5
        & m1_subset_1(sK10,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ~ r1_tmap_1(X3,X1,X4,X5)
              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
              & X5 = X6
              & m1_subset_1(X6,u1_struct_0(X2)) )
          & m1_subset_1(X5,u1_struct_0(X3)) )
     => ( ? [X6] :
            ( ~ r1_tmap_1(X3,X1,X4,sK9)
            & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
            & sK9 = X6
            & m1_subset_1(X6,u1_struct_0(X2)) )
        & m1_subset_1(sK9,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ~ r1_tmap_1(X3,X1,X4,X5)
                  & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                  & X5 = X6
                  & m1_subset_1(X6,u1_struct_0(X2)) )
              & m1_subset_1(X5,u1_struct_0(X3)) )
          & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ~ r1_tmap_1(X3,X1,sK8,X5)
                & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK8),X6)
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(X2)) )
            & m1_subset_1(X5,u1_struct_0(X3)) )
        & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
        & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(sK8,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ~ r1_tmap_1(X3,X1,X4,X5)
                      & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                      & X5 = X6
                      & m1_subset_1(X6,u1_struct_0(X2)) )
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ~ r1_tmap_1(sK7,X1,X4,X5)
                    & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK7,X2,X4),X6)
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(X2)) )
                & m1_subset_1(X5,u1_struct_0(sK7)) )
            & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK7
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(sK7),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK7,X0)
        & ~ v2_struct_0(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ~ r1_tmap_1(X3,X1,X4,X5)
                          & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                          & X5 = X6
                          & m1_subset_1(X6,u1_struct_0(X2)) )
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                  & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ~ r1_tmap_1(X3,X1,X4,X5)
                        & r1_tmap_1(sK6,X1,k3_tmap_1(X0,X1,X3,sK6,X4),X6)
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(sK6)) )
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = X3
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK6,X0)
        & ~ v2_struct_0(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
                            ( ~ r1_tmap_1(X3,sK5,X4,X5)
                            & r1_tmap_1(X2,sK5,k3_tmap_1(X0,sK5,X3,X2,X4),X6)
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK5))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK5))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK5)
        & v2_pre_topc(sK5)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ~ r1_tmap_1(X3,X1,X4,X5)
                                & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                & X5 = X6
                                & m1_subset_1(X6,u1_struct_0(X2)) )
                            & m1_subset_1(X5,u1_struct_0(X3)) )
                        & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(sK4,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK4)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK4)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,
    ( ~ r1_tmap_1(sK7,sK5,sK8,sK9)
    & r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10)
    & sK9 = sK10
    & m1_subset_1(sK10,u1_struct_0(sK6))
    & m1_subset_1(sK9,u1_struct_0(sK7))
    & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5))))
    & v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5))
    & v1_funct_1(sK8)
    & m1_pre_topc(sK7,sK4)
    & ~ v2_struct_0(sK7)
    & m1_pre_topc(sK6,sK4)
    & ~ v2_struct_0(sK6)
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5)
    & ~ v2_struct_0(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9,sK10])],[f36,f63,f62,f61,f60,f59,f58,f57])).

fof(f104,plain,(
    m1_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f64])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
                  | ~ m1_pre_topc(X1,X2) )
                & ( m1_pre_topc(X1,X2)
                  | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f98,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f64])).

fof(f99,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f64])).

fof(f106,plain,(
    m1_pre_topc(sK7,sK4) ),
    inference(cnf_transformation,[],[f64])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f83,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f91,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f110,plain,(
    g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7 ),
    inference(cnf_transformation,[],[f64])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f67,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f114,plain,(
    r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10) ),
    inference(cnf_transformation,[],[f64])).

fof(f113,plain,(
    sK9 = sK10 ),
    inference(cnf_transformation,[],[f64])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f53])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f119,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f88])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f90,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f13,axiom,(
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
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( ( m1_pre_topc(X2,X3)
                          & v1_tsep_1(X2,X3) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( X5 = X6
                                 => ( r1_tmap_1(X3,X1,X4,X5)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(flattening,[],[f33])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( r1_tmap_1(X3,X1,X4,X5)
                                  | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                                & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                  | ~ r1_tmap_1(X3,X1,X4,X5) ) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(nnf_transformation,[],[f34])).

fof(f96,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X5)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | X5 != X6
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ v1_tsep_1(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f56])).

fof(f121,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X6)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ v1_tsep_1(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(equality_resolution,[],[f96])).

fof(f108,plain,(
    v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f64])).

fof(f107,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f64])).

fof(f100,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f64])).

fof(f101,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f64])).

fof(f102,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f64])).

fof(f105,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f64])).

fof(f109,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f64])).

fof(f97,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f64])).

fof(f103,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f64])).

fof(f111,plain,(
    m1_subset_1(sK9,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f64])).

fof(f115,plain,(
    ~ r1_tmap_1(sK7,sK5,sK8,sK9) ),
    inference(cnf_transformation,[],[f64])).

fof(f112,plain,(
    m1_subset_1(sK10,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f64])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X1,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X3,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    inference(rectify,[],[f3])).

fof(f19,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f20,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f37,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
              | ~ r2_hidden(X2,u1_pre_topc(X0))
              | ~ r2_hidden(X1,u1_pre_topc(X0))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f38,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( sP0(X0)
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f20,f37])).

fof(f46,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ? [X3] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              & r1_tarski(X3,u1_pre_topc(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X3] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
                | ~ r1_tarski(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f47,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ? [X3] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              & r1_tarski(X3,u1_pre_topc(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X3] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
                | ~ r1_tarski(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f48,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ? [X1] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
              & r1_tarski(X1,u1_pre_topc(X0))
              & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X2] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
                | ~ r1_tarski(X2,u1_pre_topc(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f47])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r1_tarski(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0))
        & r1_tarski(sK3(X0),u1_pre_topc(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0))
            & r1_tarski(sK3(X0),u1_pre_topc(X0))
            & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X2] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
                | ~ r1_tarski(X2,u1_pre_topc(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f48,f49])).

fof(f75,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_43,negated_conjecture,
    ( m1_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_2901,plain,
    ( m1_pre_topc(sK6,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_27,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2911,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_29,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2909,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X2,X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3111,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | r1_tarski(u1_struct_0(X2),u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2911,c_2909])).

cnf(c_6740,plain,
    ( m1_pre_topc(X0,sK6) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK6)) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2901,c_3111])).

cnf(c_49,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_52,plain,
    ( v2_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_48,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_53,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_7354,plain,
    ( m1_pre_topc(X0,sK6) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6740,c_52,c_53,c_4747,c_4748,c_5642,c_6742])).

cnf(c_41,negated_conjecture,
    ( m1_pre_topc(sK7,sK4) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_2903,plain,
    ( m1_pre_topc(sK7,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_6739,plain,
    ( m1_pre_topc(X0,sK7) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK7)) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2903,c_3111])).

cnf(c_18,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2915,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4748,plain,
    ( l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2901,c_2915])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2928,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5643,plain,
    ( l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2901,c_2928])).

cnf(c_26,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2912,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_37,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_19,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2914,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5330,plain,
    ( m1_pre_topc(X0,sK6) = iProver_top
    | m1_pre_topc(X0,sK7) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_37,c_2914])).

cnf(c_5435,plain,
    ( m1_pre_topc(X0,sK7) != iProver_top
    | m1_pre_topc(X0,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5330,c_53,c_4748])).

cnf(c_5436,plain,
    ( m1_pre_topc(X0,sK6) = iProver_top
    | m1_pre_topc(X0,sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_5435])).

cnf(c_5443,plain,
    ( m1_pre_topc(sK7,sK6) = iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2912,c_5436])).

cnf(c_4747,plain,
    ( l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_2903,c_2915])).

cnf(c_5453,plain,
    ( m1_pre_topc(sK7,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5443,c_53,c_4747])).

cnf(c_6745,plain,
    ( m1_pre_topc(X0,sK7) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK7)) = iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | v2_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5453,c_3111])).

cnf(c_7203,plain,
    ( m1_pre_topc(X0,sK7) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6739,c_52,c_53,c_4748,c_5643,c_6745])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2930,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_7211,plain,
    ( u1_struct_0(X0) = u1_struct_0(sK7)
    | m1_pre_topc(X0,sK7) != iProver_top
    | r1_tarski(u1_struct_0(sK7),u1_struct_0(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7203,c_2930])).

cnf(c_7364,plain,
    ( u1_struct_0(sK7) = u1_struct_0(sK6)
    | m1_pre_topc(sK6,sK7) != iProver_top
    | m1_pre_topc(sK7,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_7354,c_7211])).

cnf(c_21,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_279,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21,c_18])).

cnf(c_280,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_279])).

cnf(c_2893,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_280])).

cnf(c_3906,plain,
    ( m1_pre_topc(X0,sK6) != iProver_top
    | m1_pre_topc(X0,sK7) = iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_37,c_2893])).

cnf(c_4168,plain,
    ( m1_pre_topc(sK6,sK7) = iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2912,c_3906])).

cnf(c_7488,plain,
    ( u1_struct_0(sK7) = u1_struct_0(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7364,c_53,c_4168,c_4747,c_4748,c_5443])).

cnf(c_33,negated_conjecture,
    ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_2907,plain,
    ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_34,negated_conjecture,
    ( sK9 = sK10 ),
    inference(cnf_transformation,[],[f113])).

cnf(c_2970,plain,
    ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK9) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2907,c_34])).

cnf(c_16,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_23,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_25,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_272,plain,
    ( ~ v3_pre_topc(u1_struct_0(X0),X1)
    | v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_23,c_25])).

cnf(c_273,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_272])).

cnf(c_522,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ r2_hidden(X2,u1_pre_topc(X3))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | X1 != X3
    | u1_struct_0(X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_273])).

cnf(c_523,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X1))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_522])).

cnf(c_527,plain,
    ( v1_tsep_1(X0,X1)
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X1))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_523,c_25])).

cnf(c_30,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_tsep_1(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_39,negated_conjecture,
    ( v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_657,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_tsep_1(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X5)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | u1_struct_0(X0) != u1_struct_0(sK7)
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_39])).

cnf(c_658,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK8),X4)
    | r1_tmap_1(X3,X1,sK8,X4)
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ v1_funct_1(sK8)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | u1_struct_0(X3) != u1_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_657])).

cnf(c_40,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_662,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ v1_tsep_1(X0,X3)
    | r1_tmap_1(X3,X1,sK8,X4)
    | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK8),X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | u1_struct_0(X3) != u1_struct_0(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_658,c_40])).

cnf(c_663,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK8),X4)
    | r1_tmap_1(X3,X1,sK8,X4)
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | u1_struct_0(X3) != u1_struct_0(sK7) ),
    inference(renaming,[status(thm)],[c_662])).

cnf(c_706,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK8),X4)
    | r1_tmap_1(X3,X1,sK8,X4)
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | u1_struct_0(X3) != u1_struct_0(sK7) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_663,c_29])).

cnf(c_729,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK8),X4)
    | r1_tmap_1(X3,X1,sK8,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r2_hidden(u1_struct_0(X5),u1_pre_topc(X6))
    | ~ m1_pre_topc(X5,X6)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X6)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X6)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | X0 != X5
    | X3 != X6
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | u1_struct_0(X3) != u1_struct_0(sK7) ),
    inference(resolution_lifted,[status(thm)],[c_527,c_706])).

cnf(c_730,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK8),X4)
    | r1_tmap_1(X3,X1,sK8,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X3))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | u1_struct_0(X3) != u1_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_729])).

cnf(c_774,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK8),X4)
    | r1_tmap_1(X3,X1,sK8,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X3))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | u1_struct_0(X3) != u1_struct_0(sK7) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_730,c_3,c_18])).

cnf(c_2892,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK7)
    | r1_tmap_1(X2,X0,k3_tmap_1(X3,X0,X1,X2,sK8),X4) != iProver_top
    | r1_tmap_1(X1,X0,sK8,X4) = iProver_top
    | m1_subset_1(X4,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | r2_hidden(u1_struct_0(X2),u1_pre_topc(X1)) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X1,X3) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X3) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_774])).

cnf(c_3786,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK7)
    | r1_tmap_1(X1,sK5,k3_tmap_1(X2,sK5,X0,X1,sK8),X3) != iProver_top
    | r1_tmap_1(X0,sK5,sK8,X3) = iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
    | r2_hidden(u1_struct_0(X1),u1_pre_topc(X0)) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v2_pre_topc(sK5) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2892])).

cnf(c_47,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_54,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_46,negated_conjecture,
    ( v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_55,plain,
    ( v2_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_45,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_56,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_3880,plain,
    ( v2_pre_topc(X2) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | r2_hidden(u1_struct_0(X1),u1_pre_topc(X0)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | r1_tmap_1(X0,sK5,sK8,X3) = iProver_top
    | r1_tmap_1(X1,sK5,k3_tmap_1(X2,sK5,X0,X1,sK8),X3) != iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK7)
    | l1_pre_topc(X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3786,c_54,c_55,c_56])).

cnf(c_3881,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK7)
    | r1_tmap_1(X1,sK5,k3_tmap_1(X2,sK5,X0,X1,sK8),X3) != iProver_top
    | r1_tmap_1(X0,sK5,sK8,X3) = iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
    | r2_hidden(u1_struct_0(X1),u1_pre_topc(X0)) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3880])).

cnf(c_3898,plain,
    ( r1_tmap_1(X0,sK5,k3_tmap_1(X1,sK5,sK7,X0,sK8),X2) != iProver_top
    | r1_tmap_1(sK7,sK5,sK8,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) != iProver_top
    | r2_hidden(u1_struct_0(X0),u1_pre_topc(sK7)) != iProver_top
    | m1_pre_topc(X0,sK7) != iProver_top
    | m1_pre_topc(sK7,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK7) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3881])).

cnf(c_42,negated_conjecture,
    ( ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_59,plain,
    ( v2_struct_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_63,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_4255,plain,
    ( v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | m1_pre_topc(sK7,X1) != iProver_top
    | m1_pre_topc(X0,sK7) != iProver_top
    | r2_hidden(u1_struct_0(X0),u1_pre_topc(sK7)) != iProver_top
    | r1_tmap_1(X0,sK5,k3_tmap_1(X1,sK5,sK7,X0,sK8),X2) != iProver_top
    | r1_tmap_1(sK7,sK5,sK8,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK7)) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3898,c_59,c_63])).

cnf(c_4256,plain,
    ( r1_tmap_1(X0,sK5,k3_tmap_1(X1,sK5,sK7,X0,sK8),X2) != iProver_top
    | r1_tmap_1(sK7,sK5,sK8,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK7)) != iProver_top
    | r2_hidden(u1_struct_0(X0),u1_pre_topc(sK7)) != iProver_top
    | m1_pre_topc(X0,sK7) != iProver_top
    | m1_pre_topc(sK7,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_4255])).

cnf(c_4272,plain,
    ( r1_tmap_1(sK7,sK5,sK8,sK9) = iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
    | r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK7)) != iProver_top
    | m1_pre_topc(sK6,sK7) != iProver_top
    | m1_pre_topc(sK7,sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2970,c_4256])).

cnf(c_50,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_51,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_44,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_57,plain,
    ( v2_struct_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_60,plain,
    ( m1_pre_topc(sK7,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK9,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_64,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_32,negated_conjecture,
    ( ~ r1_tmap_1(sK7,sK5,sK8,sK9) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_67,plain,
    ( r1_tmap_1(sK7,sK5,sK8,sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK10,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_2906,plain,
    ( m1_subset_1(sK10,u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_2957,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK6)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2906,c_34])).

cnf(c_4401,plain,
    ( m1_pre_topc(sK6,sK7) != iProver_top
    | r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4272,c_51,c_52,c_53,c_57,c_60,c_64,c_67,c_2957])).

cnf(c_4402,plain,
    ( r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK7)) != iProver_top
    | m1_pre_topc(sK6,sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_4401])).

cnf(c_7492,plain,
    ( r2_hidden(u1_struct_0(sK7),u1_pre_topc(sK7)) != iProver_top
    | m1_pre_topc(sK6,sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7488,c_4402])).

cnf(c_5642,plain,
    ( l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_2903,c_2928])).

cnf(c_15,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_5085,plain,
    ( r2_hidden(u1_struct_0(sK7),u1_pre_topc(sK7))
    | ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(sK7) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_5086,plain,
    ( r2_hidden(u1_struct_0(sK7),u1_pre_topc(sK7)) = iProver_top
    | l1_pre_topc(sK7) != iProver_top
    | v2_pre_topc(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5085])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7492,c_5642,c_5086,c_4748,c_4747,c_4168,c_53,c_52])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:09:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.52/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/0.98  
% 3.52/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.52/0.98  
% 3.52/0.98  ------  iProver source info
% 3.52/0.98  
% 3.52/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.52/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.52/0.98  git: non_committed_changes: false
% 3.52/0.98  git: last_make_outside_of_git: false
% 3.52/0.98  
% 3.52/0.98  ------ 
% 3.52/0.98  
% 3.52/0.98  ------ Input Options
% 3.52/0.98  
% 3.52/0.98  --out_options                           all
% 3.52/0.98  --tptp_safe_out                         true
% 3.52/0.98  --problem_path                          ""
% 3.52/0.98  --include_path                          ""
% 3.52/0.98  --clausifier                            res/vclausify_rel
% 3.52/0.98  --clausifier_options                    --mode clausify
% 3.52/0.98  --stdin                                 false
% 3.52/0.98  --stats_out                             all
% 3.52/0.98  
% 3.52/0.98  ------ General Options
% 3.52/0.98  
% 3.52/0.98  --fof                                   false
% 3.52/0.98  --time_out_real                         305.
% 3.52/0.98  --time_out_virtual                      -1.
% 3.52/0.98  --symbol_type_check                     false
% 3.52/0.98  --clausify_out                          false
% 3.52/0.98  --sig_cnt_out                           false
% 3.52/0.98  --trig_cnt_out                          false
% 3.52/0.98  --trig_cnt_out_tolerance                1.
% 3.52/0.98  --trig_cnt_out_sk_spl                   false
% 3.52/0.98  --abstr_cl_out                          false
% 3.52/0.98  
% 3.52/0.98  ------ Global Options
% 3.52/0.98  
% 3.52/0.98  --schedule                              default
% 3.52/0.98  --add_important_lit                     false
% 3.52/0.98  --prop_solver_per_cl                    1000
% 3.52/0.98  --min_unsat_core                        false
% 3.52/0.98  --soft_assumptions                      false
% 3.52/0.98  --soft_lemma_size                       3
% 3.52/0.98  --prop_impl_unit_size                   0
% 3.52/0.98  --prop_impl_unit                        []
% 3.52/0.98  --share_sel_clauses                     true
% 3.52/0.98  --reset_solvers                         false
% 3.52/0.98  --bc_imp_inh                            [conj_cone]
% 3.52/0.98  --conj_cone_tolerance                   3.
% 3.52/0.98  --extra_neg_conj                        none
% 3.52/0.98  --large_theory_mode                     true
% 3.52/0.98  --prolific_symb_bound                   200
% 3.52/0.98  --lt_threshold                          2000
% 3.52/0.98  --clause_weak_htbl                      true
% 3.52/0.98  --gc_record_bc_elim                     false
% 3.52/0.98  
% 3.52/0.98  ------ Preprocessing Options
% 3.52/0.98  
% 3.52/0.98  --preprocessing_flag                    true
% 3.52/0.98  --time_out_prep_mult                    0.1
% 3.52/0.98  --splitting_mode                        input
% 3.52/0.98  --splitting_grd                         true
% 3.52/0.98  --splitting_cvd                         false
% 3.52/0.98  --splitting_cvd_svl                     false
% 3.52/0.98  --splitting_nvd                         32
% 3.52/0.98  --sub_typing                            true
% 3.52/0.98  --prep_gs_sim                           true
% 3.52/0.98  --prep_unflatten                        true
% 3.52/0.98  --prep_res_sim                          true
% 3.52/0.98  --prep_upred                            true
% 3.52/0.98  --prep_sem_filter                       exhaustive
% 3.52/0.98  --prep_sem_filter_out                   false
% 3.52/0.98  --pred_elim                             true
% 3.52/0.98  --res_sim_input                         true
% 3.52/0.98  --eq_ax_congr_red                       true
% 3.52/0.98  --pure_diseq_elim                       true
% 3.52/0.98  --brand_transform                       false
% 3.52/0.98  --non_eq_to_eq                          false
% 3.52/0.98  --prep_def_merge                        true
% 3.52/0.98  --prep_def_merge_prop_impl              false
% 3.52/0.98  --prep_def_merge_mbd                    true
% 3.52/0.98  --prep_def_merge_tr_red                 false
% 3.52/0.98  --prep_def_merge_tr_cl                  false
% 3.52/0.98  --smt_preprocessing                     true
% 3.52/0.98  --smt_ac_axioms                         fast
% 3.52/0.98  --preprocessed_out                      false
% 3.52/0.98  --preprocessed_stats                    false
% 3.52/0.98  
% 3.52/0.98  ------ Abstraction refinement Options
% 3.52/0.98  
% 3.52/0.98  --abstr_ref                             []
% 3.52/0.98  --abstr_ref_prep                        false
% 3.52/0.98  --abstr_ref_until_sat                   false
% 3.52/0.98  --abstr_ref_sig_restrict                funpre
% 3.52/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.52/0.98  --abstr_ref_under                       []
% 3.52/0.98  
% 3.52/0.98  ------ SAT Options
% 3.52/0.98  
% 3.52/0.98  --sat_mode                              false
% 3.52/0.98  --sat_fm_restart_options                ""
% 3.52/0.98  --sat_gr_def                            false
% 3.52/0.98  --sat_epr_types                         true
% 3.52/0.98  --sat_non_cyclic_types                  false
% 3.52/0.98  --sat_finite_models                     false
% 3.52/0.98  --sat_fm_lemmas                         false
% 3.52/0.98  --sat_fm_prep                           false
% 3.52/0.98  --sat_fm_uc_incr                        true
% 3.52/0.98  --sat_out_model                         small
% 3.52/0.98  --sat_out_clauses                       false
% 3.52/0.98  
% 3.52/0.98  ------ QBF Options
% 3.52/0.98  
% 3.52/0.98  --qbf_mode                              false
% 3.52/0.98  --qbf_elim_univ                         false
% 3.52/0.98  --qbf_dom_inst                          none
% 3.52/0.98  --qbf_dom_pre_inst                      false
% 3.52/0.98  --qbf_sk_in                             false
% 3.52/0.98  --qbf_pred_elim                         true
% 3.52/0.98  --qbf_split                             512
% 3.52/0.98  
% 3.52/0.98  ------ BMC1 Options
% 3.52/0.98  
% 3.52/0.98  --bmc1_incremental                      false
% 3.52/0.98  --bmc1_axioms                           reachable_all
% 3.52/0.98  --bmc1_min_bound                        0
% 3.52/0.98  --bmc1_max_bound                        -1
% 3.52/0.98  --bmc1_max_bound_default                -1
% 3.52/0.98  --bmc1_symbol_reachability              true
% 3.52/0.98  --bmc1_property_lemmas                  false
% 3.52/0.98  --bmc1_k_induction                      false
% 3.52/0.98  --bmc1_non_equiv_states                 false
% 3.52/0.98  --bmc1_deadlock                         false
% 3.52/0.98  --bmc1_ucm                              false
% 3.52/0.98  --bmc1_add_unsat_core                   none
% 3.52/0.98  --bmc1_unsat_core_children              false
% 3.52/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.52/0.98  --bmc1_out_stat                         full
% 3.52/0.98  --bmc1_ground_init                      false
% 3.52/0.98  --bmc1_pre_inst_next_state              false
% 3.52/0.98  --bmc1_pre_inst_state                   false
% 3.52/0.98  --bmc1_pre_inst_reach_state             false
% 3.52/0.98  --bmc1_out_unsat_core                   false
% 3.52/0.98  --bmc1_aig_witness_out                  false
% 3.52/0.98  --bmc1_verbose                          false
% 3.52/0.98  --bmc1_dump_clauses_tptp                false
% 3.52/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.52/0.98  --bmc1_dump_file                        -
% 3.52/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.52/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.52/0.98  --bmc1_ucm_extend_mode                  1
% 3.52/0.98  --bmc1_ucm_init_mode                    2
% 3.52/0.98  --bmc1_ucm_cone_mode                    none
% 3.52/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.52/0.98  --bmc1_ucm_relax_model                  4
% 3.52/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.52/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.52/0.98  --bmc1_ucm_layered_model                none
% 3.52/0.98  --bmc1_ucm_max_lemma_size               10
% 3.52/0.98  
% 3.52/0.98  ------ AIG Options
% 3.52/0.98  
% 3.52/0.98  --aig_mode                              false
% 3.52/0.98  
% 3.52/0.98  ------ Instantiation Options
% 3.52/0.98  
% 3.52/0.98  --instantiation_flag                    true
% 3.52/0.98  --inst_sos_flag                         false
% 3.52/0.98  --inst_sos_phase                        true
% 3.52/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.52/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.52/0.98  --inst_lit_sel_side                     num_symb
% 3.52/0.98  --inst_solver_per_active                1400
% 3.52/0.98  --inst_solver_calls_frac                1.
% 3.52/0.98  --inst_passive_queue_type               priority_queues
% 3.52/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.52/0.98  --inst_passive_queues_freq              [25;2]
% 3.52/0.98  --inst_dismatching                      true
% 3.52/0.98  --inst_eager_unprocessed_to_passive     true
% 3.52/0.98  --inst_prop_sim_given                   true
% 3.52/0.98  --inst_prop_sim_new                     false
% 3.52/0.98  --inst_subs_new                         false
% 3.52/0.98  --inst_eq_res_simp                      false
% 3.52/0.98  --inst_subs_given                       false
% 3.52/0.98  --inst_orphan_elimination               true
% 3.52/0.98  --inst_learning_loop_flag               true
% 3.52/0.98  --inst_learning_start                   3000
% 3.52/0.98  --inst_learning_factor                  2
% 3.52/0.98  --inst_start_prop_sim_after_learn       3
% 3.52/0.98  --inst_sel_renew                        solver
% 3.52/0.98  --inst_lit_activity_flag                true
% 3.52/0.98  --inst_restr_to_given                   false
% 3.52/0.98  --inst_activity_threshold               500
% 3.52/0.98  --inst_out_proof                        true
% 3.52/0.98  
% 3.52/0.98  ------ Resolution Options
% 3.52/0.98  
% 3.52/0.98  --resolution_flag                       true
% 3.52/0.98  --res_lit_sel                           adaptive
% 3.52/0.98  --res_lit_sel_side                      none
% 3.52/0.98  --res_ordering                          kbo
% 3.52/0.98  --res_to_prop_solver                    active
% 3.52/0.98  --res_prop_simpl_new                    false
% 3.52/0.98  --res_prop_simpl_given                  true
% 3.52/0.98  --res_passive_queue_type                priority_queues
% 3.52/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.52/0.98  --res_passive_queues_freq               [15;5]
% 3.52/0.98  --res_forward_subs                      full
% 3.52/0.98  --res_backward_subs                     full
% 3.52/0.98  --res_forward_subs_resolution           true
% 3.52/0.98  --res_backward_subs_resolution          true
% 3.52/0.98  --res_orphan_elimination                true
% 3.52/0.98  --res_time_limit                        2.
% 3.52/0.98  --res_out_proof                         true
% 3.52/0.98  
% 3.52/0.98  ------ Superposition Options
% 3.52/0.98  
% 3.52/0.98  --superposition_flag                    true
% 3.52/0.98  --sup_passive_queue_type                priority_queues
% 3.52/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.52/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.52/0.98  --demod_completeness_check              fast
% 3.52/0.98  --demod_use_ground                      true
% 3.52/0.98  --sup_to_prop_solver                    passive
% 3.52/0.98  --sup_prop_simpl_new                    true
% 3.52/0.98  --sup_prop_simpl_given                  true
% 3.52/0.98  --sup_fun_splitting                     false
% 3.52/0.98  --sup_smt_interval                      50000
% 3.52/0.98  
% 3.52/0.98  ------ Superposition Simplification Setup
% 3.52/0.98  
% 3.52/0.98  --sup_indices_passive                   []
% 3.52/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.52/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.52/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.52/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.52/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.52/0.98  --sup_full_bw                           [BwDemod]
% 3.52/0.98  --sup_immed_triv                        [TrivRules]
% 3.52/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.52/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.52/0.98  --sup_immed_bw_main                     []
% 3.52/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.52/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.52/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.52/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.52/0.98  
% 3.52/0.98  ------ Combination Options
% 3.52/0.98  
% 3.52/0.98  --comb_res_mult                         3
% 3.52/0.98  --comb_sup_mult                         2
% 3.52/0.98  --comb_inst_mult                        10
% 3.52/0.98  
% 3.52/0.98  ------ Debug Options
% 3.52/0.98  
% 3.52/0.98  --dbg_backtrace                         false
% 3.52/0.98  --dbg_dump_prop_clauses                 false
% 3.52/0.98  --dbg_dump_prop_clauses_file            -
% 3.52/0.98  --dbg_out_stat                          false
% 3.52/0.98  ------ Parsing...
% 3.52/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.52/0.98  
% 3.52/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.52/0.98  
% 3.52/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.52/0.98  
% 3.52/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.52/0.98  ------ Proving...
% 3.52/0.98  ------ Problem Properties 
% 3.52/0.98  
% 3.52/0.98  
% 3.52/0.98  clauses                                 42
% 3.52/0.98  conjectures                             17
% 3.52/0.98  EPR                                     19
% 3.52/0.98  Horn                                    34
% 3.52/0.98  unary                                   18
% 3.52/0.98  binary                                  6
% 3.52/0.98  lits                                    134
% 3.52/0.98  lits eq                                 7
% 3.52/0.98  fd_pure                                 0
% 3.52/0.98  fd_pseudo                               0
% 3.52/0.98  fd_cond                                 0
% 3.52/0.98  fd_pseudo_cond                          1
% 3.52/0.98  AC symbols                              0
% 3.52/0.98  
% 3.52/0.98  ------ Schedule dynamic 5 is on 
% 3.52/0.98  
% 3.52/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.52/0.98  
% 3.52/0.98  
% 3.52/0.98  ------ 
% 3.52/0.98  Current options:
% 3.52/0.98  ------ 
% 3.52/0.98  
% 3.52/0.98  ------ Input Options
% 3.52/0.98  
% 3.52/0.98  --out_options                           all
% 3.52/0.98  --tptp_safe_out                         true
% 3.52/0.98  --problem_path                          ""
% 3.52/0.98  --include_path                          ""
% 3.52/0.98  --clausifier                            res/vclausify_rel
% 3.52/0.98  --clausifier_options                    --mode clausify
% 3.52/0.98  --stdin                                 false
% 3.52/0.98  --stats_out                             all
% 3.52/0.98  
% 3.52/0.98  ------ General Options
% 3.52/0.98  
% 3.52/0.98  --fof                                   false
% 3.52/0.98  --time_out_real                         305.
% 3.52/0.98  --time_out_virtual                      -1.
% 3.52/0.98  --symbol_type_check                     false
% 3.52/0.98  --clausify_out                          false
% 3.52/0.98  --sig_cnt_out                           false
% 3.52/0.98  --trig_cnt_out                          false
% 3.52/0.98  --trig_cnt_out_tolerance                1.
% 3.52/0.98  --trig_cnt_out_sk_spl                   false
% 3.52/0.98  --abstr_cl_out                          false
% 3.52/0.98  
% 3.52/0.98  ------ Global Options
% 3.52/0.98  
% 3.52/0.98  --schedule                              default
% 3.52/0.98  --add_important_lit                     false
% 3.52/0.98  --prop_solver_per_cl                    1000
% 3.52/0.98  --min_unsat_core                        false
% 3.52/0.98  --soft_assumptions                      false
% 3.52/0.98  --soft_lemma_size                       3
% 3.52/0.98  --prop_impl_unit_size                   0
% 3.52/0.98  --prop_impl_unit                        []
% 3.52/0.98  --share_sel_clauses                     true
% 3.52/0.98  --reset_solvers                         false
% 3.52/0.98  --bc_imp_inh                            [conj_cone]
% 3.52/0.98  --conj_cone_tolerance                   3.
% 3.52/0.98  --extra_neg_conj                        none
% 3.52/0.98  --large_theory_mode                     true
% 3.52/0.98  --prolific_symb_bound                   200
% 3.52/0.98  --lt_threshold                          2000
% 3.52/0.98  --clause_weak_htbl                      true
% 3.52/0.98  --gc_record_bc_elim                     false
% 3.52/0.98  
% 3.52/0.98  ------ Preprocessing Options
% 3.52/0.98  
% 3.52/0.98  --preprocessing_flag                    true
% 3.52/0.98  --time_out_prep_mult                    0.1
% 3.52/0.98  --splitting_mode                        input
% 3.52/0.98  --splitting_grd                         true
% 3.52/0.98  --splitting_cvd                         false
% 3.52/0.98  --splitting_cvd_svl                     false
% 3.52/0.98  --splitting_nvd                         32
% 3.52/0.98  --sub_typing                            true
% 3.52/0.98  --prep_gs_sim                           true
% 3.52/0.98  --prep_unflatten                        true
% 3.52/0.98  --prep_res_sim                          true
% 3.52/0.98  --prep_upred                            true
% 3.52/0.98  --prep_sem_filter                       exhaustive
% 3.52/0.98  --prep_sem_filter_out                   false
% 3.52/0.98  --pred_elim                             true
% 3.52/0.98  --res_sim_input                         true
% 3.52/0.98  --eq_ax_congr_red                       true
% 3.52/0.98  --pure_diseq_elim                       true
% 3.52/0.98  --brand_transform                       false
% 3.52/0.98  --non_eq_to_eq                          false
% 3.52/0.98  --prep_def_merge                        true
% 3.52/0.98  --prep_def_merge_prop_impl              false
% 3.52/0.98  --prep_def_merge_mbd                    true
% 3.52/0.98  --prep_def_merge_tr_red                 false
% 3.52/0.98  --prep_def_merge_tr_cl                  false
% 3.52/0.98  --smt_preprocessing                     true
% 3.52/0.98  --smt_ac_axioms                         fast
% 3.52/0.98  --preprocessed_out                      false
% 3.52/0.98  --preprocessed_stats                    false
% 3.52/0.98  
% 3.52/0.98  ------ Abstraction refinement Options
% 3.52/0.98  
% 3.52/0.98  --abstr_ref                             []
% 3.52/0.98  --abstr_ref_prep                        false
% 3.52/0.98  --abstr_ref_until_sat                   false
% 3.52/0.98  --abstr_ref_sig_restrict                funpre
% 3.52/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.52/0.98  --abstr_ref_under                       []
% 3.52/0.98  
% 3.52/0.98  ------ SAT Options
% 3.52/0.98  
% 3.52/0.98  --sat_mode                              false
% 3.52/0.98  --sat_fm_restart_options                ""
% 3.52/0.98  --sat_gr_def                            false
% 3.52/0.98  --sat_epr_types                         true
% 3.52/0.98  --sat_non_cyclic_types                  false
% 3.52/0.98  --sat_finite_models                     false
% 3.52/0.98  --sat_fm_lemmas                         false
% 3.52/0.98  --sat_fm_prep                           false
% 3.52/0.98  --sat_fm_uc_incr                        true
% 3.52/0.98  --sat_out_model                         small
% 3.52/0.98  --sat_out_clauses                       false
% 3.52/0.98  
% 3.52/0.98  ------ QBF Options
% 3.52/0.98  
% 3.52/0.98  --qbf_mode                              false
% 3.52/0.98  --qbf_elim_univ                         false
% 3.52/0.98  --qbf_dom_inst                          none
% 3.52/0.98  --qbf_dom_pre_inst                      false
% 3.52/0.98  --qbf_sk_in                             false
% 3.52/0.98  --qbf_pred_elim                         true
% 3.52/0.98  --qbf_split                             512
% 3.52/0.98  
% 3.52/0.98  ------ BMC1 Options
% 3.52/0.98  
% 3.52/0.98  --bmc1_incremental                      false
% 3.52/0.98  --bmc1_axioms                           reachable_all
% 3.52/0.98  --bmc1_min_bound                        0
% 3.52/0.98  --bmc1_max_bound                        -1
% 3.52/0.98  --bmc1_max_bound_default                -1
% 3.52/0.98  --bmc1_symbol_reachability              true
% 3.52/0.98  --bmc1_property_lemmas                  false
% 3.52/0.98  --bmc1_k_induction                      false
% 3.52/0.98  --bmc1_non_equiv_states                 false
% 3.52/0.98  --bmc1_deadlock                         false
% 3.52/0.98  --bmc1_ucm                              false
% 3.52/0.98  --bmc1_add_unsat_core                   none
% 3.52/0.98  --bmc1_unsat_core_children              false
% 3.52/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.52/0.98  --bmc1_out_stat                         full
% 3.52/0.98  --bmc1_ground_init                      false
% 3.52/0.98  --bmc1_pre_inst_next_state              false
% 3.52/0.98  --bmc1_pre_inst_state                   false
% 3.52/0.98  --bmc1_pre_inst_reach_state             false
% 3.52/0.98  --bmc1_out_unsat_core                   false
% 3.52/0.98  --bmc1_aig_witness_out                  false
% 3.52/0.98  --bmc1_verbose                          false
% 3.52/0.98  --bmc1_dump_clauses_tptp                false
% 3.52/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.52/0.98  --bmc1_dump_file                        -
% 3.52/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.52/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.52/0.98  --bmc1_ucm_extend_mode                  1
% 3.52/0.98  --bmc1_ucm_init_mode                    2
% 3.52/0.98  --bmc1_ucm_cone_mode                    none
% 3.52/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.52/0.98  --bmc1_ucm_relax_model                  4
% 3.52/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.52/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.52/0.98  --bmc1_ucm_layered_model                none
% 3.52/0.98  --bmc1_ucm_max_lemma_size               10
% 3.52/0.98  
% 3.52/0.98  ------ AIG Options
% 3.52/0.98  
% 3.52/0.98  --aig_mode                              false
% 3.52/0.98  
% 3.52/0.98  ------ Instantiation Options
% 3.52/0.98  
% 3.52/0.98  --instantiation_flag                    true
% 3.52/0.98  --inst_sos_flag                         false
% 3.52/0.98  --inst_sos_phase                        true
% 3.52/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.52/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.52/0.98  --inst_lit_sel_side                     none
% 3.52/0.98  --inst_solver_per_active                1400
% 3.52/0.98  --inst_solver_calls_frac                1.
% 3.52/0.98  --inst_passive_queue_type               priority_queues
% 3.52/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.52/0.98  --inst_passive_queues_freq              [25;2]
% 3.52/0.98  --inst_dismatching                      true
% 3.52/0.98  --inst_eager_unprocessed_to_passive     true
% 3.52/0.98  --inst_prop_sim_given                   true
% 3.52/0.98  --inst_prop_sim_new                     false
% 3.52/0.98  --inst_subs_new                         false
% 3.52/0.98  --inst_eq_res_simp                      false
% 3.52/0.98  --inst_subs_given                       false
% 3.52/0.98  --inst_orphan_elimination               true
% 3.52/0.98  --inst_learning_loop_flag               true
% 3.52/0.98  --inst_learning_start                   3000
% 3.52/0.98  --inst_learning_factor                  2
% 3.52/0.98  --inst_start_prop_sim_after_learn       3
% 3.52/0.98  --inst_sel_renew                        solver
% 3.52/0.98  --inst_lit_activity_flag                true
% 3.52/0.98  --inst_restr_to_given                   false
% 3.52/0.98  --inst_activity_threshold               500
% 3.52/0.98  --inst_out_proof                        true
% 3.52/0.98  
% 3.52/0.98  ------ Resolution Options
% 3.52/0.98  
% 3.52/0.98  --resolution_flag                       false
% 3.52/0.98  --res_lit_sel                           adaptive
% 3.52/0.98  --res_lit_sel_side                      none
% 3.52/0.98  --res_ordering                          kbo
% 3.52/0.98  --res_to_prop_solver                    active
% 3.52/0.98  --res_prop_simpl_new                    false
% 3.52/0.98  --res_prop_simpl_given                  true
% 3.52/0.98  --res_passive_queue_type                priority_queues
% 3.52/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.52/0.98  --res_passive_queues_freq               [15;5]
% 3.52/0.98  --res_forward_subs                      full
% 3.52/0.98  --res_backward_subs                     full
% 3.52/0.98  --res_forward_subs_resolution           true
% 3.52/0.98  --res_backward_subs_resolution          true
% 3.52/0.98  --res_orphan_elimination                true
% 3.52/0.98  --res_time_limit                        2.
% 3.52/0.98  --res_out_proof                         true
% 3.52/0.98  
% 3.52/0.98  ------ Superposition Options
% 3.52/0.98  
% 3.52/0.98  --superposition_flag                    true
% 3.52/0.98  --sup_passive_queue_type                priority_queues
% 3.52/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.52/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.52/0.98  --demod_completeness_check              fast
% 3.52/0.98  --demod_use_ground                      true
% 3.52/0.98  --sup_to_prop_solver                    passive
% 3.52/0.98  --sup_prop_simpl_new                    true
% 3.52/0.98  --sup_prop_simpl_given                  true
% 3.52/0.98  --sup_fun_splitting                     false
% 3.52/0.98  --sup_smt_interval                      50000
% 3.52/0.98  
% 3.52/0.98  ------ Superposition Simplification Setup
% 3.52/0.98  
% 3.52/0.98  --sup_indices_passive                   []
% 3.52/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.52/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.52/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.52/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.52/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.52/0.98  --sup_full_bw                           [BwDemod]
% 3.52/0.98  --sup_immed_triv                        [TrivRules]
% 3.52/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.52/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.52/0.98  --sup_immed_bw_main                     []
% 3.52/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.52/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.52/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.52/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.52/0.98  
% 3.52/0.98  ------ Combination Options
% 3.52/0.98  
% 3.52/0.98  --comb_res_mult                         3
% 3.52/0.98  --comb_sup_mult                         2
% 3.52/0.98  --comb_inst_mult                        10
% 3.52/0.98  
% 3.52/0.98  ------ Debug Options
% 3.52/0.98  
% 3.52/0.98  --dbg_backtrace                         false
% 3.52/0.98  --dbg_dump_prop_clauses                 false
% 3.52/0.98  --dbg_dump_prop_clauses_file            -
% 3.52/0.98  --dbg_out_stat                          false
% 3.52/0.98  
% 3.52/0.98  
% 3.52/0.98  
% 3.52/0.98  
% 3.52/0.98  ------ Proving...
% 3.52/0.98  
% 3.52/0.98  
% 3.52/0.98  % SZS status Theorem for theBenchmark.p
% 3.52/0.98  
% 3.52/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.52/0.98  
% 3.52/0.98  fof(f14,conjecture,(
% 3.52/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.52/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/0.98  
% 3.52/0.98  fof(f15,negated_conjecture,(
% 3.52/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.52/0.98    inference(negated_conjecture,[],[f14])).
% 3.52/0.98  
% 3.52/0.98  fof(f35,plain,(
% 3.52/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.52/0.98    inference(ennf_transformation,[],[f15])).
% 3.52/0.98  
% 3.52/0.98  fof(f36,plain,(
% 3.52/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.52/0.98    inference(flattening,[],[f35])).
% 3.52/0.98  
% 3.52/0.98  fof(f63,plain,(
% 3.52/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK10) & sK10 = X5 & m1_subset_1(sK10,u1_struct_0(X2)))) )),
% 3.52/0.98    introduced(choice_axiom,[])).
% 3.52/0.98  
% 3.52/0.98  fof(f62,plain,(
% 3.52/0.98    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X3,X1,X4,sK9) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & sK9 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK9,u1_struct_0(X3)))) )),
% 3.52/0.98    introduced(choice_axiom,[])).
% 3.52/0.98  
% 3.52/0.98  fof(f61,plain,(
% 3.52/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,sK8,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK8),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK8,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK8))) )),
% 3.52/0.98    introduced(choice_axiom,[])).
% 3.52/0.98  
% 3.52/0.98  fof(f60,plain,(
% 3.52/0.98    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK7,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK7,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK7))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK7 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK7),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK7,X0) & ~v2_struct_0(sK7))) )),
% 3.52/0.98    introduced(choice_axiom,[])).
% 3.52/0.98  
% 3.52/0.98  fof(f59,plain,(
% 3.52/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(sK6,X1,k3_tmap_1(X0,X1,X3,sK6,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK6))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK6,X0) & ~v2_struct_0(sK6))) )),
% 3.52/0.98    introduced(choice_axiom,[])).
% 3.52/0.98  
% 3.52/0.98  fof(f58,plain,(
% 3.52/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK5,X4,X5) & r1_tmap_1(X2,sK5,k3_tmap_1(X0,sK5,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK5)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK5)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5))) )),
% 3.52/0.98    introduced(choice_axiom,[])).
% 3.52/0.98  
% 3.52/0.98  fof(f57,plain,(
% 3.52/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK4,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK4) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK4) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 3.52/0.98    introduced(choice_axiom,[])).
% 3.52/0.98  
% 3.52/0.98  fof(f64,plain,(
% 3.52/0.98    ((((((~r1_tmap_1(sK7,sK5,sK8,sK9) & r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10) & sK9 = sK10 & m1_subset_1(sK10,u1_struct_0(sK6))) & m1_subset_1(sK9,u1_struct_0(sK7))) & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7 & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) & v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5)) & v1_funct_1(sK8)) & m1_pre_topc(sK7,sK4) & ~v2_struct_0(sK7)) & m1_pre_topc(sK6,sK4) & ~v2_struct_0(sK6)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)),
% 3.52/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9,sK10])],[f36,f63,f62,f61,f60,f59,f58,f57])).
% 3.52/0.98  
% 3.52/0.98  fof(f104,plain,(
% 3.52/0.98    m1_pre_topc(sK6,sK4)),
% 3.52/0.98    inference(cnf_transformation,[],[f64])).
% 3.52/0.98  
% 3.52/0.98  fof(f11,axiom,(
% 3.52/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 3.52/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/0.98  
% 3.52/0.98  fof(f29,plain,(
% 3.52/0.98    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.52/0.98    inference(ennf_transformation,[],[f11])).
% 3.52/0.98  
% 3.52/0.98  fof(f30,plain,(
% 3.52/0.98    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.52/0.98    inference(flattening,[],[f29])).
% 3.52/0.98  
% 3.52/0.98  fof(f55,plain,(
% 3.52/0.98    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.52/0.98    inference(nnf_transformation,[],[f30])).
% 3.52/0.98  
% 3.52/0.98  fof(f93,plain,(
% 3.52/0.98    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.52/0.98    inference(cnf_transformation,[],[f55])).
% 3.52/0.98  
% 3.52/0.98  fof(f12,axiom,(
% 3.52/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 3.52/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/0.98  
% 3.52/0.98  fof(f31,plain,(
% 3.52/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.52/0.98    inference(ennf_transformation,[],[f12])).
% 3.52/0.98  
% 3.52/0.98  fof(f32,plain,(
% 3.52/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.52/0.98    inference(flattening,[],[f31])).
% 3.52/0.98  
% 3.52/0.98  fof(f94,plain,(
% 3.52/0.98    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.52/0.98    inference(cnf_transformation,[],[f32])).
% 3.52/0.98  
% 3.52/0.98  fof(f98,plain,(
% 3.52/0.98    v2_pre_topc(sK4)),
% 3.52/0.98    inference(cnf_transformation,[],[f64])).
% 3.52/0.98  
% 3.52/0.98  fof(f99,plain,(
% 3.52/0.98    l1_pre_topc(sK4)),
% 3.52/0.98    inference(cnf_transformation,[],[f64])).
% 3.52/0.98  
% 3.52/0.98  fof(f106,plain,(
% 3.52/0.98    m1_pre_topc(sK7,sK4)),
% 3.52/0.98    inference(cnf_transformation,[],[f64])).
% 3.52/0.98  
% 3.52/0.98  fof(f5,axiom,(
% 3.52/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.52/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/0.98  
% 3.52/0.98  fof(f22,plain,(
% 3.52/0.98    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.52/0.98    inference(ennf_transformation,[],[f5])).
% 3.52/0.98  
% 3.52/0.98  fof(f83,plain,(
% 3.52/0.98    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.52/0.98    inference(cnf_transformation,[],[f22])).
% 3.52/0.98  
% 3.52/0.98  fof(f2,axiom,(
% 3.52/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 3.52/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/0.98  
% 3.52/0.98  fof(f17,plain,(
% 3.52/0.98    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.52/0.98    inference(ennf_transformation,[],[f2])).
% 3.52/0.98  
% 3.52/0.98  fof(f18,plain,(
% 3.52/0.98    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.52/0.98    inference(flattening,[],[f17])).
% 3.52/0.98  
% 3.52/0.98  fof(f68,plain,(
% 3.52/0.98    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.52/0.98    inference(cnf_transformation,[],[f18])).
% 3.52/0.98  
% 3.52/0.98  fof(f10,axiom,(
% 3.52/0.98    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 3.52/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/0.98  
% 3.52/0.98  fof(f28,plain,(
% 3.52/0.98    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 3.52/0.98    inference(ennf_transformation,[],[f10])).
% 3.52/0.98  
% 3.52/0.98  fof(f91,plain,(
% 3.52/0.98    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 3.52/0.98    inference(cnf_transformation,[],[f28])).
% 3.52/0.98  
% 3.52/0.98  fof(f110,plain,(
% 3.52/0.98    g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7),
% 3.52/0.98    inference(cnf_transformation,[],[f64])).
% 3.52/0.98  
% 3.52/0.98  fof(f6,axiom,(
% 3.52/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 3.52/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/0.98  
% 3.52/0.98  fof(f23,plain,(
% 3.52/0.98    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 3.52/0.98    inference(ennf_transformation,[],[f6])).
% 3.52/0.98  
% 3.52/0.98  fof(f84,plain,(
% 3.52/0.98    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 3.52/0.98    inference(cnf_transformation,[],[f23])).
% 3.52/0.98  
% 3.52/0.98  fof(f1,axiom,(
% 3.52/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.52/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/0.98  
% 3.52/0.98  fof(f39,plain,(
% 3.52/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.52/0.98    inference(nnf_transformation,[],[f1])).
% 3.52/0.98  
% 3.52/0.98  fof(f40,plain,(
% 3.52/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.52/0.98    inference(flattening,[],[f39])).
% 3.52/0.98  
% 3.52/0.98  fof(f67,plain,(
% 3.52/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.52/0.98    inference(cnf_transformation,[],[f40])).
% 3.52/0.98  
% 3.52/0.98  fof(f7,axiom,(
% 3.52/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 3.52/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/0.98  
% 3.52/0.98  fof(f24,plain,(
% 3.52/0.98    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.52/0.98    inference(ennf_transformation,[],[f7])).
% 3.52/0.98  
% 3.52/0.98  fof(f52,plain,(
% 3.52/0.98    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.52/0.98    inference(nnf_transformation,[],[f24])).
% 3.52/0.98  
% 3.52/0.98  fof(f85,plain,(
% 3.52/0.98    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.52/0.98    inference(cnf_transformation,[],[f52])).
% 3.52/0.98  
% 3.52/0.98  fof(f114,plain,(
% 3.52/0.98    r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10)),
% 3.52/0.98    inference(cnf_transformation,[],[f64])).
% 3.52/0.98  
% 3.52/0.98  fof(f113,plain,(
% 3.52/0.98    sK9 = sK10),
% 3.52/0.98    inference(cnf_transformation,[],[f64])).
% 3.52/0.98  
% 3.52/0.98  fof(f4,axiom,(
% 3.52/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 3.52/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/0.98  
% 3.52/0.98  fof(f21,plain,(
% 3.52/0.98    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.52/0.98    inference(ennf_transformation,[],[f4])).
% 3.52/0.98  
% 3.52/0.98  fof(f51,plain,(
% 3.52/0.98    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.52/0.98    inference(nnf_transformation,[],[f21])).
% 3.52/0.98  
% 3.52/0.98  fof(f82,plain,(
% 3.52/0.98    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.52/0.98    inference(cnf_transformation,[],[f51])).
% 3.52/0.98  
% 3.52/0.98  fof(f8,axiom,(
% 3.52/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 3.52/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/0.98  
% 3.52/0.98  fof(f25,plain,(
% 3.52/0.98    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.52/0.98    inference(ennf_transformation,[],[f8])).
% 3.52/0.98  
% 3.52/0.98  fof(f26,plain,(
% 3.52/0.98    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.52/0.98    inference(flattening,[],[f25])).
% 3.52/0.98  
% 3.52/0.98  fof(f53,plain,(
% 3.52/0.98    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.52/0.98    inference(nnf_transformation,[],[f26])).
% 3.52/0.98  
% 3.52/0.98  fof(f54,plain,(
% 3.52/0.98    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.52/0.98    inference(flattening,[],[f53])).
% 3.52/0.98  
% 3.52/0.98  fof(f88,plain,(
% 3.52/0.98    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.52/0.98    inference(cnf_transformation,[],[f54])).
% 3.52/0.98  
% 3.52/0.98  fof(f119,plain,(
% 3.52/0.98    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.52/0.98    inference(equality_resolution,[],[f88])).
% 3.52/0.98  
% 3.52/0.98  fof(f9,axiom,(
% 3.52/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.52/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/0.98  
% 3.52/0.98  fof(f27,plain,(
% 3.52/0.98    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.52/0.98    inference(ennf_transformation,[],[f9])).
% 3.52/0.98  
% 3.52/0.98  fof(f90,plain,(
% 3.52/0.98    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.52/0.98    inference(cnf_transformation,[],[f27])).
% 3.52/0.98  
% 3.52/0.98  fof(f13,axiom,(
% 3.52/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 3.52/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/0.98  
% 3.52/0.98  fof(f33,plain,(
% 3.52/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.52/0.98    inference(ennf_transformation,[],[f13])).
% 3.52/0.98  
% 3.52/0.98  fof(f34,plain,(
% 3.52/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.52/0.98    inference(flattening,[],[f33])).
% 3.52/0.98  
% 3.52/0.98  fof(f56,plain,(
% 3.52/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5))) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.52/0.98    inference(nnf_transformation,[],[f34])).
% 3.52/0.98  
% 3.52/0.98  fof(f96,plain,(
% 3.52/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.52/0.98    inference(cnf_transformation,[],[f56])).
% 3.52/0.98  
% 3.52/0.98  fof(f121,plain,(
% 3.52/0.98    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.52/0.98    inference(equality_resolution,[],[f96])).
% 3.52/0.98  
% 3.52/0.98  fof(f108,plain,(
% 3.52/0.98    v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5))),
% 3.52/0.98    inference(cnf_transformation,[],[f64])).
% 3.52/0.98  
% 3.52/0.98  fof(f107,plain,(
% 3.52/0.98    v1_funct_1(sK8)),
% 3.52/0.98    inference(cnf_transformation,[],[f64])).
% 3.52/0.98  
% 3.52/0.98  fof(f100,plain,(
% 3.52/0.98    ~v2_struct_0(sK5)),
% 3.52/0.98    inference(cnf_transformation,[],[f64])).
% 3.52/0.98  
% 3.52/0.98  fof(f101,plain,(
% 3.52/0.98    v2_pre_topc(sK5)),
% 3.52/0.98    inference(cnf_transformation,[],[f64])).
% 3.52/0.98  
% 3.52/0.98  fof(f102,plain,(
% 3.52/0.98    l1_pre_topc(sK5)),
% 3.52/0.98    inference(cnf_transformation,[],[f64])).
% 3.52/0.98  
% 3.52/0.98  fof(f105,plain,(
% 3.52/0.98    ~v2_struct_0(sK7)),
% 3.52/0.98    inference(cnf_transformation,[],[f64])).
% 3.52/0.98  
% 3.52/0.98  fof(f109,plain,(
% 3.52/0.98    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5))))),
% 3.52/0.98    inference(cnf_transformation,[],[f64])).
% 3.52/0.98  
% 3.52/0.98  fof(f97,plain,(
% 3.52/0.98    ~v2_struct_0(sK4)),
% 3.52/0.98    inference(cnf_transformation,[],[f64])).
% 3.52/0.98  
% 3.52/0.98  fof(f103,plain,(
% 3.52/0.98    ~v2_struct_0(sK6)),
% 3.52/0.98    inference(cnf_transformation,[],[f64])).
% 3.52/0.98  
% 3.52/0.98  fof(f111,plain,(
% 3.52/0.98    m1_subset_1(sK9,u1_struct_0(sK7))),
% 3.52/0.98    inference(cnf_transformation,[],[f64])).
% 3.52/0.98  
% 3.52/0.98  fof(f115,plain,(
% 3.52/0.98    ~r1_tmap_1(sK7,sK5,sK8,sK9)),
% 3.52/0.98    inference(cnf_transformation,[],[f64])).
% 3.52/0.98  
% 3.52/0.98  fof(f112,plain,(
% 3.52/0.98    m1_subset_1(sK10,u1_struct_0(sK6))),
% 3.52/0.98    inference(cnf_transformation,[],[f64])).
% 3.52/0.98  
% 3.52/0.98  fof(f3,axiom,(
% 3.52/0.98    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 3.52/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/0.98  
% 3.52/0.98  fof(f16,plain,(
% 3.52/0.98    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 3.52/0.98    inference(rectify,[],[f3])).
% 3.52/0.98  
% 3.52/0.98  fof(f19,plain,(
% 3.52/0.98    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 3.52/0.98    inference(ennf_transformation,[],[f16])).
% 3.52/0.98  
% 3.52/0.98  fof(f20,plain,(
% 3.52/0.98    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 3.52/0.98    inference(flattening,[],[f19])).
% 3.52/0.98  
% 3.52/0.98  fof(f37,plain,(
% 3.52/0.98    ! [X0] : (sP0(X0) <=> ! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.52/0.98    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.52/0.98  
% 3.52/0.98  fof(f38,plain,(
% 3.52/0.98    ! [X0] : ((v2_pre_topc(X0) <=> (sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 3.52/0.98    inference(definition_folding,[],[f20,f37])).
% 3.52/0.98  
% 3.52/0.98  fof(f46,plain,(
% 3.52/0.98    ! [X0] : (((v2_pre_topc(X0) | (~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 3.52/0.98    inference(nnf_transformation,[],[f38])).
% 3.52/0.98  
% 3.52/0.98  fof(f47,plain,(
% 3.52/0.98    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 3.52/0.98    inference(flattening,[],[f46])).
% 3.52/0.98  
% 3.52/0.98  fof(f48,plain,(
% 3.52/0.98    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 3.52/0.98    inference(rectify,[],[f47])).
% 3.52/0.98  
% 3.52/0.98  fof(f49,plain,(
% 3.52/0.98    ! [X0] : (? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0)) & r1_tarski(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 3.52/0.98    introduced(choice_axiom,[])).
% 3.52/0.98  
% 3.52/0.98  fof(f50,plain,(
% 3.52/0.98    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0)) & r1_tarski(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 3.52/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f48,f49])).
% 3.52/0.98  
% 3.52/0.98  fof(f75,plain,(
% 3.52/0.98    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 3.52/0.98    inference(cnf_transformation,[],[f50])).
% 3.52/0.98  
% 3.52/0.98  cnf(c_43,negated_conjecture,
% 3.52/0.98      ( m1_pre_topc(sK6,sK4) ),
% 3.52/0.98      inference(cnf_transformation,[],[f104]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_2901,plain,
% 3.52/0.98      ( m1_pre_topc(sK6,sK4) = iProver_top ),
% 3.52/0.98      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_27,plain,
% 3.52/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.52/0.98      | ~ m1_pre_topc(X0,X2)
% 3.52/0.98      | ~ m1_pre_topc(X2,X1)
% 3.52/0.98      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 3.52/0.98      | ~ l1_pre_topc(X1)
% 3.52/0.98      | ~ v2_pre_topc(X1) ),
% 3.52/0.98      inference(cnf_transformation,[],[f93]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_2911,plain,
% 3.52/0.98      ( m1_pre_topc(X0,X1) != iProver_top
% 3.52/0.98      | m1_pre_topc(X2,X1) != iProver_top
% 3.52/0.98      | m1_pre_topc(X0,X2) != iProver_top
% 3.52/0.98      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) = iProver_top
% 3.52/0.98      | l1_pre_topc(X1) != iProver_top
% 3.52/0.98      | v2_pre_topc(X1) != iProver_top ),
% 3.52/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_29,plain,
% 3.52/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.52/0.98      | ~ m1_pre_topc(X2,X0)
% 3.52/0.98      | m1_pre_topc(X2,X1)
% 3.52/0.98      | ~ l1_pre_topc(X1)
% 3.52/0.98      | ~ v2_pre_topc(X1) ),
% 3.52/0.98      inference(cnf_transformation,[],[f94]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_2909,plain,
% 3.52/0.98      ( m1_pre_topc(X0,X1) != iProver_top
% 3.52/0.98      | m1_pre_topc(X2,X0) != iProver_top
% 3.52/0.98      | m1_pre_topc(X2,X1) = iProver_top
% 3.52/0.98      | l1_pre_topc(X1) != iProver_top
% 3.52/0.98      | v2_pre_topc(X1) != iProver_top ),
% 3.52/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_3111,plain,
% 3.52/0.98      ( m1_pre_topc(X0,X1) != iProver_top
% 3.52/0.98      | m1_pre_topc(X2,X0) != iProver_top
% 3.52/0.98      | r1_tarski(u1_struct_0(X2),u1_struct_0(X0)) = iProver_top
% 3.52/0.98      | l1_pre_topc(X1) != iProver_top
% 3.52/0.98      | v2_pre_topc(X1) != iProver_top ),
% 3.52/0.98      inference(forward_subsumption_resolution,
% 3.52/0.98                [status(thm)],
% 3.52/0.98                [c_2911,c_2909]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_6740,plain,
% 3.52/0.98      ( m1_pre_topc(X0,sK6) != iProver_top
% 3.52/0.98      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK6)) = iProver_top
% 3.52/0.98      | l1_pre_topc(sK4) != iProver_top
% 3.52/0.98      | v2_pre_topc(sK4) != iProver_top ),
% 3.52/0.98      inference(superposition,[status(thm)],[c_2901,c_3111]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_49,negated_conjecture,
% 3.52/0.98      ( v2_pre_topc(sK4) ),
% 3.52/0.98      inference(cnf_transformation,[],[f98]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_52,plain,
% 3.52/0.98      ( v2_pre_topc(sK4) = iProver_top ),
% 3.52/0.98      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_48,negated_conjecture,
% 3.52/0.98      ( l1_pre_topc(sK4) ),
% 3.52/0.98      inference(cnf_transformation,[],[f99]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_53,plain,
% 3.52/0.98      ( l1_pre_topc(sK4) = iProver_top ),
% 3.52/0.98      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_7354,plain,
% 3.52/0.98      ( m1_pre_topc(X0,sK6) != iProver_top
% 3.52/0.98      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK6)) = iProver_top ),
% 3.52/0.98      inference(global_propositional_subsumption,
% 3.52/0.98                [status(thm)],
% 3.52/0.98                [c_6740,c_52,c_53,c_4747,c_4748,c_5642,c_6742]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_41,negated_conjecture,
% 3.52/0.98      ( m1_pre_topc(sK7,sK4) ),
% 3.52/0.98      inference(cnf_transformation,[],[f106]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_2903,plain,
% 3.52/0.98      ( m1_pre_topc(sK7,sK4) = iProver_top ),
% 3.52/0.98      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_6739,plain,
% 3.52/0.98      ( m1_pre_topc(X0,sK7) != iProver_top
% 3.52/0.98      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK7)) = iProver_top
% 3.52/0.98      | l1_pre_topc(sK4) != iProver_top
% 3.52/0.98      | v2_pre_topc(sK4) != iProver_top ),
% 3.52/0.98      inference(superposition,[status(thm)],[c_2903,c_3111]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_18,plain,
% 3.52/0.98      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.52/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_2915,plain,
% 3.52/0.98      ( m1_pre_topc(X0,X1) != iProver_top
% 3.52/0.98      | l1_pre_topc(X1) != iProver_top
% 3.52/0.98      | l1_pre_topc(X0) = iProver_top ),
% 3.52/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_4748,plain,
% 3.52/0.98      ( l1_pre_topc(sK4) != iProver_top
% 3.52/0.98      | l1_pre_topc(sK6) = iProver_top ),
% 3.52/0.98      inference(superposition,[status(thm)],[c_2901,c_2915]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_3,plain,
% 3.52/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.52/0.98      | ~ l1_pre_topc(X1)
% 3.52/0.98      | ~ v2_pre_topc(X1)
% 3.52/0.98      | v2_pre_topc(X0) ),
% 3.52/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_2928,plain,
% 3.52/0.98      ( m1_pre_topc(X0,X1) != iProver_top
% 3.52/0.98      | l1_pre_topc(X1) != iProver_top
% 3.52/0.98      | v2_pre_topc(X1) != iProver_top
% 3.52/0.98      | v2_pre_topc(X0) = iProver_top ),
% 3.52/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_5643,plain,
% 3.52/0.98      ( l1_pre_topc(sK4) != iProver_top
% 3.52/0.98      | v2_pre_topc(sK4) != iProver_top
% 3.52/0.98      | v2_pre_topc(sK6) = iProver_top ),
% 3.52/0.98      inference(superposition,[status(thm)],[c_2901,c_2928]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_26,plain,
% 3.52/0.98      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 3.52/0.98      inference(cnf_transformation,[],[f91]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_2912,plain,
% 3.52/0.98      ( m1_pre_topc(X0,X0) = iProver_top
% 3.52/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.52/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_37,negated_conjecture,
% 3.52/0.98      ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7 ),
% 3.52/0.98      inference(cnf_transformation,[],[f110]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_19,plain,
% 3.52/0.98      ( m1_pre_topc(X0,X1)
% 3.52/0.98      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.52/0.98      | ~ l1_pre_topc(X1) ),
% 3.52/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_2914,plain,
% 3.52/0.98      ( m1_pre_topc(X0,X1) = iProver_top
% 3.52/0.98      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 3.52/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.52/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_5330,plain,
% 3.52/0.98      ( m1_pre_topc(X0,sK6) = iProver_top
% 3.52/0.98      | m1_pre_topc(X0,sK7) != iProver_top
% 3.52/0.98      | l1_pre_topc(sK6) != iProver_top ),
% 3.52/0.98      inference(superposition,[status(thm)],[c_37,c_2914]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_5435,plain,
% 3.52/0.98      ( m1_pre_topc(X0,sK7) != iProver_top
% 3.52/0.98      | m1_pre_topc(X0,sK6) = iProver_top ),
% 3.52/0.98      inference(global_propositional_subsumption,
% 3.52/0.98                [status(thm)],
% 3.52/0.98                [c_5330,c_53,c_4748]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_5436,plain,
% 3.52/0.98      ( m1_pre_topc(X0,sK6) = iProver_top
% 3.52/0.98      | m1_pre_topc(X0,sK7) != iProver_top ),
% 3.52/0.98      inference(renaming,[status(thm)],[c_5435]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_5443,plain,
% 3.52/0.98      ( m1_pre_topc(sK7,sK6) = iProver_top
% 3.52/0.98      | l1_pre_topc(sK7) != iProver_top ),
% 3.52/0.98      inference(superposition,[status(thm)],[c_2912,c_5436]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_4747,plain,
% 3.52/0.98      ( l1_pre_topc(sK4) != iProver_top
% 3.52/0.98      | l1_pre_topc(sK7) = iProver_top ),
% 3.52/0.98      inference(superposition,[status(thm)],[c_2903,c_2915]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_5453,plain,
% 3.52/0.98      ( m1_pre_topc(sK7,sK6) = iProver_top ),
% 3.52/0.98      inference(global_propositional_subsumption,
% 3.52/0.98                [status(thm)],
% 3.52/0.98                [c_5443,c_53,c_4747]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_6745,plain,
% 3.52/0.98      ( m1_pre_topc(X0,sK7) != iProver_top
% 3.52/0.98      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK7)) = iProver_top
% 3.52/0.98      | l1_pre_topc(sK6) != iProver_top
% 3.52/0.98      | v2_pre_topc(sK6) != iProver_top ),
% 3.52/0.98      inference(superposition,[status(thm)],[c_5453,c_3111]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_7203,plain,
% 3.52/0.98      ( m1_pre_topc(X0,sK7) != iProver_top
% 3.52/0.98      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK7)) = iProver_top ),
% 3.52/0.98      inference(global_propositional_subsumption,
% 3.52/0.98                [status(thm)],
% 3.52/0.98                [c_6739,c_52,c_53,c_4748,c_5643,c_6745]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_0,plain,
% 3.52/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.52/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_2930,plain,
% 3.52/0.98      ( X0 = X1
% 3.52/0.98      | r1_tarski(X0,X1) != iProver_top
% 3.52/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 3.52/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_7211,plain,
% 3.52/0.98      ( u1_struct_0(X0) = u1_struct_0(sK7)
% 3.52/0.98      | m1_pre_topc(X0,sK7) != iProver_top
% 3.52/0.98      | r1_tarski(u1_struct_0(sK7),u1_struct_0(X0)) != iProver_top ),
% 3.52/0.98      inference(superposition,[status(thm)],[c_7203,c_2930]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_7364,plain,
% 3.52/0.98      ( u1_struct_0(sK7) = u1_struct_0(sK6)
% 3.52/0.98      | m1_pre_topc(sK6,sK7) != iProver_top
% 3.52/0.98      | m1_pre_topc(sK7,sK6) != iProver_top ),
% 3.52/0.98      inference(superposition,[status(thm)],[c_7354,c_7211]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_21,plain,
% 3.52/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.52/0.98      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.52/0.98      | ~ l1_pre_topc(X0)
% 3.52/0.98      | ~ l1_pre_topc(X1) ),
% 3.52/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_279,plain,
% 3.52/0.98      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.52/0.98      | ~ m1_pre_topc(X0,X1)
% 3.52/0.98      | ~ l1_pre_topc(X1) ),
% 3.52/0.98      inference(global_propositional_subsumption,
% 3.52/0.98                [status(thm)],
% 3.52/0.98                [c_21,c_18]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_280,plain,
% 3.52/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.52/0.98      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.52/0.98      | ~ l1_pre_topc(X1) ),
% 3.52/0.98      inference(renaming,[status(thm)],[c_279]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_2893,plain,
% 3.52/0.98      ( m1_pre_topc(X0,X1) != iProver_top
% 3.52/0.98      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 3.52/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.52/0.98      inference(predicate_to_equality,[status(thm)],[c_280]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_3906,plain,
% 3.52/0.98      ( m1_pre_topc(X0,sK6) != iProver_top
% 3.52/0.98      | m1_pre_topc(X0,sK7) = iProver_top
% 3.52/0.98      | l1_pre_topc(sK6) != iProver_top ),
% 3.52/0.98      inference(superposition,[status(thm)],[c_37,c_2893]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_4168,plain,
% 3.52/0.98      ( m1_pre_topc(sK6,sK7) = iProver_top
% 3.52/0.98      | l1_pre_topc(sK6) != iProver_top ),
% 3.52/0.98      inference(superposition,[status(thm)],[c_2912,c_3906]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_7488,plain,
% 3.52/0.98      ( u1_struct_0(sK7) = u1_struct_0(sK6) ),
% 3.52/0.98      inference(global_propositional_subsumption,
% 3.52/0.98                [status(thm)],
% 3.52/0.98                [c_7364,c_53,c_4168,c_4747,c_4748,c_5443]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_33,negated_conjecture,
% 3.52/0.98      ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10) ),
% 3.52/0.98      inference(cnf_transformation,[],[f114]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_2907,plain,
% 3.52/0.98      ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10) = iProver_top ),
% 3.52/0.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_34,negated_conjecture,
% 3.52/0.98      ( sK9 = sK10 ),
% 3.52/0.98      inference(cnf_transformation,[],[f113]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_2970,plain,
% 3.52/0.98      ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK9) = iProver_top ),
% 3.52/0.98      inference(light_normalisation,[status(thm)],[c_2907,c_34]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_16,plain,
% 3.52/0.98      ( v3_pre_topc(X0,X1)
% 3.52/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.52/0.98      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 3.52/0.98      | ~ l1_pre_topc(X1) ),
% 3.52/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_23,plain,
% 3.52/0.98      ( v1_tsep_1(X0,X1)
% 3.52/0.98      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.52/0.98      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.52/0.98      | ~ m1_pre_topc(X0,X1)
% 3.52/0.98      | ~ l1_pre_topc(X1)
% 3.52/0.98      | ~ v2_pre_topc(X1) ),
% 3.52/0.98      inference(cnf_transformation,[],[f119]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_25,plain,
% 3.52/0.98      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.52/0.98      | ~ m1_pre_topc(X0,X1)
% 3.52/0.98      | ~ l1_pre_topc(X1) ),
% 3.52/0.98      inference(cnf_transformation,[],[f90]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_272,plain,
% 3.52/0.98      ( ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.52/0.98      | v1_tsep_1(X0,X1)
% 3.52/0.98      | ~ m1_pre_topc(X0,X1)
% 3.52/0.98      | ~ l1_pre_topc(X1)
% 3.52/0.98      | ~ v2_pre_topc(X1) ),
% 3.52/0.98      inference(global_propositional_subsumption,
% 3.52/0.98                [status(thm)],
% 3.52/0.98                [c_23,c_25]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_273,plain,
% 3.52/0.98      ( v1_tsep_1(X0,X1)
% 3.52/0.98      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.52/0.98      | ~ m1_pre_topc(X0,X1)
% 3.52/0.98      | ~ l1_pre_topc(X1)
% 3.52/0.98      | ~ v2_pre_topc(X1) ),
% 3.52/0.98      inference(renaming,[status(thm)],[c_272]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_522,plain,
% 3.52/0.98      ( v1_tsep_1(X0,X1)
% 3.52/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 3.52/0.98      | ~ r2_hidden(X2,u1_pre_topc(X3))
% 3.52/0.98      | ~ m1_pre_topc(X0,X1)
% 3.52/0.98      | ~ l1_pre_topc(X3)
% 3.52/0.98      | ~ l1_pre_topc(X1)
% 3.52/0.98      | ~ v2_pre_topc(X1)
% 3.52/0.98      | X1 != X3
% 3.52/0.98      | u1_struct_0(X0) != X2 ),
% 3.52/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_273]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_523,plain,
% 3.52/0.98      ( v1_tsep_1(X0,X1)
% 3.52/0.98      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.52/0.98      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X1))
% 3.52/0.98      | ~ m1_pre_topc(X0,X1)
% 3.52/0.98      | ~ l1_pre_topc(X1)
% 3.52/0.98      | ~ v2_pre_topc(X1) ),
% 3.52/0.98      inference(unflattening,[status(thm)],[c_522]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_527,plain,
% 3.52/0.98      ( v1_tsep_1(X0,X1)
% 3.52/0.98      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X1))
% 3.52/0.98      | ~ m1_pre_topc(X0,X1)
% 3.52/0.98      | ~ l1_pre_topc(X1)
% 3.52/0.98      | ~ v2_pre_topc(X1) ),
% 3.52/0.98      inference(global_propositional_subsumption,
% 3.52/0.98                [status(thm)],
% 3.52/0.98                [c_523,c_25]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_30,plain,
% 3.52/0.98      ( r1_tmap_1(X0,X1,X2,X3)
% 3.52/0.98      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 3.52/0.98      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.52/0.98      | ~ v1_tsep_1(X4,X0)
% 3.52/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.52/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.52/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.52/0.98      | ~ m1_pre_topc(X4,X5)
% 3.52/0.98      | ~ m1_pre_topc(X0,X5)
% 3.52/0.98      | ~ m1_pre_topc(X4,X0)
% 3.52/0.98      | v2_struct_0(X5)
% 3.52/0.98      | v2_struct_0(X1)
% 3.52/0.98      | v2_struct_0(X4)
% 3.52/0.98      | v2_struct_0(X0)
% 3.52/0.98      | ~ v1_funct_1(X2)
% 3.52/0.98      | ~ l1_pre_topc(X5)
% 3.52/0.98      | ~ l1_pre_topc(X1)
% 3.52/0.98      | ~ v2_pre_topc(X5)
% 3.52/0.98      | ~ v2_pre_topc(X1) ),
% 3.52/0.98      inference(cnf_transformation,[],[f121]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_39,negated_conjecture,
% 3.52/0.98      ( v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5)) ),
% 3.52/0.98      inference(cnf_transformation,[],[f108]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_657,plain,
% 3.52/0.98      ( r1_tmap_1(X0,X1,X2,X3)
% 3.52/0.98      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 3.52/0.98      | ~ v1_tsep_1(X4,X0)
% 3.52/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.52/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.52/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.52/0.98      | ~ m1_pre_topc(X4,X0)
% 3.52/0.98      | ~ m1_pre_topc(X4,X5)
% 3.52/0.98      | ~ m1_pre_topc(X0,X5)
% 3.52/0.98      | v2_struct_0(X0)
% 3.52/0.98      | v2_struct_0(X1)
% 3.52/0.98      | v2_struct_0(X4)
% 3.52/0.98      | v2_struct_0(X5)
% 3.52/0.98      | ~ v1_funct_1(X2)
% 3.52/0.98      | ~ l1_pre_topc(X1)
% 3.52/0.98      | ~ l1_pre_topc(X5)
% 3.52/0.98      | ~ v2_pre_topc(X1)
% 3.52/0.98      | ~ v2_pre_topc(X5)
% 3.52/0.98      | u1_struct_0(X1) != u1_struct_0(sK5)
% 3.52/0.98      | u1_struct_0(X0) != u1_struct_0(sK7)
% 3.52/0.98      | sK8 != X2 ),
% 3.52/0.98      inference(resolution_lifted,[status(thm)],[c_30,c_39]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_658,plain,
% 3.52/0.98      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK8),X4)
% 3.52/0.98      | r1_tmap_1(X3,X1,sK8,X4)
% 3.52/0.98      | ~ v1_tsep_1(X0,X3)
% 3.52/0.98      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.52/0.98      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.52/0.98      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.52/0.98      | ~ m1_pre_topc(X0,X3)
% 3.52/0.98      | ~ m1_pre_topc(X0,X2)
% 3.52/0.98      | ~ m1_pre_topc(X3,X2)
% 3.52/0.98      | v2_struct_0(X3)
% 3.52/0.98      | v2_struct_0(X1)
% 3.52/0.98      | v2_struct_0(X0)
% 3.52/0.98      | v2_struct_0(X2)
% 3.52/0.98      | ~ v1_funct_1(sK8)
% 3.52/0.98      | ~ l1_pre_topc(X1)
% 3.52/0.98      | ~ l1_pre_topc(X2)
% 3.52/0.98      | ~ v2_pre_topc(X1)
% 3.52/0.98      | ~ v2_pre_topc(X2)
% 3.52/0.98      | u1_struct_0(X1) != u1_struct_0(sK5)
% 3.52/0.98      | u1_struct_0(X3) != u1_struct_0(sK7) ),
% 3.52/0.98      inference(unflattening,[status(thm)],[c_657]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_40,negated_conjecture,
% 3.52/0.98      ( v1_funct_1(sK8) ),
% 3.52/0.98      inference(cnf_transformation,[],[f107]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_662,plain,
% 3.52/0.98      ( v2_struct_0(X2)
% 3.52/0.98      | v2_struct_0(X0)
% 3.52/0.98      | v2_struct_0(X1)
% 3.52/0.98      | v2_struct_0(X3)
% 3.52/0.98      | ~ m1_pre_topc(X3,X2)
% 3.52/0.98      | ~ m1_pre_topc(X0,X2)
% 3.52/0.98      | ~ m1_pre_topc(X0,X3)
% 3.52/0.98      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.52/0.98      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.52/0.98      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.52/0.98      | ~ v1_tsep_1(X0,X3)
% 3.52/0.98      | r1_tmap_1(X3,X1,sK8,X4)
% 3.52/0.98      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK8),X4)
% 3.52/0.98      | ~ l1_pre_topc(X1)
% 3.52/0.98      | ~ l1_pre_topc(X2)
% 3.52/0.98      | ~ v2_pre_topc(X1)
% 3.52/0.98      | ~ v2_pre_topc(X2)
% 3.52/0.98      | u1_struct_0(X1) != u1_struct_0(sK5)
% 3.52/0.98      | u1_struct_0(X3) != u1_struct_0(sK7) ),
% 3.52/0.98      inference(global_propositional_subsumption,
% 3.52/0.98                [status(thm)],
% 3.52/0.98                [c_658,c_40]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_663,plain,
% 3.52/0.98      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK8),X4)
% 3.52/0.98      | r1_tmap_1(X3,X1,sK8,X4)
% 3.52/0.98      | ~ v1_tsep_1(X0,X3)
% 3.52/0.98      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.52/0.98      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.52/0.98      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.52/0.98      | ~ m1_pre_topc(X0,X2)
% 3.52/0.98      | ~ m1_pre_topc(X0,X3)
% 3.52/0.98      | ~ m1_pre_topc(X3,X2)
% 3.52/0.98      | v2_struct_0(X0)
% 3.52/0.98      | v2_struct_0(X1)
% 3.52/0.98      | v2_struct_0(X2)
% 3.52/0.98      | v2_struct_0(X3)
% 3.52/0.98      | ~ l1_pre_topc(X1)
% 3.52/0.98      | ~ l1_pre_topc(X2)
% 3.52/0.98      | ~ v2_pre_topc(X1)
% 3.52/0.98      | ~ v2_pre_topc(X2)
% 3.52/0.98      | u1_struct_0(X1) != u1_struct_0(sK5)
% 3.52/0.98      | u1_struct_0(X3) != u1_struct_0(sK7) ),
% 3.52/0.98      inference(renaming,[status(thm)],[c_662]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_706,plain,
% 3.52/0.98      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK8),X4)
% 3.52/0.98      | r1_tmap_1(X3,X1,sK8,X4)
% 3.52/0.98      | ~ v1_tsep_1(X0,X3)
% 3.52/0.98      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.52/0.98      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.52/0.98      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.52/0.98      | ~ m1_pre_topc(X0,X3)
% 3.52/0.98      | ~ m1_pre_topc(X3,X2)
% 3.52/0.98      | v2_struct_0(X0)
% 3.52/0.98      | v2_struct_0(X1)
% 3.52/0.98      | v2_struct_0(X2)
% 3.52/0.98      | v2_struct_0(X3)
% 3.52/0.98      | ~ l1_pre_topc(X1)
% 3.52/0.98      | ~ l1_pre_topc(X2)
% 3.52/0.98      | ~ v2_pre_topc(X1)
% 3.52/0.98      | ~ v2_pre_topc(X2)
% 3.52/0.98      | u1_struct_0(X1) != u1_struct_0(sK5)
% 3.52/0.98      | u1_struct_0(X3) != u1_struct_0(sK7) ),
% 3.52/0.98      inference(forward_subsumption_resolution,
% 3.52/0.98                [status(thm)],
% 3.52/0.98                [c_663,c_29]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_729,plain,
% 3.52/0.98      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK8),X4)
% 3.52/0.98      | r1_tmap_1(X3,X1,sK8,X4)
% 3.52/0.98      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.52/0.98      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.52/0.98      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.52/0.98      | ~ r2_hidden(u1_struct_0(X5),u1_pre_topc(X6))
% 3.52/0.98      | ~ m1_pre_topc(X5,X6)
% 3.52/0.98      | ~ m1_pre_topc(X0,X3)
% 3.52/0.98      | ~ m1_pre_topc(X3,X2)
% 3.52/0.98      | v2_struct_0(X1)
% 3.52/0.98      | v2_struct_0(X0)
% 3.52/0.98      | v2_struct_0(X2)
% 3.52/0.98      | v2_struct_0(X3)
% 3.52/0.98      | ~ l1_pre_topc(X6)
% 3.52/0.98      | ~ l1_pre_topc(X2)
% 3.52/0.98      | ~ l1_pre_topc(X1)
% 3.52/0.98      | ~ v2_pre_topc(X6)
% 3.52/0.98      | ~ v2_pre_topc(X2)
% 3.52/0.98      | ~ v2_pre_topc(X1)
% 3.52/0.98      | X0 != X5
% 3.52/0.98      | X3 != X6
% 3.52/0.98      | u1_struct_0(X1) != u1_struct_0(sK5)
% 3.52/0.98      | u1_struct_0(X3) != u1_struct_0(sK7) ),
% 3.52/0.98      inference(resolution_lifted,[status(thm)],[c_527,c_706]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_730,plain,
% 3.52/0.98      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK8),X4)
% 3.52/0.98      | r1_tmap_1(X3,X1,sK8,X4)
% 3.52/0.98      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.52/0.98      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.52/0.98      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.52/0.98      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X3))
% 3.52/0.98      | ~ m1_pre_topc(X0,X3)
% 3.52/0.98      | ~ m1_pre_topc(X3,X2)
% 3.52/0.98      | v2_struct_0(X1)
% 3.52/0.98      | v2_struct_0(X2)
% 3.52/0.98      | v2_struct_0(X0)
% 3.52/0.98      | v2_struct_0(X3)
% 3.52/0.98      | ~ l1_pre_topc(X1)
% 3.52/0.98      | ~ l1_pre_topc(X2)
% 3.52/0.98      | ~ l1_pre_topc(X3)
% 3.52/0.98      | ~ v2_pre_topc(X1)
% 3.52/0.98      | ~ v2_pre_topc(X2)
% 3.52/0.98      | ~ v2_pre_topc(X3)
% 3.52/0.98      | u1_struct_0(X1) != u1_struct_0(sK5)
% 3.52/0.98      | u1_struct_0(X3) != u1_struct_0(sK7) ),
% 3.52/0.98      inference(unflattening,[status(thm)],[c_729]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_774,plain,
% 3.52/0.98      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK8),X4)
% 3.52/0.98      | r1_tmap_1(X3,X1,sK8,X4)
% 3.52/0.98      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.52/0.98      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.52/0.98      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.52/0.98      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X3))
% 3.52/0.98      | ~ m1_pre_topc(X0,X3)
% 3.52/0.98      | ~ m1_pre_topc(X3,X2)
% 3.52/0.98      | v2_struct_0(X0)
% 3.52/0.98      | v2_struct_0(X1)
% 3.52/0.98      | v2_struct_0(X2)
% 3.52/0.98      | v2_struct_0(X3)
% 3.52/0.98      | ~ l1_pre_topc(X1)
% 3.52/0.98      | ~ l1_pre_topc(X2)
% 3.52/0.98      | ~ v2_pre_topc(X1)
% 3.52/0.98      | ~ v2_pre_topc(X2)
% 3.52/0.98      | u1_struct_0(X1) != u1_struct_0(sK5)
% 3.52/0.98      | u1_struct_0(X3) != u1_struct_0(sK7) ),
% 3.52/0.98      inference(forward_subsumption_resolution,
% 3.52/0.98                [status(thm)],
% 3.52/0.98                [c_730,c_3,c_18]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_2892,plain,
% 3.52/0.98      ( u1_struct_0(X0) != u1_struct_0(sK5)
% 3.52/0.98      | u1_struct_0(X1) != u1_struct_0(sK7)
% 3.52/0.98      | r1_tmap_1(X2,X0,k3_tmap_1(X3,X0,X1,X2,sK8),X4) != iProver_top
% 3.52/0.98      | r1_tmap_1(X1,X0,sK8,X4) = iProver_top
% 3.52/0.98      | m1_subset_1(X4,u1_struct_0(X2)) != iProver_top
% 3.52/0.98      | m1_subset_1(X4,u1_struct_0(X1)) != iProver_top
% 3.52/0.98      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 3.52/0.98      | r2_hidden(u1_struct_0(X2),u1_pre_topc(X1)) != iProver_top
% 3.52/0.98      | m1_pre_topc(X2,X1) != iProver_top
% 3.52/0.98      | m1_pre_topc(X1,X3) != iProver_top
% 3.52/0.98      | v2_struct_0(X0) = iProver_top
% 3.52/0.98      | v2_struct_0(X2) = iProver_top
% 3.52/0.98      | v2_struct_0(X1) = iProver_top
% 3.52/0.98      | v2_struct_0(X3) = iProver_top
% 3.52/0.98      | l1_pre_topc(X0) != iProver_top
% 3.52/0.98      | l1_pre_topc(X3) != iProver_top
% 3.52/0.98      | v2_pre_topc(X0) != iProver_top
% 3.52/0.98      | v2_pre_topc(X3) != iProver_top ),
% 3.52/0.98      inference(predicate_to_equality,[status(thm)],[c_774]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_3786,plain,
% 3.52/0.98      ( u1_struct_0(X0) != u1_struct_0(sK7)
% 3.52/0.98      | r1_tmap_1(X1,sK5,k3_tmap_1(X2,sK5,X0,X1,sK8),X3) != iProver_top
% 3.52/0.98      | r1_tmap_1(X0,sK5,sK8,X3) = iProver_top
% 3.52/0.98      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 3.52/0.98      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 3.52/0.98      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
% 3.52/0.98      | r2_hidden(u1_struct_0(X1),u1_pre_topc(X0)) != iProver_top
% 3.52/0.98      | m1_pre_topc(X0,X2) != iProver_top
% 3.52/0.98      | m1_pre_topc(X1,X0) != iProver_top
% 3.52/0.98      | v2_struct_0(X1) = iProver_top
% 3.52/0.98      | v2_struct_0(X0) = iProver_top
% 3.52/0.98      | v2_struct_0(X2) = iProver_top
% 3.52/0.98      | v2_struct_0(sK5) = iProver_top
% 3.52/0.98      | l1_pre_topc(X2) != iProver_top
% 3.52/0.98      | l1_pre_topc(sK5) != iProver_top
% 3.52/0.98      | v2_pre_topc(X2) != iProver_top
% 3.52/0.98      | v2_pre_topc(sK5) != iProver_top ),
% 3.52/0.98      inference(equality_resolution,[status(thm)],[c_2892]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_47,negated_conjecture,
% 3.52/0.98      ( ~ v2_struct_0(sK5) ),
% 3.52/0.98      inference(cnf_transformation,[],[f100]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_54,plain,
% 3.52/0.98      ( v2_struct_0(sK5) != iProver_top ),
% 3.52/0.98      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_46,negated_conjecture,
% 3.52/0.98      ( v2_pre_topc(sK5) ),
% 3.52/0.98      inference(cnf_transformation,[],[f101]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_55,plain,
% 3.52/0.98      ( v2_pre_topc(sK5) = iProver_top ),
% 3.52/0.98      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_45,negated_conjecture,
% 3.52/0.98      ( l1_pre_topc(sK5) ),
% 3.52/0.98      inference(cnf_transformation,[],[f102]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_56,plain,
% 3.52/0.98      ( l1_pre_topc(sK5) = iProver_top ),
% 3.52/0.98      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_3880,plain,
% 3.52/0.98      ( v2_pre_topc(X2) != iProver_top
% 3.52/0.98      | v2_struct_0(X2) = iProver_top
% 3.52/0.98      | v2_struct_0(X0) = iProver_top
% 3.52/0.98      | v2_struct_0(X1) = iProver_top
% 3.52/0.98      | m1_pre_topc(X1,X0) != iProver_top
% 3.52/0.98      | m1_pre_topc(X0,X2) != iProver_top
% 3.52/0.98      | r2_hidden(u1_struct_0(X1),u1_pre_topc(X0)) != iProver_top
% 3.52/0.98      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
% 3.52/0.98      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 3.52/0.98      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 3.52/0.98      | r1_tmap_1(X0,sK5,sK8,X3) = iProver_top
% 3.52/0.98      | r1_tmap_1(X1,sK5,k3_tmap_1(X2,sK5,X0,X1,sK8),X3) != iProver_top
% 3.52/0.98      | u1_struct_0(X0) != u1_struct_0(sK7)
% 3.52/0.98      | l1_pre_topc(X2) != iProver_top ),
% 3.52/0.98      inference(global_propositional_subsumption,
% 3.52/0.98                [status(thm)],
% 3.52/0.98                [c_3786,c_54,c_55,c_56]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_3881,plain,
% 3.52/0.98      ( u1_struct_0(X0) != u1_struct_0(sK7)
% 3.52/0.98      | r1_tmap_1(X1,sK5,k3_tmap_1(X2,sK5,X0,X1,sK8),X3) != iProver_top
% 3.52/0.98      | r1_tmap_1(X0,sK5,sK8,X3) = iProver_top
% 3.52/0.98      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 3.52/0.98      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 3.52/0.98      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
% 3.52/0.98      | r2_hidden(u1_struct_0(X1),u1_pre_topc(X0)) != iProver_top
% 3.52/0.98      | m1_pre_topc(X0,X2) != iProver_top
% 3.52/0.98      | m1_pre_topc(X1,X0) != iProver_top
% 3.52/0.98      | v2_struct_0(X1) = iProver_top
% 3.52/0.98      | v2_struct_0(X0) = iProver_top
% 3.52/0.98      | v2_struct_0(X2) = iProver_top
% 3.52/0.98      | l1_pre_topc(X2) != iProver_top
% 3.52/0.98      | v2_pre_topc(X2) != iProver_top ),
% 3.52/0.98      inference(renaming,[status(thm)],[c_3880]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_3898,plain,
% 3.52/0.98      ( r1_tmap_1(X0,sK5,k3_tmap_1(X1,sK5,sK7,X0,sK8),X2) != iProver_top
% 3.52/0.98      | r1_tmap_1(sK7,sK5,sK8,X2) = iProver_top
% 3.52/0.98      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 3.52/0.98      | m1_subset_1(X2,u1_struct_0(sK7)) != iProver_top
% 3.52/0.98      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) != iProver_top
% 3.52/0.98      | r2_hidden(u1_struct_0(X0),u1_pre_topc(sK7)) != iProver_top
% 3.52/0.98      | m1_pre_topc(X0,sK7) != iProver_top
% 3.52/0.98      | m1_pre_topc(sK7,X1) != iProver_top
% 3.52/0.98      | v2_struct_0(X1) = iProver_top
% 3.52/0.98      | v2_struct_0(X0) = iProver_top
% 3.52/0.98      | v2_struct_0(sK7) = iProver_top
% 3.52/0.98      | l1_pre_topc(X1) != iProver_top
% 3.52/0.98      | v2_pre_topc(X1) != iProver_top ),
% 3.52/0.98      inference(equality_resolution,[status(thm)],[c_3881]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_42,negated_conjecture,
% 3.52/0.98      ( ~ v2_struct_0(sK7) ),
% 3.52/0.98      inference(cnf_transformation,[],[f105]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_59,plain,
% 3.52/0.98      ( v2_struct_0(sK7) != iProver_top ),
% 3.52/0.98      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_38,negated_conjecture,
% 3.52/0.98      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) ),
% 3.52/0.98      inference(cnf_transformation,[],[f109]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_63,plain,
% 3.52/0.98      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) = iProver_top ),
% 3.52/0.98      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_4255,plain,
% 3.52/0.98      ( v2_struct_0(X0) = iProver_top
% 3.52/0.98      | v2_struct_0(X1) = iProver_top
% 3.52/0.98      | m1_pre_topc(sK7,X1) != iProver_top
% 3.52/0.98      | m1_pre_topc(X0,sK7) != iProver_top
% 3.52/0.98      | r2_hidden(u1_struct_0(X0),u1_pre_topc(sK7)) != iProver_top
% 3.52/0.98      | r1_tmap_1(X0,sK5,k3_tmap_1(X1,sK5,sK7,X0,sK8),X2) != iProver_top
% 3.52/0.98      | r1_tmap_1(sK7,sK5,sK8,X2) = iProver_top
% 3.52/0.98      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 3.52/0.98      | m1_subset_1(X2,u1_struct_0(sK7)) != iProver_top
% 3.52/0.98      | l1_pre_topc(X1) != iProver_top
% 3.52/0.98      | v2_pre_topc(X1) != iProver_top ),
% 3.52/0.98      inference(global_propositional_subsumption,
% 3.52/0.98                [status(thm)],
% 3.52/0.98                [c_3898,c_59,c_63]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_4256,plain,
% 3.52/0.98      ( r1_tmap_1(X0,sK5,k3_tmap_1(X1,sK5,sK7,X0,sK8),X2) != iProver_top
% 3.52/0.98      | r1_tmap_1(sK7,sK5,sK8,X2) = iProver_top
% 3.52/0.98      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 3.52/0.98      | m1_subset_1(X2,u1_struct_0(sK7)) != iProver_top
% 3.52/0.98      | r2_hidden(u1_struct_0(X0),u1_pre_topc(sK7)) != iProver_top
% 3.52/0.98      | m1_pre_topc(X0,sK7) != iProver_top
% 3.52/0.98      | m1_pre_topc(sK7,X1) != iProver_top
% 3.52/0.98      | v2_struct_0(X1) = iProver_top
% 3.52/0.98      | v2_struct_0(X0) = iProver_top
% 3.52/0.98      | l1_pre_topc(X1) != iProver_top
% 3.52/0.98      | v2_pre_topc(X1) != iProver_top ),
% 3.52/0.98      inference(renaming,[status(thm)],[c_4255]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_4272,plain,
% 3.52/0.98      ( r1_tmap_1(sK7,sK5,sK8,sK9) = iProver_top
% 3.52/0.98      | m1_subset_1(sK9,u1_struct_0(sK6)) != iProver_top
% 3.52/0.98      | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
% 3.52/0.98      | r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK7)) != iProver_top
% 3.52/0.98      | m1_pre_topc(sK6,sK7) != iProver_top
% 3.52/0.98      | m1_pre_topc(sK7,sK4) != iProver_top
% 3.52/0.98      | v2_struct_0(sK4) = iProver_top
% 3.52/0.98      | v2_struct_0(sK6) = iProver_top
% 3.52/0.98      | l1_pre_topc(sK4) != iProver_top
% 3.52/0.98      | v2_pre_topc(sK4) != iProver_top ),
% 3.52/0.98      inference(superposition,[status(thm)],[c_2970,c_4256]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_50,negated_conjecture,
% 3.52/0.98      ( ~ v2_struct_0(sK4) ),
% 3.52/0.98      inference(cnf_transformation,[],[f97]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_51,plain,
% 3.52/0.98      ( v2_struct_0(sK4) != iProver_top ),
% 3.52/0.98      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_44,negated_conjecture,
% 3.52/0.98      ( ~ v2_struct_0(sK6) ),
% 3.52/0.98      inference(cnf_transformation,[],[f103]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_57,plain,
% 3.52/0.98      ( v2_struct_0(sK6) != iProver_top ),
% 3.52/0.98      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_60,plain,
% 3.52/0.98      ( m1_pre_topc(sK7,sK4) = iProver_top ),
% 3.52/0.98      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_36,negated_conjecture,
% 3.52/0.98      ( m1_subset_1(sK9,u1_struct_0(sK7)) ),
% 3.52/0.98      inference(cnf_transformation,[],[f111]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_64,plain,
% 3.52/0.98      ( m1_subset_1(sK9,u1_struct_0(sK7)) = iProver_top ),
% 3.52/0.98      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_32,negated_conjecture,
% 3.52/0.98      ( ~ r1_tmap_1(sK7,sK5,sK8,sK9) ),
% 3.52/0.98      inference(cnf_transformation,[],[f115]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_67,plain,
% 3.52/0.98      ( r1_tmap_1(sK7,sK5,sK8,sK9) != iProver_top ),
% 3.52/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_35,negated_conjecture,
% 3.52/0.98      ( m1_subset_1(sK10,u1_struct_0(sK6)) ),
% 3.52/0.98      inference(cnf_transformation,[],[f112]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_2906,plain,
% 3.52/0.98      ( m1_subset_1(sK10,u1_struct_0(sK6)) = iProver_top ),
% 3.52/0.98      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_2957,plain,
% 3.52/0.98      ( m1_subset_1(sK9,u1_struct_0(sK6)) = iProver_top ),
% 3.52/0.98      inference(light_normalisation,[status(thm)],[c_2906,c_34]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_4401,plain,
% 3.52/0.98      ( m1_pre_topc(sK6,sK7) != iProver_top
% 3.52/0.98      | r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK7)) != iProver_top ),
% 3.52/0.98      inference(global_propositional_subsumption,
% 3.52/0.98                [status(thm)],
% 3.52/0.98                [c_4272,c_51,c_52,c_53,c_57,c_60,c_64,c_67,c_2957]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_4402,plain,
% 3.52/0.98      ( r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK7)) != iProver_top
% 3.52/0.98      | m1_pre_topc(sK6,sK7) != iProver_top ),
% 3.52/0.98      inference(renaming,[status(thm)],[c_4401]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_7492,plain,
% 3.52/0.98      ( r2_hidden(u1_struct_0(sK7),u1_pre_topc(sK7)) != iProver_top
% 3.52/0.98      | m1_pre_topc(sK6,sK7) != iProver_top ),
% 3.52/0.98      inference(demodulation,[status(thm)],[c_7488,c_4402]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_5642,plain,
% 3.52/0.98      ( l1_pre_topc(sK4) != iProver_top
% 3.52/0.98      | v2_pre_topc(sK4) != iProver_top
% 3.52/0.98      | v2_pre_topc(sK7) = iProver_top ),
% 3.52/0.98      inference(superposition,[status(thm)],[c_2903,c_2928]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_15,plain,
% 3.52/0.98      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
% 3.52/0.98      | ~ l1_pre_topc(X0)
% 3.52/0.98      | ~ v2_pre_topc(X0) ),
% 3.52/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_5085,plain,
% 3.52/0.98      ( r2_hidden(u1_struct_0(sK7),u1_pre_topc(sK7))
% 3.52/0.98      | ~ l1_pre_topc(sK7)
% 3.52/0.98      | ~ v2_pre_topc(sK7) ),
% 3.52/0.98      inference(instantiation,[status(thm)],[c_15]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_5086,plain,
% 3.52/0.98      ( r2_hidden(u1_struct_0(sK7),u1_pre_topc(sK7)) = iProver_top
% 3.52/0.98      | l1_pre_topc(sK7) != iProver_top
% 3.52/0.98      | v2_pre_topc(sK7) != iProver_top ),
% 3.52/0.98      inference(predicate_to_equality,[status(thm)],[c_5085]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(contradiction,plain,
% 3.52/0.98      ( $false ),
% 3.52/0.98      inference(minisat,
% 3.52/0.98                [status(thm)],
% 3.52/0.98                [c_7492,c_5642,c_5086,c_4748,c_4747,c_4168,c_53,c_52]) ).
% 3.52/0.98  
% 3.52/0.98  
% 3.52/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.52/0.98  
% 3.52/0.98  ------                               Statistics
% 3.52/0.98  
% 3.52/0.98  ------ General
% 3.52/0.98  
% 3.52/0.98  abstr_ref_over_cycles:                  0
% 3.52/0.98  abstr_ref_under_cycles:                 0
% 3.52/0.98  gc_basic_clause_elim:                   0
% 3.52/0.98  forced_gc_time:                         0
% 3.52/0.98  parsing_time:                           0.012
% 3.52/0.98  unif_index_cands_time:                  0.
% 3.52/0.98  unif_index_add_time:                    0.
% 3.52/0.98  orderings_time:                         0.
% 3.52/0.98  out_proof_time:                         0.022
% 3.52/0.98  total_time:                             0.291
% 3.52/0.98  num_of_symbols:                         62
% 3.52/0.98  num_of_terms:                           3798
% 3.52/0.98  
% 3.52/0.98  ------ Preprocessing
% 3.52/0.98  
% 3.52/0.98  num_of_splits:                          0
% 3.52/0.98  num_of_split_atoms:                     0
% 3.52/0.98  num_of_reused_defs:                     0
% 3.52/0.98  num_eq_ax_congr_red:                    15
% 3.52/0.98  num_of_sem_filtered_clauses:            1
% 3.52/0.98  num_of_subtypes:                        0
% 3.52/0.98  monotx_restored_types:                  0
% 3.52/0.98  sat_num_of_epr_types:                   0
% 3.52/0.98  sat_num_of_non_cyclic_types:            0
% 3.52/0.98  sat_guarded_non_collapsed_types:        0
% 3.52/0.98  num_pure_diseq_elim:                    0
% 3.52/0.98  simp_replaced_by:                       0
% 3.52/0.98  res_preprocessed:                       211
% 3.52/0.98  prep_upred:                             0
% 3.52/0.98  prep_unflattend:                        22
% 3.52/0.98  smt_new_axioms:                         0
% 3.52/0.98  pred_elim_cands:                        9
% 3.52/0.98  pred_elim:                              4
% 3.52/0.98  pred_elim_cl:                           6
% 3.52/0.98  pred_elim_cycles:                       6
% 3.52/0.98  merged_defs:                            0
% 3.52/0.98  merged_defs_ncl:                        0
% 3.52/0.98  bin_hyper_res:                          0
% 3.52/0.98  prep_cycles:                            4
% 3.52/0.98  pred_elim_time:                         0.039
% 3.52/0.98  splitting_time:                         0.
% 3.52/0.98  sem_filter_time:                        0.
% 3.52/0.98  monotx_time:                            0.001
% 3.52/0.98  subtype_inf_time:                       0.
% 3.52/0.98  
% 3.52/0.98  ------ Problem properties
% 3.52/0.98  
% 3.52/0.98  clauses:                                42
% 3.52/0.98  conjectures:                            17
% 3.52/0.98  epr:                                    19
% 3.52/0.98  horn:                                   34
% 3.52/0.98  ground:                                 17
% 3.52/0.98  unary:                                  18
% 3.52/0.98  binary:                                 6
% 3.52/0.98  lits:                                   134
% 3.52/0.98  lits_eq:                                7
% 3.52/0.98  fd_pure:                                0
% 3.52/0.98  fd_pseudo:                              0
% 3.52/0.98  fd_cond:                                0
% 3.52/0.98  fd_pseudo_cond:                         1
% 3.52/0.98  ac_symbols:                             0
% 3.52/0.98  
% 3.52/0.98  ------ Propositional Solver
% 3.52/0.98  
% 3.52/0.98  prop_solver_calls:                      28
% 3.52/0.98  prop_fast_solver_calls:                 2112
% 3.52/0.98  smt_solver_calls:                       0
% 3.52/0.98  smt_fast_solver_calls:                  0
% 3.52/0.98  prop_num_of_clauses:                    1920
% 3.52/0.98  prop_preprocess_simplified:             7971
% 3.52/0.98  prop_fo_subsumed:                       56
% 3.52/0.98  prop_solver_time:                       0.
% 3.52/0.98  smt_solver_time:                        0.
% 3.52/0.98  smt_fast_solver_time:                   0.
% 3.52/0.98  prop_fast_solver_time:                  0.
% 3.52/0.98  prop_unsat_core_time:                   0.
% 3.52/0.98  
% 3.52/0.98  ------ QBF
% 3.52/0.98  
% 3.52/0.98  qbf_q_res:                              0
% 3.52/0.98  qbf_num_tautologies:                    0
% 3.52/0.98  qbf_prep_cycles:                        0
% 3.52/0.98  
% 3.52/0.98  ------ BMC1
% 3.52/0.98  
% 3.52/0.98  bmc1_current_bound:                     -1
% 3.52/0.98  bmc1_last_solved_bound:                 -1
% 3.52/0.98  bmc1_unsat_core_size:                   -1
% 3.52/0.98  bmc1_unsat_core_parents_size:           -1
% 3.52/0.98  bmc1_merge_next_fun:                    0
% 3.52/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.52/0.98  
% 3.52/0.98  ------ Instantiation
% 3.52/0.98  
% 3.52/0.98  inst_num_of_clauses:                    565
% 3.52/0.98  inst_num_in_passive:                    129
% 3.52/0.98  inst_num_in_active:                     365
% 3.52/0.98  inst_num_in_unprocessed:                71
% 3.52/0.98  inst_num_of_loops:                      380
% 3.52/0.98  inst_num_of_learning_restarts:          0
% 3.52/0.98  inst_num_moves_active_passive:          11
% 3.52/0.98  inst_lit_activity:                      0
% 3.52/0.98  inst_lit_activity_moves:                0
% 3.52/0.98  inst_num_tautologies:                   0
% 3.52/0.98  inst_num_prop_implied:                  0
% 3.52/0.98  inst_num_existing_simplified:           0
% 3.52/0.98  inst_num_eq_res_simplified:             0
% 3.52/0.98  inst_num_child_elim:                    0
% 3.52/0.98  inst_num_of_dismatching_blockings:      160
% 3.52/0.98  inst_num_of_non_proper_insts:           855
% 3.52/0.98  inst_num_of_duplicates:                 0
% 3.52/0.98  inst_inst_num_from_inst_to_res:         0
% 3.52/0.98  inst_dismatching_checking_time:         0.
% 3.52/0.98  
% 3.52/0.98  ------ Resolution
% 3.52/0.98  
% 3.52/0.98  res_num_of_clauses:                     0
% 3.52/0.98  res_num_in_passive:                     0
% 3.52/0.98  res_num_in_active:                      0
% 3.52/0.98  res_num_of_loops:                       215
% 3.52/0.98  res_forward_subset_subsumed:            133
% 3.52/0.98  res_backward_subset_subsumed:           0
% 3.52/0.98  res_forward_subsumed:                   0
% 3.52/0.98  res_backward_subsumed:                  0
% 3.52/0.98  res_forward_subsumption_resolution:     6
% 3.52/0.98  res_backward_subsumption_resolution:    0
% 3.52/0.98  res_clause_to_clause_subsumption:       459
% 3.52/0.98  res_orphan_elimination:                 0
% 3.52/0.98  res_tautology_del:                      113
% 3.52/0.98  res_num_eq_res_simplified:              0
% 3.52/0.98  res_num_sel_changes:                    0
% 3.52/0.98  res_moves_from_active_to_pass:          0
% 3.52/0.98  
% 3.52/0.98  ------ Superposition
% 3.52/0.98  
% 3.52/0.98  sup_time_total:                         0.
% 3.52/0.98  sup_time_generating:                    0.
% 3.52/0.98  sup_time_sim_full:                      0.
% 3.52/0.98  sup_time_sim_immed:                     0.
% 3.52/0.98  
% 3.52/0.98  sup_num_of_clauses:                     91
% 3.52/0.98  sup_num_in_active:                      68
% 3.52/0.98  sup_num_in_passive:                     23
% 3.52/0.98  sup_num_of_loops:                       74
% 3.52/0.98  sup_fw_superposition:                   58
% 3.52/0.98  sup_bw_superposition:                   51
% 3.52/0.98  sup_immediate_simplified:               23
% 3.52/0.98  sup_given_eliminated:                   0
% 3.52/0.98  comparisons_done:                       0
% 3.52/0.98  comparisons_avoided:                    0
% 3.52/0.98  
% 3.52/0.98  ------ Simplifications
% 3.52/0.98  
% 3.52/0.98  
% 3.52/0.98  sim_fw_subset_subsumed:                 11
% 3.52/0.98  sim_bw_subset_subsumed:                 5
% 3.52/0.98  sim_fw_subsumed:                        9
% 3.52/0.98  sim_bw_subsumed:                        3
% 3.52/0.98  sim_fw_subsumption_res:                 1
% 3.52/0.98  sim_bw_subsumption_res:                 0
% 3.52/0.98  sim_tautology_del:                      19
% 3.52/0.98  sim_eq_tautology_del:                   2
% 3.52/0.98  sim_eq_res_simp:                        0
% 3.52/0.98  sim_fw_demodulated:                     0
% 3.52/0.98  sim_bw_demodulated:                     4
% 3.52/0.98  sim_light_normalised:                   4
% 3.52/0.98  sim_joinable_taut:                      0
% 3.52/0.98  sim_joinable_simp:                      0
% 3.52/0.98  sim_ac_normalised:                      0
% 3.52/0.98  sim_smt_subsumption:                    0
% 3.52/0.98  
%------------------------------------------------------------------------------
