%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:30 EST 2020

% Result     : Theorem 15.31s
% Output     : CNFRefutation 15.31s
% Verified   : 
% Statistics : Number of formulae       :  234 (2097 expanded)
%              Number of clauses        :  133 ( 477 expanded)
%              Number of leaves         :   27 ( 908 expanded)
%              Depth                    :   19
%              Number of atoms          : 1051 (28451 expanded)
%              Number of equality atoms :  292 (4177 expanded)
%              Maximal formula depth    :   32 (   5 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f113,conjecture,(
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

fof(f114,negated_conjecture,(
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
    inference(negated_conjecture,[],[f113])).

fof(f249,plain,(
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
    inference(ennf_transformation,[],[f114])).

fof(f250,plain,(
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
    inference(flattening,[],[f249])).

fof(f380,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ~ r1_tmap_1(X3,X1,X4,X5)
          & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
          & X5 = X6
          & m1_subset_1(X6,u1_struct_0(X2)) )
     => ( ~ r1_tmap_1(X3,X1,X4,X5)
        & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK55)
        & sK55 = X5
        & m1_subset_1(sK55,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f379,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ~ r1_tmap_1(X3,X1,X4,X5)
              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
              & X5 = X6
              & m1_subset_1(X6,u1_struct_0(X2)) )
          & m1_subset_1(X5,u1_struct_0(X3)) )
     => ( ? [X6] :
            ( ~ r1_tmap_1(X3,X1,X4,sK54)
            & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
            & sK54 = X6
            & m1_subset_1(X6,u1_struct_0(X2)) )
        & m1_subset_1(sK54,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f378,plain,(
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
                ( ~ r1_tmap_1(X3,X1,sK53,X5)
                & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK53),X6)
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(X2)) )
            & m1_subset_1(X5,u1_struct_0(X3)) )
        & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
        & m1_subset_1(sK53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(sK53,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK53) ) ) ),
    introduced(choice_axiom,[])).

fof(f377,plain,(
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
                    ( ~ r1_tmap_1(sK52,X1,X4,X5)
                    & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK52,X2,X4),X6)
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(X2)) )
                & m1_subset_1(X5,u1_struct_0(sK52)) )
            & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK52
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK52),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(sK52),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK52,X0)
        & ~ v2_struct_0(sK52) ) ) ),
    introduced(choice_axiom,[])).

fof(f376,plain,(
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
                        & r1_tmap_1(sK51,X1,k3_tmap_1(X0,X1,X3,sK51,X4),X6)
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(sK51)) )
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & g1_pre_topc(u1_struct_0(sK51),u1_pre_topc(sK51)) = X3
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK51,X0)
        & ~ v2_struct_0(sK51) ) ) ),
    introduced(choice_axiom,[])).

fof(f375,plain,(
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
                            ( ~ r1_tmap_1(X3,sK50,X4,X5)
                            & r1_tmap_1(X2,sK50,k3_tmap_1(X0,sK50,X3,X2,X4),X6)
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK50))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK50))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK50)
        & v2_pre_topc(sK50)
        & ~ v2_struct_0(sK50) ) ) ),
    introduced(choice_axiom,[])).

fof(f374,plain,
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
                              & r1_tmap_1(X2,X1,k3_tmap_1(sK49,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK49)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK49)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK49)
      & v2_pre_topc(sK49)
      & ~ v2_struct_0(sK49) ) ),
    introduced(choice_axiom,[])).

fof(f381,plain,
    ( ~ r1_tmap_1(sK52,sK50,sK53,sK54)
    & r1_tmap_1(sK51,sK50,k3_tmap_1(sK49,sK50,sK52,sK51,sK53),sK55)
    & sK54 = sK55
    & m1_subset_1(sK55,u1_struct_0(sK51))
    & m1_subset_1(sK54,u1_struct_0(sK52))
    & g1_pre_topc(u1_struct_0(sK51),u1_pre_topc(sK51)) = sK52
    & m1_subset_1(sK53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK52),u1_struct_0(sK50))))
    & v1_funct_2(sK53,u1_struct_0(sK52),u1_struct_0(sK50))
    & v1_funct_1(sK53)
    & m1_pre_topc(sK52,sK49)
    & ~ v2_struct_0(sK52)
    & m1_pre_topc(sK51,sK49)
    & ~ v2_struct_0(sK51)
    & l1_pre_topc(sK50)
    & v2_pre_topc(sK50)
    & ~ v2_struct_0(sK50)
    & l1_pre_topc(sK49)
    & v2_pre_topc(sK49)
    & ~ v2_struct_0(sK49) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK49,sK50,sK51,sK52,sK53,sK54,sK55])],[f250,f380,f379,f378,f377,f376,f375,f374])).

fof(f607,plain,(
    m1_subset_1(sK54,u1_struct_0(sK52)) ),
    inference(cnf_transformation,[],[f381])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f147,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f148,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f147])).

fof(f417,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f148])).

fof(f595,plain,(
    l1_pre_topc(sK49) ),
    inference(cnf_transformation,[],[f381])).

fof(f601,plain,(
    ~ v2_struct_0(sK52) ),
    inference(cnf_transformation,[],[f381])).

fof(f602,plain,(
    m1_pre_topc(sK52,sK49) ),
    inference(cnf_transformation,[],[f381])).

fof(f62,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f185,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f62])).

fof(f506,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f185])).

fof(f69,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f191,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f69])).

fof(f192,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f191])).

fof(f513,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f192])).

fof(f63,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f186,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f63])).

fof(f507,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f186])).

fof(f60,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f183,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f60])).

fof(f504,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f183])).

fof(f103,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f234,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f103])).

fof(f572,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f234])).

fof(f610,plain,(
    r1_tmap_1(sK51,sK50,k3_tmap_1(sK49,sK50,sK52,sK51,sK53),sK55) ),
    inference(cnf_transformation,[],[f381])).

fof(f609,plain,(
    sK54 = sK55 ),
    inference(cnf_transformation,[],[f381])).

fof(f111,axiom,(
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
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X3))
                               => ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X2))
                                   => ( ( X6 = X7
                                        & r1_tarski(X5,u1_struct_0(X2))
                                        & r2_hidden(X6,X5)
                                        & v3_pre_topc(X5,X3) )
                                     => ( r1_tmap_1(X3,X1,X4,X6)
                                      <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f245,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
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
    inference(ennf_transformation,[],[f111])).

fof(f246,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
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
    inference(flattening,[],[f245])).

fof(f372,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( ( r1_tmap_1(X3,X1,X4,X6)
                                      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                    & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                                      | ~ r1_tmap_1(X3,X1,X4,X6) ) )
                                  | X6 != X7
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
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
    inference(nnf_transformation,[],[f246])).

fof(f590,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X6)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | X6 != X7
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X6,X5)
      | ~ v3_pre_topc(X5,X3)
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
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
    inference(cnf_transformation,[],[f372])).

fof(f631,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X7)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X7,X5)
      | ~ v3_pre_topc(X5,X3)
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
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
    inference(equality_resolution,[],[f590])).

fof(f593,plain,(
    ~ v2_struct_0(sK49) ),
    inference(cnf_transformation,[],[f381])).

fof(f594,plain,(
    v2_pre_topc(sK49) ),
    inference(cnf_transformation,[],[f381])).

fof(f596,plain,(
    ~ v2_struct_0(sK50) ),
    inference(cnf_transformation,[],[f381])).

fof(f597,plain,(
    v2_pre_topc(sK50) ),
    inference(cnf_transformation,[],[f381])).

fof(f598,plain,(
    l1_pre_topc(sK50) ),
    inference(cnf_transformation,[],[f381])).

fof(f599,plain,(
    ~ v2_struct_0(sK51) ),
    inference(cnf_transformation,[],[f381])).

fof(f600,plain,(
    m1_pre_topc(sK51,sK49) ),
    inference(cnf_transformation,[],[f381])).

fof(f603,plain,(
    v1_funct_1(sK53) ),
    inference(cnf_transformation,[],[f381])).

fof(f604,plain,(
    v1_funct_2(sK53,u1_struct_0(sK52),u1_struct_0(sK50)) ),
    inference(cnf_transformation,[],[f381])).

fof(f605,plain,(
    m1_subset_1(sK53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK52),u1_struct_0(sK50)))) ),
    inference(cnf_transformation,[],[f381])).

fof(f611,plain,(
    ~ r1_tmap_1(sK52,sK50,sK53,sK54) ),
    inference(cnf_transformation,[],[f381])).

fof(f608,plain,(
    m1_subset_1(sK55,u1_struct_0(sK51)) ),
    inference(cnf_transformation,[],[f381])).

fof(f104,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f235,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f104])).

fof(f573,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f235])).

fof(f606,plain,(
    g1_pre_topc(u1_struct_0(sK51),u1_pre_topc(sK51)) = sK52 ),
    inference(cnf_transformation,[],[f381])).

fof(f83,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f215,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f83])).

fof(f336,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f215])).

fof(f540,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f336])).

fof(f102,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
               => ( m1_pre_topc(X1,X0)
                <=> m1_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f232,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f102])).

fof(f233,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f232])).

fof(f359,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  | ~ m1_pre_topc(X2,X0) )
                & ( m1_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0) ) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f233])).

fof(f571,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f359])).

fof(f629,plain,(
    ! [X2,X0] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f571])).

fof(f77,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f204,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f77])).

fof(f205,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f204])).

fof(f526,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f205])).

fof(f58,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f179,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f58])).

fof(f180,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f179])).

fof(f502,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f180])).

fof(f109,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f243,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f109])).

fof(f244,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f243])).

fof(f588,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f244])).

fof(f105,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f236,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f105])).

fof(f574,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f236])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f276,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f419,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f276])).

fof(f107,axiom,(
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

fof(f239,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f107])).

fof(f240,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f239])).

fof(f364,plain,(
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
    inference(nnf_transformation,[],[f240])).

fof(f579,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f364])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f261,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f262,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f261])).

fof(f388,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f262])).

fof(f90,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f221,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f90])).

fof(f222,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f221])).

fof(f547,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f222])).

cnf(c_215,negated_conjecture,
    ( m1_subset_1(sK54,u1_struct_0(sK52)) ),
    inference(cnf_transformation,[],[f607])).

cnf(c_13539,plain,
    ( m1_subset_1(sK54,u1_struct_0(sK52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_215])).

cnf(c_35,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f417])).

cnf(c_13682,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_32581,plain,
    ( r2_hidden(sK54,u1_struct_0(sK52)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK52)) = iProver_top ),
    inference(superposition,[status(thm)],[c_13539,c_13682])).

cnf(c_227,negated_conjecture,
    ( l1_pre_topc(sK49) ),
    inference(cnf_transformation,[],[f595])).

cnf(c_232,plain,
    ( l1_pre_topc(sK49) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_227])).

cnf(c_221,negated_conjecture,
    ( ~ v2_struct_0(sK52) ),
    inference(cnf_transformation,[],[f601])).

cnf(c_238,plain,
    ( v2_struct_0(sK52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_221])).

cnf(c_220,negated_conjecture,
    ( m1_pre_topc(sK52,sK49) ),
    inference(cnf_transformation,[],[f602])).

cnf(c_239,plain,
    ( m1_pre_topc(sK52,sK49) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_220])).

cnf(c_124,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f506])).

cnf(c_131,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0)) ),
    inference(cnf_transformation,[],[f513])).

cnf(c_2680,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(k2_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_124,c_131])).

cnf(c_13984,plain,
    ( v2_struct_0(sK52)
    | ~ l1_pre_topc(sK52)
    | ~ v1_xboole_0(k2_struct_0(sK52)) ),
    inference(instantiation,[status(thm)],[c_2680])).

cnf(c_13985,plain,
    ( v2_struct_0(sK52) = iProver_top
    | l1_pre_topc(sK52) != iProver_top
    | v1_xboole_0(k2_struct_0(sK52)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13984])).

cnf(c_125,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f507])).

cnf(c_14331,plain,
    ( ~ m1_pre_topc(sK52,X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(sK52) ),
    inference(instantiation,[status(thm)],[c_125])).

cnf(c_16931,plain,
    ( ~ m1_pre_topc(sK52,sK49)
    | ~ l1_pre_topc(sK49)
    | l1_pre_topc(sK52) ),
    inference(instantiation,[status(thm)],[c_14331])).

cnf(c_16932,plain,
    ( m1_pre_topc(sK52,sK49) != iProver_top
    | l1_pre_topc(sK49) != iProver_top
    | l1_pre_topc(sK52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16931])).

cnf(c_9615,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_18342,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_struct_0(sK52))
    | k2_struct_0(sK52) != X0 ),
    inference(instantiation,[status(thm)],[c_9615])).

cnf(c_26440,plain,
    ( v1_xboole_0(k2_struct_0(sK52))
    | ~ v1_xboole_0(u1_struct_0(sK52))
    | k2_struct_0(sK52) != u1_struct_0(sK52) ),
    inference(instantiation,[status(thm)],[c_18342])).

cnf(c_26441,plain,
    ( k2_struct_0(sK52) != u1_struct_0(sK52)
    | v1_xboole_0(k2_struct_0(sK52)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK52)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26440])).

cnf(c_13535,plain,
    ( m1_pre_topc(sK52,sK49) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_220])).

cnf(c_13621,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_125])).

cnf(c_32550,plain,
    ( l1_pre_topc(sK49) != iProver_top
    | l1_pre_topc(sK52) = iProver_top ),
    inference(superposition,[status(thm)],[c_13535,c_13621])).

cnf(c_32766,plain,
    ( l1_pre_topc(sK52) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_32550,c_232,c_239,c_16932])).

cnf(c_122,plain,
    ( ~ l1_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f504])).

cnf(c_2705,plain,
    ( ~ l1_pre_topc(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_124,c_122])).

cnf(c_13515,plain,
    ( k2_struct_0(X0) = u1_struct_0(X0)
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2705])).

cnf(c_32771,plain,
    ( k2_struct_0(sK52) = u1_struct_0(sK52) ),
    inference(superposition,[status(thm)],[c_32766,c_13515])).

cnf(c_32856,plain,
    ( r2_hidden(sK54,u1_struct_0(sK52)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_32581,c_232,c_238,c_239,c_13985,c_16932,c_26441,c_32771])).

cnf(c_190,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f572])).

cnf(c_13563,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_190])).

cnf(c_212,negated_conjecture,
    ( r1_tmap_1(sK51,sK50,k3_tmap_1(sK49,sK50,sK52,sK51,sK53),sK55) ),
    inference(cnf_transformation,[],[f610])).

cnf(c_13541,plain,
    ( r1_tmap_1(sK51,sK50,k3_tmap_1(sK49,sK50,sK52,sK51,sK53),sK55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_212])).

cnf(c_213,negated_conjecture,
    ( sK54 = sK55 ),
    inference(cnf_transformation,[],[f609])).

cnf(c_13708,plain,
    ( r1_tmap_1(sK51,sK50,k3_tmap_1(sK49,sK50,sK52,sK51,sK53),sK54) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13541,c_213])).

cnf(c_207,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(X6,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ r2_hidden(X3,X6)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f631])).

cnf(c_13546,plain,
    ( r1_tmap_1(X0,X1,X2,X3) = iProver_top
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3) != iProver_top
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | v3_pre_topc(X6,X0) != iProver_top
    | m1_pre_topc(X4,X5) != iProver_top
    | m1_pre_topc(X0,X5) != iProver_top
    | m1_pre_topc(X4,X0) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X4)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r1_tarski(X6,u1_struct_0(X4)) != iProver_top
    | r2_hidden(X3,X6) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X5) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X4) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X5) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X5) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_207])).

cnf(c_33462,plain,
    ( r1_tmap_1(sK52,sK50,sK53,sK54) = iProver_top
    | v1_funct_2(sK53,u1_struct_0(sK52),u1_struct_0(sK50)) != iProver_top
    | v3_pre_topc(X0,sK52) != iProver_top
    | m1_pre_topc(sK51,sK49) != iProver_top
    | m1_pre_topc(sK51,sK52) != iProver_top
    | m1_pre_topc(sK52,sK49) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK52))) != iProver_top
    | m1_subset_1(sK54,u1_struct_0(sK51)) != iProver_top
    | m1_subset_1(sK54,u1_struct_0(sK52)) != iProver_top
    | m1_subset_1(sK53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK52),u1_struct_0(sK50)))) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK51)) != iProver_top
    | r2_hidden(sK54,X0) != iProver_top
    | v2_struct_0(sK49) = iProver_top
    | v2_struct_0(sK51) = iProver_top
    | v2_struct_0(sK50) = iProver_top
    | v2_struct_0(sK52) = iProver_top
    | l1_pre_topc(sK49) != iProver_top
    | l1_pre_topc(sK50) != iProver_top
    | v2_pre_topc(sK49) != iProver_top
    | v2_pre_topc(sK50) != iProver_top
    | v1_funct_1(sK53) != iProver_top ),
    inference(superposition,[status(thm)],[c_13708,c_13546])).

cnf(c_229,negated_conjecture,
    ( ~ v2_struct_0(sK49) ),
    inference(cnf_transformation,[],[f593])).

cnf(c_230,plain,
    ( v2_struct_0(sK49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_229])).

cnf(c_228,negated_conjecture,
    ( v2_pre_topc(sK49) ),
    inference(cnf_transformation,[],[f594])).

cnf(c_231,plain,
    ( v2_pre_topc(sK49) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_228])).

cnf(c_226,negated_conjecture,
    ( ~ v2_struct_0(sK50) ),
    inference(cnf_transformation,[],[f596])).

cnf(c_233,plain,
    ( v2_struct_0(sK50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_226])).

cnf(c_225,negated_conjecture,
    ( v2_pre_topc(sK50) ),
    inference(cnf_transformation,[],[f597])).

cnf(c_234,plain,
    ( v2_pre_topc(sK50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_225])).

cnf(c_224,negated_conjecture,
    ( l1_pre_topc(sK50) ),
    inference(cnf_transformation,[],[f598])).

cnf(c_235,plain,
    ( l1_pre_topc(sK50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_224])).

cnf(c_223,negated_conjecture,
    ( ~ v2_struct_0(sK51) ),
    inference(cnf_transformation,[],[f599])).

cnf(c_236,plain,
    ( v2_struct_0(sK51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_223])).

cnf(c_222,negated_conjecture,
    ( m1_pre_topc(sK51,sK49) ),
    inference(cnf_transformation,[],[f600])).

cnf(c_237,plain,
    ( m1_pre_topc(sK51,sK49) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_222])).

cnf(c_219,negated_conjecture,
    ( v1_funct_1(sK53) ),
    inference(cnf_transformation,[],[f603])).

cnf(c_240,plain,
    ( v1_funct_1(sK53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_219])).

cnf(c_218,negated_conjecture,
    ( v1_funct_2(sK53,u1_struct_0(sK52),u1_struct_0(sK50)) ),
    inference(cnf_transformation,[],[f604])).

cnf(c_241,plain,
    ( v1_funct_2(sK53,u1_struct_0(sK52),u1_struct_0(sK50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_218])).

cnf(c_217,negated_conjecture,
    ( m1_subset_1(sK53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK52),u1_struct_0(sK50)))) ),
    inference(cnf_transformation,[],[f605])).

cnf(c_242,plain,
    ( m1_subset_1(sK53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK52),u1_struct_0(sK50)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_217])).

cnf(c_243,plain,
    ( m1_subset_1(sK54,u1_struct_0(sK52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_215])).

cnf(c_211,negated_conjecture,
    ( ~ r1_tmap_1(sK52,sK50,sK53,sK54) ),
    inference(cnf_transformation,[],[f611])).

cnf(c_246,plain,
    ( r1_tmap_1(sK52,sK50,sK53,sK54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_211])).

cnf(c_214,negated_conjecture,
    ( m1_subset_1(sK55,u1_struct_0(sK51)) ),
    inference(cnf_transformation,[],[f608])).

cnf(c_13540,plain,
    ( m1_subset_1(sK55,u1_struct_0(sK51)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_214])).

cnf(c_13700,plain,
    ( m1_subset_1(sK54,u1_struct_0(sK51)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13540,c_213])).

cnf(c_14425,plain,
    ( ~ m1_pre_topc(sK51,X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(sK51) ),
    inference(instantiation,[status(thm)],[c_125])).

cnf(c_16969,plain,
    ( ~ m1_pre_topc(sK51,sK49)
    | ~ l1_pre_topc(sK49)
    | l1_pre_topc(sK51) ),
    inference(instantiation,[status(thm)],[c_14425])).

cnf(c_16970,plain,
    ( m1_pre_topc(sK51,sK49) != iProver_top
    | l1_pre_topc(sK49) != iProver_top
    | l1_pre_topc(sK51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16969])).

cnf(c_191,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f573])).

cnf(c_13562,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_191])).

cnf(c_216,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK51),u1_pre_topc(sK51)) = sK52 ),
    inference(cnf_transformation,[],[f606])).

cnf(c_159,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f540])).

cnf(c_1232,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_159,c_125])).

cnf(c_1233,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_1232])).

cnf(c_13523,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1233])).

cnf(c_27301,plain,
    ( m1_pre_topc(X0,sK51) != iProver_top
    | m1_pre_topc(X0,sK52) = iProver_top
    | l1_pre_topc(sK51) != iProver_top ),
    inference(superposition,[status(thm)],[c_216,c_13523])).

cnf(c_27436,plain,
    ( m1_pre_topc(X0,sK52) = iProver_top
    | m1_pre_topc(X0,sK51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27301,c_232,c_237,c_16970])).

cnf(c_27437,plain,
    ( m1_pre_topc(X0,sK51) != iProver_top
    | m1_pre_topc(X0,sK52) = iProver_top ),
    inference(renaming,[status(thm)],[c_27436])).

cnf(c_27443,plain,
    ( m1_pre_topc(sK51,sK52) = iProver_top
    | l1_pre_topc(sK51) != iProver_top ),
    inference(superposition,[status(thm)],[c_13562,c_27437])).

cnf(c_34225,plain,
    ( r2_hidden(sK54,X0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK51)) != iProver_top
    | v3_pre_topc(X0,sK52) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK52))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_33462,c_230,c_231,c_232,c_233,c_234,c_235,c_236,c_237,c_238,c_239,c_240,c_241,c_242,c_243,c_246,c_13700,c_16970,c_27443])).

cnf(c_34226,plain,
    ( v3_pre_topc(X0,sK52) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK52))) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK51)) != iProver_top
    | r2_hidden(sK54,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_34225])).

cnf(c_43748,plain,
    ( v3_pre_topc(u1_struct_0(X0),sK52) != iProver_top
    | m1_pre_topc(X0,sK52) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK51)) != iProver_top
    | r2_hidden(sK54,u1_struct_0(X0)) != iProver_top
    | l1_pre_topc(sK52) != iProver_top ),
    inference(superposition,[status(thm)],[c_13563,c_34226])).

cnf(c_188,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f629])).

cnf(c_144,plain,
    ( ~ l1_pre_topc(X0)
    | v2_pre_topc(X0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f526])).

cnf(c_1197,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_188,c_144,c_125])).

cnf(c_1198,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(renaming,[status(thm)],[c_1197])).

cnf(c_13524,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1198])).

cnf(c_27807,plain,
    ( m1_pre_topc(sK51,X0) != iProver_top
    | m1_pre_topc(sK52,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK51),u1_pre_topc(sK51))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK51),u1_pre_topc(sK51))) != iProver_top ),
    inference(superposition,[status(thm)],[c_216,c_13524])).

cnf(c_27809,plain,
    ( m1_pre_topc(sK51,X0) != iProver_top
    | m1_pre_topc(sK52,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK52) != iProver_top
    | v2_pre_topc(sK52) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_27807,c_216])).

cnf(c_120,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f502])).

cnf(c_18312,plain,
    ( ~ m1_pre_topc(sK52,X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(sK52) ),
    inference(instantiation,[status(thm)],[c_120])).

cnf(c_27042,plain,
    ( ~ m1_pre_topc(sK52,sK49)
    | ~ l1_pre_topc(sK49)
    | ~ v2_pre_topc(sK49)
    | v2_pre_topc(sK52) ),
    inference(instantiation,[status(thm)],[c_18312])).

cnf(c_27043,plain,
    ( m1_pre_topc(sK52,sK49) != iProver_top
    | l1_pre_topc(sK49) != iProver_top
    | v2_pre_topc(sK49) != iProver_top
    | v2_pre_topc(sK52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27042])).

cnf(c_28376,plain,
    ( m1_pre_topc(sK51,X0) != iProver_top
    | m1_pre_topc(sK52,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27809,c_231,c_232,c_239,c_16932,c_27043])).

cnf(c_28383,plain,
    ( m1_pre_topc(sK52,sK51) = iProver_top
    | l1_pre_topc(sK51) != iProver_top ),
    inference(superposition,[status(thm)],[c_13562,c_28376])).

cnf(c_28516,plain,
    ( m1_pre_topc(sK52,sK51) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_28383,c_232,c_237,c_16970])).

cnf(c_206,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f588])).

cnf(c_13547,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X2,X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_206])).

cnf(c_34714,plain,
    ( m1_pre_topc(X0,sK51) = iProver_top
    | m1_pre_topc(X0,sK52) != iProver_top
    | l1_pre_topc(sK51) != iProver_top
    | v2_pre_topc(sK51) != iProver_top ),
    inference(superposition,[status(thm)],[c_28516,c_13547])).

cnf(c_18649,plain,
    ( ~ m1_pre_topc(sK51,X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(sK51) ),
    inference(instantiation,[status(thm)],[c_120])).

cnf(c_27087,plain,
    ( ~ m1_pre_topc(sK51,sK49)
    | ~ l1_pre_topc(sK49)
    | ~ v2_pre_topc(sK49)
    | v2_pre_topc(sK51) ),
    inference(instantiation,[status(thm)],[c_18649])).

cnf(c_27088,plain,
    ( m1_pre_topc(sK51,sK49) != iProver_top
    | l1_pre_topc(sK49) != iProver_top
    | v2_pre_topc(sK49) != iProver_top
    | v2_pre_topc(sK51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27087])).

cnf(c_39588,plain,
    ( m1_pre_topc(X0,sK51) = iProver_top
    | m1_pre_topc(X0,sK52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_34714,c_231,c_232,c_237,c_16970,c_27088])).

cnf(c_192,plain,
    ( ~ m1_pre_topc(X0,X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f574])).

cnf(c_13561,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_192])).

cnf(c_36,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f419])).

cnf(c_13674,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_34233,plain,
    ( v3_pre_topc(X0,sK52) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK51)) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK52)) != iProver_top
    | r2_hidden(sK54,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_13674,c_34226])).

cnf(c_40657,plain,
    ( v3_pre_topc(u1_struct_0(X0),sK52) != iProver_top
    | m1_pre_topc(X0,sK51) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK52)) != iProver_top
    | r2_hidden(sK54,u1_struct_0(X0)) != iProver_top
    | l1_pre_topc(sK51) != iProver_top ),
    inference(superposition,[status(thm)],[c_13561,c_34233])).

cnf(c_13533,plain,
    ( m1_pre_topc(sK51,sK49) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_222])).

cnf(c_196,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X2)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f579])).

cnf(c_13557,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_196])).

cnf(c_43546,plain,
    ( m1_pre_topc(X0,sK49) != iProver_top
    | m1_pre_topc(sK51,X0) != iProver_top
    | r1_tarski(u1_struct_0(sK51),u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(sK49) != iProver_top
    | v2_pre_topc(sK49) != iProver_top ),
    inference(superposition,[status(thm)],[c_13533,c_13557])).

cnf(c_44123,plain,
    ( m1_pre_topc(X0,sK49) != iProver_top
    | m1_pre_topc(sK51,X0) != iProver_top
    | r1_tarski(u1_struct_0(sK51),u1_struct_0(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_43546,c_231,c_232])).

cnf(c_43545,plain,
    ( m1_pre_topc(X0,sK49) != iProver_top
    | m1_pre_topc(sK52,X0) != iProver_top
    | r1_tarski(u1_struct_0(sK52),u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(sK49) != iProver_top
    | v2_pre_topc(sK49) != iProver_top ),
    inference(superposition,[status(thm)],[c_13535,c_13557])).

cnf(c_44103,plain,
    ( m1_pre_topc(X0,sK49) != iProver_top
    | m1_pre_topc(sK52,X0) != iProver_top
    | r1_tarski(u1_struct_0(sK52),u1_struct_0(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_43545,c_231,c_232])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f388])).

cnf(c_13695,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_44109,plain,
    ( u1_struct_0(X0) = u1_struct_0(sK52)
    | m1_pre_topc(X0,sK49) != iProver_top
    | m1_pre_topc(sK52,X0) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK52)) != iProver_top ),
    inference(superposition,[status(thm)],[c_44103,c_13695])).

cnf(c_44362,plain,
    ( u1_struct_0(sK52) = u1_struct_0(sK51)
    | m1_pre_topc(sK51,sK49) != iProver_top
    | m1_pre_topc(sK51,sK52) != iProver_top
    | m1_pre_topc(sK52,sK49) != iProver_top
    | m1_pre_topc(sK52,sK51) != iProver_top ),
    inference(superposition,[status(thm)],[c_44123,c_44109])).

cnf(c_45732,plain,
    ( u1_struct_0(sK52) = u1_struct_0(sK51) ),
    inference(global_propositional_subsumption,[status(thm)],[c_44362,c_232,c_237,c_239,c_16970,c_27443,c_28383])).

cnf(c_45814,plain,
    ( m1_pre_topc(X0,sK51) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK52)) = iProver_top
    | l1_pre_topc(sK51) != iProver_top ),
    inference(superposition,[status(thm)],[c_45732,c_13561])).

cnf(c_47274,plain,
    ( r2_hidden(sK54,u1_struct_0(X0)) != iProver_top
    | v3_pre_topc(u1_struct_0(X0),sK52) != iProver_top
    | m1_pre_topc(X0,sK52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_43748,c_231,c_232,c_237,c_16970,c_27088,c_34714,c_40657,c_45814])).

cnf(c_47275,plain,
    ( v3_pre_topc(u1_struct_0(X0),sK52) != iProver_top
    | m1_pre_topc(X0,sK52) != iProver_top
    | r2_hidden(sK54,u1_struct_0(X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_47274])).

cnf(c_47280,plain,
    ( v3_pre_topc(u1_struct_0(sK52),sK52) != iProver_top
    | m1_pre_topc(sK52,sK52) != iProver_top ),
    inference(superposition,[status(thm)],[c_32856,c_47275])).

cnf(c_165,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f547])).

cnf(c_13589,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_165])).

cnf(c_37829,plain,
    ( v3_pre_topc(u1_struct_0(sK52),sK52) = iProver_top
    | l1_pre_topc(sK52) != iProver_top
    | v2_pre_topc(sK52) != iProver_top ),
    inference(superposition,[status(thm)],[c_32771,c_13589])).

cnf(c_28520,plain,
    ( m1_pre_topc(sK52,sK52) = iProver_top ),
    inference(superposition,[status(thm)],[c_28516,c_27437])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_47280,c_37829,c_28520,c_27043,c_16932,c_239,c_232,c_231])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n016.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:16:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.31/2.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.31/2.48  
% 15.31/2.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.31/2.48  
% 15.31/2.48  ------  iProver source info
% 15.31/2.48  
% 15.31/2.48  git: date: 2020-06-30 10:37:57 +0100
% 15.31/2.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.31/2.48  git: non_committed_changes: false
% 15.31/2.48  git: last_make_outside_of_git: false
% 15.31/2.48  
% 15.31/2.48  ------ 
% 15.31/2.48  
% 15.31/2.48  ------ Input Options
% 15.31/2.48  
% 15.31/2.48  --out_options                           all
% 15.31/2.48  --tptp_safe_out                         true
% 15.31/2.48  --problem_path                          ""
% 15.31/2.48  --include_path                          ""
% 15.31/2.48  --clausifier                            res/vclausify_rel
% 15.31/2.48  --clausifier_options                    ""
% 15.31/2.48  --stdin                                 false
% 15.31/2.48  --stats_out                             all
% 15.31/2.48  
% 15.31/2.48  ------ General Options
% 15.31/2.48  
% 15.31/2.48  --fof                                   false
% 15.31/2.48  --time_out_real                         305.
% 15.31/2.48  --time_out_virtual                      -1.
% 15.31/2.48  --symbol_type_check                     false
% 15.31/2.48  --clausify_out                          false
% 15.31/2.48  --sig_cnt_out                           false
% 15.31/2.48  --trig_cnt_out                          false
% 15.31/2.48  --trig_cnt_out_tolerance                1.
% 15.31/2.48  --trig_cnt_out_sk_spl                   false
% 15.31/2.48  --abstr_cl_out                          false
% 15.31/2.48  
% 15.31/2.48  ------ Global Options
% 15.31/2.48  
% 15.31/2.48  --schedule                              default
% 15.31/2.48  --add_important_lit                     false
% 15.31/2.48  --prop_solver_per_cl                    1000
% 15.31/2.48  --min_unsat_core                        false
% 15.31/2.48  --soft_assumptions                      false
% 15.31/2.48  --soft_lemma_size                       3
% 15.31/2.48  --prop_impl_unit_size                   0
% 15.31/2.48  --prop_impl_unit                        []
% 15.31/2.48  --share_sel_clauses                     true
% 15.31/2.48  --reset_solvers                         false
% 15.31/2.48  --bc_imp_inh                            [conj_cone]
% 15.31/2.48  --conj_cone_tolerance                   3.
% 15.31/2.48  --extra_neg_conj                        none
% 15.31/2.48  --large_theory_mode                     true
% 15.31/2.48  --prolific_symb_bound                   200
% 15.31/2.48  --lt_threshold                          2000
% 15.31/2.48  --clause_weak_htbl                      true
% 15.31/2.48  --gc_record_bc_elim                     false
% 15.31/2.48  
% 15.31/2.48  ------ Preprocessing Options
% 15.31/2.48  
% 15.31/2.48  --preprocessing_flag                    true
% 15.31/2.48  --time_out_prep_mult                    0.1
% 15.31/2.48  --splitting_mode                        input
% 15.31/2.48  --splitting_grd                         true
% 15.31/2.48  --splitting_cvd                         false
% 15.31/2.48  --splitting_cvd_svl                     false
% 15.31/2.48  --splitting_nvd                         32
% 15.31/2.48  --sub_typing                            true
% 15.31/2.48  --prep_gs_sim                           true
% 15.31/2.48  --prep_unflatten                        true
% 15.31/2.48  --prep_res_sim                          true
% 15.31/2.48  --prep_upred                            true
% 15.31/2.48  --prep_sem_filter                       exhaustive
% 15.31/2.48  --prep_sem_filter_out                   false
% 15.31/2.48  --pred_elim                             true
% 15.31/2.48  --res_sim_input                         true
% 15.31/2.48  --eq_ax_congr_red                       true
% 15.31/2.48  --pure_diseq_elim                       true
% 15.31/2.48  --brand_transform                       false
% 15.31/2.48  --non_eq_to_eq                          false
% 15.31/2.48  --prep_def_merge                        true
% 15.31/2.48  --prep_def_merge_prop_impl              false
% 15.31/2.48  --prep_def_merge_mbd                    true
% 15.31/2.48  --prep_def_merge_tr_red                 false
% 15.31/2.48  --prep_def_merge_tr_cl                  false
% 15.31/2.48  --smt_preprocessing                     true
% 15.31/2.48  --smt_ac_axioms                         fast
% 15.31/2.48  --preprocessed_out                      false
% 15.31/2.48  --preprocessed_stats                    false
% 15.31/2.48  
% 15.31/2.48  ------ Abstraction refinement Options
% 15.31/2.48  
% 15.31/2.48  --abstr_ref                             []
% 15.31/2.48  --abstr_ref_prep                        false
% 15.31/2.48  --abstr_ref_until_sat                   false
% 15.31/2.48  --abstr_ref_sig_restrict                funpre
% 15.31/2.48  --abstr_ref_af_restrict_to_split_sk     false
% 15.31/2.48  --abstr_ref_under                       []
% 15.31/2.48  
% 15.31/2.48  ------ SAT Options
% 15.31/2.48  
% 15.31/2.48  --sat_mode                              false
% 15.31/2.48  --sat_fm_restart_options                ""
% 15.31/2.48  --sat_gr_def                            false
% 15.31/2.48  --sat_epr_types                         true
% 15.31/2.48  --sat_non_cyclic_types                  false
% 15.31/2.48  --sat_finite_models                     false
% 15.31/2.48  --sat_fm_lemmas                         false
% 15.31/2.48  --sat_fm_prep                           false
% 15.31/2.48  --sat_fm_uc_incr                        true
% 15.31/2.48  --sat_out_model                         small
% 15.31/2.48  --sat_out_clauses                       false
% 15.31/2.48  
% 15.31/2.48  ------ QBF Options
% 15.31/2.48  
% 15.31/2.48  --qbf_mode                              false
% 15.31/2.48  --qbf_elim_univ                         false
% 15.31/2.48  --qbf_dom_inst                          none
% 15.31/2.48  --qbf_dom_pre_inst                      false
% 15.31/2.48  --qbf_sk_in                             false
% 15.31/2.48  --qbf_pred_elim                         true
% 15.31/2.48  --qbf_split                             512
% 15.31/2.48  
% 15.31/2.48  ------ BMC1 Options
% 15.31/2.48  
% 15.31/2.48  --bmc1_incremental                      false
% 15.31/2.48  --bmc1_axioms                           reachable_all
% 15.31/2.48  --bmc1_min_bound                        0
% 15.31/2.48  --bmc1_max_bound                        -1
% 15.31/2.48  --bmc1_max_bound_default                -1
% 15.31/2.48  --bmc1_symbol_reachability              true
% 15.31/2.48  --bmc1_property_lemmas                  false
% 15.31/2.48  --bmc1_k_induction                      false
% 15.31/2.48  --bmc1_non_equiv_states                 false
% 15.31/2.48  --bmc1_deadlock                         false
% 15.31/2.48  --bmc1_ucm                              false
% 15.31/2.48  --bmc1_add_unsat_core                   none
% 15.31/2.48  --bmc1_unsat_core_children              false
% 15.31/2.48  --bmc1_unsat_core_extrapolate_axioms    false
% 15.31/2.48  --bmc1_out_stat                         full
% 15.31/2.48  --bmc1_ground_init                      false
% 15.31/2.48  --bmc1_pre_inst_next_state              false
% 15.31/2.48  --bmc1_pre_inst_state                   false
% 15.31/2.48  --bmc1_pre_inst_reach_state             false
% 15.31/2.48  --bmc1_out_unsat_core                   false
% 15.31/2.48  --bmc1_aig_witness_out                  false
% 15.31/2.48  --bmc1_verbose                          false
% 15.31/2.48  --bmc1_dump_clauses_tptp                false
% 15.31/2.48  --bmc1_dump_unsat_core_tptp             false
% 15.31/2.48  --bmc1_dump_file                        -
% 15.31/2.48  --bmc1_ucm_expand_uc_limit              128
% 15.31/2.48  --bmc1_ucm_n_expand_iterations          6
% 15.31/2.48  --bmc1_ucm_extend_mode                  1
% 15.31/2.48  --bmc1_ucm_init_mode                    2
% 15.31/2.48  --bmc1_ucm_cone_mode                    none
% 15.31/2.48  --bmc1_ucm_reduced_relation_type        0
% 15.31/2.48  --bmc1_ucm_relax_model                  4
% 15.31/2.48  --bmc1_ucm_full_tr_after_sat            true
% 15.31/2.48  --bmc1_ucm_expand_neg_assumptions       false
% 15.31/2.48  --bmc1_ucm_layered_model                none
% 15.31/2.48  --bmc1_ucm_max_lemma_size               10
% 15.31/2.48  
% 15.31/2.48  ------ AIG Options
% 15.31/2.48  
% 15.31/2.48  --aig_mode                              false
% 15.31/2.48  
% 15.31/2.48  ------ Instantiation Options
% 15.31/2.48  
% 15.31/2.48  --instantiation_flag                    true
% 15.31/2.48  --inst_sos_flag                         true
% 15.31/2.48  --inst_sos_phase                        true
% 15.31/2.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.31/2.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.31/2.48  --inst_lit_sel_side                     num_symb
% 15.31/2.48  --inst_solver_per_active                1400
% 15.31/2.48  --inst_solver_calls_frac                1.
% 15.31/2.48  --inst_passive_queue_type               priority_queues
% 15.31/2.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.31/2.48  --inst_passive_queues_freq              [25;2]
% 15.31/2.48  --inst_dismatching                      true
% 15.31/2.48  --inst_eager_unprocessed_to_passive     true
% 15.31/2.48  --inst_prop_sim_given                   true
% 15.31/2.48  --inst_prop_sim_new                     false
% 15.31/2.48  --inst_subs_new                         false
% 15.31/2.48  --inst_eq_res_simp                      false
% 15.31/2.48  --inst_subs_given                       false
% 15.31/2.48  --inst_orphan_elimination               true
% 15.31/2.48  --inst_learning_loop_flag               true
% 15.31/2.48  --inst_learning_start                   3000
% 15.31/2.48  --inst_learning_factor                  2
% 15.31/2.48  --inst_start_prop_sim_after_learn       3
% 15.31/2.48  --inst_sel_renew                        solver
% 15.31/2.48  --inst_lit_activity_flag                true
% 15.31/2.48  --inst_restr_to_given                   false
% 15.31/2.48  --inst_activity_threshold               500
% 15.31/2.48  --inst_out_proof                        true
% 15.31/2.48  
% 15.31/2.48  ------ Resolution Options
% 15.31/2.48  
% 15.31/2.48  --resolution_flag                       true
% 15.31/2.48  --res_lit_sel                           adaptive
% 15.31/2.48  --res_lit_sel_side                      none
% 15.31/2.48  --res_ordering                          kbo
% 15.31/2.48  --res_to_prop_solver                    active
% 15.31/2.48  --res_prop_simpl_new                    false
% 15.31/2.48  --res_prop_simpl_given                  true
% 15.31/2.48  --res_passive_queue_type                priority_queues
% 15.31/2.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.31/2.48  --res_passive_queues_freq               [15;5]
% 15.31/2.48  --res_forward_subs                      full
% 15.31/2.48  --res_backward_subs                     full
% 15.31/2.48  --res_forward_subs_resolution           true
% 15.31/2.48  --res_backward_subs_resolution          true
% 15.31/2.48  --res_orphan_elimination                true
% 15.31/2.48  --res_time_limit                        2.
% 15.31/2.48  --res_out_proof                         true
% 15.31/2.48  
% 15.31/2.48  ------ Superposition Options
% 15.31/2.48  
% 15.31/2.48  --superposition_flag                    true
% 15.31/2.48  --sup_passive_queue_type                priority_queues
% 15.31/2.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.31/2.48  --sup_passive_queues_freq               [8;1;4]
% 15.31/2.48  --demod_completeness_check              fast
% 15.31/2.48  --demod_use_ground                      true
% 15.31/2.48  --sup_to_prop_solver                    passive
% 15.31/2.48  --sup_prop_simpl_new                    true
% 15.31/2.48  --sup_prop_simpl_given                  true
% 15.31/2.48  --sup_fun_splitting                     true
% 15.31/2.48  --sup_smt_interval                      50000
% 15.31/2.48  
% 15.31/2.48  ------ Superposition Simplification Setup
% 15.31/2.48  
% 15.31/2.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.31/2.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.31/2.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.31/2.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.31/2.48  --sup_full_triv                         [TrivRules;PropSubs]
% 15.31/2.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.31/2.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.31/2.48  --sup_immed_triv                        [TrivRules]
% 15.31/2.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.31/2.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.31/2.48  --sup_immed_bw_main                     []
% 15.31/2.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.31/2.48  --sup_input_triv                        [Unflattening;TrivRules]
% 15.31/2.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.31/2.48  --sup_input_bw                          []
% 15.31/2.48  
% 15.31/2.48  ------ Combination Options
% 15.31/2.48  
% 15.31/2.48  --comb_res_mult                         3
% 15.31/2.48  --comb_sup_mult                         2
% 15.31/2.48  --comb_inst_mult                        10
% 15.31/2.48  
% 15.31/2.48  ------ Debug Options
% 15.31/2.48  
% 15.31/2.48  --dbg_backtrace                         false
% 15.31/2.48  --dbg_dump_prop_clauses                 false
% 15.31/2.48  --dbg_dump_prop_clauses_file            -
% 15.31/2.48  --dbg_out_stat                          false
% 15.31/2.48  ------ Parsing...
% 15.31/2.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.31/2.48  
% 15.31/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 15.31/2.48  
% 15.31/2.48  ------ Preprocessing... gs_s  sp: 8 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.31/2.48  
% 15.31/2.48  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.31/2.48  ------ Proving...
% 15.31/2.48  ------ Problem Properties 
% 15.31/2.48  
% 15.31/2.48  
% 15.31/2.48  clauses                                 226
% 15.31/2.48  conjectures                             19
% 15.31/2.48  EPR                                     64
% 15.31/2.48  Horn                                    182
% 15.31/2.48  unary                                   77
% 15.31/2.48  binary                                  38
% 15.31/2.48  lits                                    723
% 15.31/2.48  lits eq                                 67
% 15.31/2.48  fd_pure                                 0
% 15.31/2.48  fd_pseudo                               0
% 15.31/2.48  fd_cond                                 5
% 15.31/2.48  fd_pseudo_cond                          6
% 15.31/2.48  AC symbols                              0
% 15.31/2.48  
% 15.31/2.48  ------ Schedule dynamic 5 is on 
% 15.31/2.48  
% 15.31/2.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.31/2.48  
% 15.31/2.48  
% 15.31/2.48  ------ 
% 15.31/2.48  Current options:
% 15.31/2.48  ------ 
% 15.31/2.48  
% 15.31/2.48  ------ Input Options
% 15.31/2.48  
% 15.31/2.48  --out_options                           all
% 15.31/2.48  --tptp_safe_out                         true
% 15.31/2.48  --problem_path                          ""
% 15.31/2.48  --include_path                          ""
% 15.31/2.48  --clausifier                            res/vclausify_rel
% 15.31/2.48  --clausifier_options                    ""
% 15.31/2.48  --stdin                                 false
% 15.31/2.48  --stats_out                             all
% 15.31/2.48  
% 15.31/2.48  ------ General Options
% 15.31/2.48  
% 15.31/2.48  --fof                                   false
% 15.31/2.48  --time_out_real                         305.
% 15.31/2.48  --time_out_virtual                      -1.
% 15.31/2.48  --symbol_type_check                     false
% 15.31/2.48  --clausify_out                          false
% 15.31/2.48  --sig_cnt_out                           false
% 15.31/2.48  --trig_cnt_out                          false
% 15.31/2.48  --trig_cnt_out_tolerance                1.
% 15.31/2.48  --trig_cnt_out_sk_spl                   false
% 15.31/2.48  --abstr_cl_out                          false
% 15.31/2.48  
% 15.31/2.48  ------ Global Options
% 15.31/2.48  
% 15.31/2.48  --schedule                              default
% 15.31/2.48  --add_important_lit                     false
% 15.31/2.48  --prop_solver_per_cl                    1000
% 15.31/2.48  --min_unsat_core                        false
% 15.31/2.48  --soft_assumptions                      false
% 15.31/2.48  --soft_lemma_size                       3
% 15.31/2.48  --prop_impl_unit_size                   0
% 15.31/2.48  --prop_impl_unit                        []
% 15.31/2.48  --share_sel_clauses                     true
% 15.31/2.48  --reset_solvers                         false
% 15.31/2.48  --bc_imp_inh                            [conj_cone]
% 15.31/2.48  --conj_cone_tolerance                   3.
% 15.31/2.48  --extra_neg_conj                        none
% 15.31/2.48  --large_theory_mode                     true
% 15.31/2.48  --prolific_symb_bound                   200
% 15.31/2.48  --lt_threshold                          2000
% 15.31/2.48  --clause_weak_htbl                      true
% 15.31/2.48  --gc_record_bc_elim                     false
% 15.31/2.48  
% 15.31/2.48  ------ Preprocessing Options
% 15.31/2.48  
% 15.31/2.48  --preprocessing_flag                    true
% 15.31/2.48  --time_out_prep_mult                    0.1
% 15.31/2.48  --splitting_mode                        input
% 15.31/2.48  --splitting_grd                         true
% 15.31/2.48  --splitting_cvd                         false
% 15.31/2.48  --splitting_cvd_svl                     false
% 15.31/2.48  --splitting_nvd                         32
% 15.31/2.48  --sub_typing                            true
% 15.31/2.48  --prep_gs_sim                           true
% 15.31/2.48  --prep_unflatten                        true
% 15.31/2.48  --prep_res_sim                          true
% 15.31/2.48  --prep_upred                            true
% 15.31/2.48  --prep_sem_filter                       exhaustive
% 15.31/2.48  --prep_sem_filter_out                   false
% 15.31/2.48  --pred_elim                             true
% 15.31/2.48  --res_sim_input                         true
% 15.31/2.48  --eq_ax_congr_red                       true
% 15.31/2.48  --pure_diseq_elim                       true
% 15.31/2.49  --brand_transform                       false
% 15.31/2.49  --non_eq_to_eq                          false
% 15.31/2.49  --prep_def_merge                        true
% 15.31/2.49  --prep_def_merge_prop_impl              false
% 15.31/2.49  --prep_def_merge_mbd                    true
% 15.31/2.49  --prep_def_merge_tr_red                 false
% 15.31/2.49  --prep_def_merge_tr_cl                  false
% 15.31/2.49  --smt_preprocessing                     true
% 15.31/2.49  --smt_ac_axioms                         fast
% 15.31/2.49  --preprocessed_out                      false
% 15.31/2.49  --preprocessed_stats                    false
% 15.31/2.49  
% 15.31/2.49  ------ Abstraction refinement Options
% 15.31/2.49  
% 15.31/2.49  --abstr_ref                             []
% 15.31/2.49  --abstr_ref_prep                        false
% 15.31/2.49  --abstr_ref_until_sat                   false
% 15.31/2.49  --abstr_ref_sig_restrict                funpre
% 15.31/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 15.31/2.49  --abstr_ref_under                       []
% 15.31/2.49  
% 15.31/2.49  ------ SAT Options
% 15.31/2.49  
% 15.31/2.49  --sat_mode                              false
% 15.31/2.49  --sat_fm_restart_options                ""
% 15.31/2.49  --sat_gr_def                            false
% 15.31/2.49  --sat_epr_types                         true
% 15.31/2.49  --sat_non_cyclic_types                  false
% 15.31/2.49  --sat_finite_models                     false
% 15.31/2.49  --sat_fm_lemmas                         false
% 15.31/2.49  --sat_fm_prep                           false
% 15.31/2.49  --sat_fm_uc_incr                        true
% 15.31/2.49  --sat_out_model                         small
% 15.31/2.49  --sat_out_clauses                       false
% 15.31/2.49  
% 15.31/2.49  ------ QBF Options
% 15.31/2.49  
% 15.31/2.49  --qbf_mode                              false
% 15.31/2.49  --qbf_elim_univ                         false
% 15.31/2.49  --qbf_dom_inst                          none
% 15.31/2.49  --qbf_dom_pre_inst                      false
% 15.31/2.49  --qbf_sk_in                             false
% 15.31/2.49  --qbf_pred_elim                         true
% 15.31/2.49  --qbf_split                             512
% 15.31/2.49  
% 15.31/2.49  ------ BMC1 Options
% 15.31/2.49  
% 15.31/2.49  --bmc1_incremental                      false
% 15.31/2.49  --bmc1_axioms                           reachable_all
% 15.31/2.49  --bmc1_min_bound                        0
% 15.31/2.49  --bmc1_max_bound                        -1
% 15.31/2.49  --bmc1_max_bound_default                -1
% 15.31/2.49  --bmc1_symbol_reachability              true
% 15.31/2.49  --bmc1_property_lemmas                  false
% 15.31/2.49  --bmc1_k_induction                      false
% 15.31/2.49  --bmc1_non_equiv_states                 false
% 15.31/2.49  --bmc1_deadlock                         false
% 15.31/2.49  --bmc1_ucm                              false
% 15.31/2.49  --bmc1_add_unsat_core                   none
% 15.31/2.49  --bmc1_unsat_core_children              false
% 15.31/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 15.31/2.49  --bmc1_out_stat                         full
% 15.31/2.49  --bmc1_ground_init                      false
% 15.31/2.49  --bmc1_pre_inst_next_state              false
% 15.31/2.49  --bmc1_pre_inst_state                   false
% 15.31/2.49  --bmc1_pre_inst_reach_state             false
% 15.31/2.49  --bmc1_out_unsat_core                   false
% 15.31/2.49  --bmc1_aig_witness_out                  false
% 15.31/2.49  --bmc1_verbose                          false
% 15.31/2.49  --bmc1_dump_clauses_tptp                false
% 15.31/2.49  --bmc1_dump_unsat_core_tptp             false
% 15.31/2.49  --bmc1_dump_file                        -
% 15.31/2.49  --bmc1_ucm_expand_uc_limit              128
% 15.31/2.49  --bmc1_ucm_n_expand_iterations          6
% 15.31/2.49  --bmc1_ucm_extend_mode                  1
% 15.31/2.49  --bmc1_ucm_init_mode                    2
% 15.31/2.49  --bmc1_ucm_cone_mode                    none
% 15.31/2.49  --bmc1_ucm_reduced_relation_type        0
% 15.31/2.49  --bmc1_ucm_relax_model                  4
% 15.31/2.49  --bmc1_ucm_full_tr_after_sat            true
% 15.31/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 15.31/2.49  --bmc1_ucm_layered_model                none
% 15.31/2.49  --bmc1_ucm_max_lemma_size               10
% 15.31/2.49  
% 15.31/2.49  ------ AIG Options
% 15.31/2.49  
% 15.31/2.49  --aig_mode                              false
% 15.31/2.49  
% 15.31/2.49  ------ Instantiation Options
% 15.31/2.49  
% 15.31/2.49  --instantiation_flag                    true
% 15.31/2.49  --inst_sos_flag                         true
% 15.31/2.49  --inst_sos_phase                        true
% 15.31/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.31/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.31/2.49  --inst_lit_sel_side                     none
% 15.31/2.49  --inst_solver_per_active                1400
% 15.31/2.49  --inst_solver_calls_frac                1.
% 15.31/2.49  --inst_passive_queue_type               priority_queues
% 15.31/2.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.31/2.49  --inst_passive_queues_freq              [25;2]
% 15.31/2.49  --inst_dismatching                      true
% 15.31/2.49  --inst_eager_unprocessed_to_passive     true
% 15.31/2.49  --inst_prop_sim_given                   true
% 15.31/2.49  --inst_prop_sim_new                     false
% 15.31/2.49  --inst_subs_new                         false
% 15.31/2.49  --inst_eq_res_simp                      false
% 15.31/2.49  --inst_subs_given                       false
% 15.31/2.49  --inst_orphan_elimination               true
% 15.31/2.49  --inst_learning_loop_flag               true
% 15.31/2.49  --inst_learning_start                   3000
% 15.31/2.49  --inst_learning_factor                  2
% 15.31/2.49  --inst_start_prop_sim_after_learn       3
% 15.31/2.49  --inst_sel_renew                        solver
% 15.31/2.49  --inst_lit_activity_flag                true
% 15.31/2.49  --inst_restr_to_given                   false
% 15.31/2.49  --inst_activity_threshold               500
% 15.31/2.49  --inst_out_proof                        true
% 15.31/2.49  
% 15.31/2.49  ------ Resolution Options
% 15.31/2.49  
% 15.31/2.49  --resolution_flag                       false
% 15.31/2.49  --res_lit_sel                           adaptive
% 15.31/2.49  --res_lit_sel_side                      none
% 15.31/2.49  --res_ordering                          kbo
% 15.31/2.49  --res_to_prop_solver                    active
% 15.31/2.49  --res_prop_simpl_new                    false
% 15.31/2.49  --res_prop_simpl_given                  true
% 15.31/2.49  --res_passive_queue_type                priority_queues
% 15.31/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.31/2.49  --res_passive_queues_freq               [15;5]
% 15.31/2.49  --res_forward_subs                      full
% 15.31/2.49  --res_backward_subs                     full
% 15.31/2.49  --res_forward_subs_resolution           true
% 15.31/2.49  --res_backward_subs_resolution          true
% 15.31/2.49  --res_orphan_elimination                true
% 15.31/2.49  --res_time_limit                        2.
% 15.31/2.49  --res_out_proof                         true
% 15.31/2.49  
% 15.31/2.49  ------ Superposition Options
% 15.31/2.49  
% 15.31/2.49  --superposition_flag                    true
% 15.31/2.49  --sup_passive_queue_type                priority_queues
% 15.31/2.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.31/2.49  --sup_passive_queues_freq               [8;1;4]
% 15.31/2.49  --demod_completeness_check              fast
% 15.31/2.49  --demod_use_ground                      true
% 15.31/2.49  --sup_to_prop_solver                    passive
% 15.31/2.49  --sup_prop_simpl_new                    true
% 15.31/2.49  --sup_prop_simpl_given                  true
% 15.31/2.49  --sup_fun_splitting                     true
% 15.31/2.49  --sup_smt_interval                      50000
% 15.31/2.49  
% 15.31/2.49  ------ Superposition Simplification Setup
% 15.31/2.49  
% 15.31/2.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.31/2.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.31/2.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.31/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.31/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 15.31/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.31/2.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.31/2.49  --sup_immed_triv                        [TrivRules]
% 15.31/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.31/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.31/2.49  --sup_immed_bw_main                     []
% 15.31/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.31/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 15.31/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.31/2.49  --sup_input_bw                          []
% 15.31/2.49  
% 15.31/2.49  ------ Combination Options
% 15.31/2.49  
% 15.31/2.49  --comb_res_mult                         3
% 15.31/2.49  --comb_sup_mult                         2
% 15.31/2.49  --comb_inst_mult                        10
% 15.31/2.49  
% 15.31/2.49  ------ Debug Options
% 15.31/2.49  
% 15.31/2.49  --dbg_backtrace                         false
% 15.31/2.49  --dbg_dump_prop_clauses                 false
% 15.31/2.49  --dbg_dump_prop_clauses_file            -
% 15.31/2.49  --dbg_out_stat                          false
% 15.31/2.49  
% 15.31/2.49  
% 15.31/2.49  
% 15.31/2.49  
% 15.31/2.49  ------ Proving...
% 15.31/2.49  
% 15.31/2.49  
% 15.31/2.49  % SZS status Theorem for theBenchmark.p
% 15.31/2.49  
% 15.31/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.31/2.49  
% 15.31/2.49  fof(f113,conjecture,(
% 15.31/2.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 15.31/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.49  
% 15.31/2.49  fof(f114,negated_conjecture,(
% 15.31/2.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 15.31/2.49    inference(negated_conjecture,[],[f113])).
% 15.31/2.49  
% 15.31/2.49  fof(f249,plain,(
% 15.31/2.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 15.31/2.49    inference(ennf_transformation,[],[f114])).
% 15.31/2.49  
% 15.31/2.49  fof(f250,plain,(
% 15.31/2.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 15.31/2.49    inference(flattening,[],[f249])).
% 15.31/2.49  
% 15.31/2.49  fof(f380,plain,(
% 15.31/2.49    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK55) & sK55 = X5 & m1_subset_1(sK55,u1_struct_0(X2)))) )),
% 15.31/2.49    introduced(choice_axiom,[])).
% 15.31/2.49  
% 15.31/2.49  fof(f379,plain,(
% 15.31/2.49    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X3,X1,X4,sK54) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & sK54 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK54,u1_struct_0(X3)))) )),
% 15.31/2.49    introduced(choice_axiom,[])).
% 15.31/2.49  
% 15.31/2.49  fof(f378,plain,(
% 15.31/2.49    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,sK53,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK53),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(sK53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK53,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK53))) )),
% 15.31/2.49    introduced(choice_axiom,[])).
% 15.31/2.49  
% 15.31/2.49  fof(f377,plain,(
% 15.31/2.49    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK52,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK52,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK52))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK52 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK52),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK52),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK52,X0) & ~v2_struct_0(sK52))) )),
% 15.31/2.49    introduced(choice_axiom,[])).
% 15.31/2.49  
% 15.31/2.49  fof(f376,plain,(
% 15.31/2.49    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(sK51,X1,k3_tmap_1(X0,X1,X3,sK51,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK51))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK51),u1_pre_topc(sK51)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK51,X0) & ~v2_struct_0(sK51))) )),
% 15.31/2.49    introduced(choice_axiom,[])).
% 15.31/2.49  
% 15.31/2.49  fof(f375,plain,(
% 15.31/2.49    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK50,X4,X5) & r1_tmap_1(X2,sK50,k3_tmap_1(X0,sK50,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK50)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK50)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK50) & v2_pre_topc(sK50) & ~v2_struct_0(sK50))) )),
% 15.31/2.49    introduced(choice_axiom,[])).
% 15.31/2.49  
% 15.31/2.49  fof(f374,plain,(
% 15.31/2.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK49,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK49) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK49) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK49) & v2_pre_topc(sK49) & ~v2_struct_0(sK49))),
% 15.31/2.49    introduced(choice_axiom,[])).
% 15.31/2.49  
% 15.31/2.49  fof(f381,plain,(
% 15.31/2.49    ((((((~r1_tmap_1(sK52,sK50,sK53,sK54) & r1_tmap_1(sK51,sK50,k3_tmap_1(sK49,sK50,sK52,sK51,sK53),sK55) & sK54 = sK55 & m1_subset_1(sK55,u1_struct_0(sK51))) & m1_subset_1(sK54,u1_struct_0(sK52))) & g1_pre_topc(u1_struct_0(sK51),u1_pre_topc(sK51)) = sK52 & m1_subset_1(sK53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK52),u1_struct_0(sK50)))) & v1_funct_2(sK53,u1_struct_0(sK52),u1_struct_0(sK50)) & v1_funct_1(sK53)) & m1_pre_topc(sK52,sK49) & ~v2_struct_0(sK52)) & m1_pre_topc(sK51,sK49) & ~v2_struct_0(sK51)) & l1_pre_topc(sK50) & v2_pre_topc(sK50) & ~v2_struct_0(sK50)) & l1_pre_topc(sK49) & v2_pre_topc(sK49) & ~v2_struct_0(sK49)),
% 15.31/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK49,sK50,sK51,sK52,sK53,sK54,sK55])],[f250,f380,f379,f378,f377,f376,f375,f374])).
% 15.31/2.49  
% 15.31/2.49  fof(f607,plain,(
% 15.31/2.49    m1_subset_1(sK54,u1_struct_0(sK52))),
% 15.31/2.49    inference(cnf_transformation,[],[f381])).
% 15.31/2.49  
% 15.31/2.49  fof(f23,axiom,(
% 15.31/2.49    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 15.31/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.49  
% 15.31/2.49  fof(f147,plain,(
% 15.31/2.49    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 15.31/2.49    inference(ennf_transformation,[],[f23])).
% 15.31/2.49  
% 15.31/2.49  fof(f148,plain,(
% 15.31/2.49    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 15.31/2.49    inference(flattening,[],[f147])).
% 15.31/2.49  
% 15.31/2.49  fof(f417,plain,(
% 15.31/2.49    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 15.31/2.49    inference(cnf_transformation,[],[f148])).
% 15.31/2.49  
% 15.31/2.49  fof(f595,plain,(
% 15.31/2.49    l1_pre_topc(sK49)),
% 15.31/2.49    inference(cnf_transformation,[],[f381])).
% 15.31/2.49  
% 15.31/2.49  fof(f601,plain,(
% 15.31/2.49    ~v2_struct_0(sK52)),
% 15.31/2.49    inference(cnf_transformation,[],[f381])).
% 15.31/2.49  
% 15.31/2.49  fof(f602,plain,(
% 15.31/2.49    m1_pre_topc(sK52,sK49)),
% 15.31/2.49    inference(cnf_transformation,[],[f381])).
% 15.31/2.49  
% 15.31/2.49  fof(f62,axiom,(
% 15.31/2.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 15.31/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.49  
% 15.31/2.49  fof(f185,plain,(
% 15.31/2.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 15.31/2.49    inference(ennf_transformation,[],[f62])).
% 15.31/2.49  
% 15.31/2.49  fof(f506,plain,(
% 15.31/2.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 15.31/2.49    inference(cnf_transformation,[],[f185])).
% 15.31/2.49  
% 15.31/2.49  fof(f69,axiom,(
% 15.31/2.49    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 15.31/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.49  
% 15.31/2.49  fof(f191,plain,(
% 15.31/2.49    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 15.31/2.49    inference(ennf_transformation,[],[f69])).
% 15.31/2.49  
% 15.31/2.49  fof(f192,plain,(
% 15.31/2.49    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 15.31/2.49    inference(flattening,[],[f191])).
% 15.31/2.49  
% 15.31/2.49  fof(f513,plain,(
% 15.31/2.49    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 15.31/2.49    inference(cnf_transformation,[],[f192])).
% 15.31/2.49  
% 15.31/2.49  fof(f63,axiom,(
% 15.31/2.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 15.31/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.49  
% 15.31/2.49  fof(f186,plain,(
% 15.31/2.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 15.31/2.49    inference(ennf_transformation,[],[f63])).
% 15.31/2.49  
% 15.31/2.49  fof(f507,plain,(
% 15.31/2.49    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 15.31/2.49    inference(cnf_transformation,[],[f186])).
% 15.31/2.49  
% 15.31/2.49  fof(f60,axiom,(
% 15.31/2.49    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 15.31/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.49  
% 15.31/2.49  fof(f183,plain,(
% 15.31/2.49    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 15.31/2.49    inference(ennf_transformation,[],[f60])).
% 15.31/2.49  
% 15.31/2.49  fof(f504,plain,(
% 15.31/2.49    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 15.31/2.49    inference(cnf_transformation,[],[f183])).
% 15.31/2.49  
% 15.31/2.49  fof(f103,axiom,(
% 15.31/2.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 15.31/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.49  
% 15.31/2.49  fof(f234,plain,(
% 15.31/2.49    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 15.31/2.49    inference(ennf_transformation,[],[f103])).
% 15.31/2.49  
% 15.31/2.49  fof(f572,plain,(
% 15.31/2.49    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 15.31/2.49    inference(cnf_transformation,[],[f234])).
% 15.31/2.49  
% 15.31/2.49  fof(f610,plain,(
% 15.31/2.49    r1_tmap_1(sK51,sK50,k3_tmap_1(sK49,sK50,sK52,sK51,sK53),sK55)),
% 15.31/2.49    inference(cnf_transformation,[],[f381])).
% 15.31/2.49  
% 15.31/2.49  fof(f609,plain,(
% 15.31/2.49    sK54 = sK55),
% 15.31/2.49    inference(cnf_transformation,[],[f381])).
% 15.31/2.49  
% 15.31/2.49  fof(f111,axiom,(
% 15.31/2.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 15.31/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.49  
% 15.31/2.49  fof(f245,plain,(
% 15.31/2.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 15.31/2.49    inference(ennf_transformation,[],[f111])).
% 15.31/2.49  
% 15.31/2.49  fof(f246,plain,(
% 15.31/2.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 15.31/2.49    inference(flattening,[],[f245])).
% 15.31/2.49  
% 15.31/2.49  fof(f372,plain,(
% 15.31/2.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 15.31/2.49    inference(nnf_transformation,[],[f246])).
% 15.31/2.49  
% 15.31/2.49  fof(f590,plain,(
% 15.31/2.49    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.31/2.49    inference(cnf_transformation,[],[f372])).
% 15.31/2.49  
% 15.31/2.49  fof(f631,plain,(
% 15.31/2.49    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.31/2.49    inference(equality_resolution,[],[f590])).
% 15.31/2.49  
% 15.31/2.49  fof(f593,plain,(
% 15.31/2.49    ~v2_struct_0(sK49)),
% 15.31/2.49    inference(cnf_transformation,[],[f381])).
% 15.31/2.49  
% 15.31/2.49  fof(f594,plain,(
% 15.31/2.49    v2_pre_topc(sK49)),
% 15.31/2.49    inference(cnf_transformation,[],[f381])).
% 15.31/2.49  
% 15.31/2.49  fof(f596,plain,(
% 15.31/2.49    ~v2_struct_0(sK50)),
% 15.31/2.49    inference(cnf_transformation,[],[f381])).
% 15.31/2.49  
% 15.31/2.49  fof(f597,plain,(
% 15.31/2.49    v2_pre_topc(sK50)),
% 15.31/2.49    inference(cnf_transformation,[],[f381])).
% 15.31/2.49  
% 15.31/2.49  fof(f598,plain,(
% 15.31/2.49    l1_pre_topc(sK50)),
% 15.31/2.49    inference(cnf_transformation,[],[f381])).
% 15.31/2.49  
% 15.31/2.49  fof(f599,plain,(
% 15.31/2.49    ~v2_struct_0(sK51)),
% 15.31/2.49    inference(cnf_transformation,[],[f381])).
% 15.31/2.49  
% 15.31/2.49  fof(f600,plain,(
% 15.31/2.49    m1_pre_topc(sK51,sK49)),
% 15.31/2.49    inference(cnf_transformation,[],[f381])).
% 15.31/2.49  
% 15.31/2.49  fof(f603,plain,(
% 15.31/2.49    v1_funct_1(sK53)),
% 15.31/2.49    inference(cnf_transformation,[],[f381])).
% 15.31/2.49  
% 15.31/2.49  fof(f604,plain,(
% 15.31/2.49    v1_funct_2(sK53,u1_struct_0(sK52),u1_struct_0(sK50))),
% 15.31/2.49    inference(cnf_transformation,[],[f381])).
% 15.31/2.49  
% 15.31/2.49  fof(f605,plain,(
% 15.31/2.49    m1_subset_1(sK53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK52),u1_struct_0(sK50))))),
% 15.31/2.49    inference(cnf_transformation,[],[f381])).
% 15.31/2.49  
% 15.31/2.49  fof(f611,plain,(
% 15.31/2.49    ~r1_tmap_1(sK52,sK50,sK53,sK54)),
% 15.31/2.49    inference(cnf_transformation,[],[f381])).
% 15.31/2.49  
% 15.31/2.49  fof(f608,plain,(
% 15.31/2.49    m1_subset_1(sK55,u1_struct_0(sK51))),
% 15.31/2.49    inference(cnf_transformation,[],[f381])).
% 15.31/2.49  
% 15.31/2.49  fof(f104,axiom,(
% 15.31/2.49    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 15.31/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.49  
% 15.31/2.49  fof(f235,plain,(
% 15.31/2.49    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 15.31/2.49    inference(ennf_transformation,[],[f104])).
% 15.31/2.49  
% 15.31/2.49  fof(f573,plain,(
% 15.31/2.49    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 15.31/2.49    inference(cnf_transformation,[],[f235])).
% 15.31/2.49  
% 15.31/2.49  fof(f606,plain,(
% 15.31/2.49    g1_pre_topc(u1_struct_0(sK51),u1_pre_topc(sK51)) = sK52),
% 15.31/2.49    inference(cnf_transformation,[],[f381])).
% 15.31/2.49  
% 15.31/2.49  fof(f83,axiom,(
% 15.31/2.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 15.31/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.49  
% 15.31/2.49  fof(f215,plain,(
% 15.31/2.49    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 15.31/2.49    inference(ennf_transformation,[],[f83])).
% 15.31/2.49  
% 15.31/2.49  fof(f336,plain,(
% 15.31/2.49    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 15.31/2.49    inference(nnf_transformation,[],[f215])).
% 15.31/2.49  
% 15.31/2.49  fof(f540,plain,(
% 15.31/2.49    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 15.31/2.49    inference(cnf_transformation,[],[f336])).
% 15.31/2.49  
% 15.31/2.49  fof(f102,axiom,(
% 15.31/2.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1 => (m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0))))))),
% 15.31/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.49  
% 15.31/2.49  fof(f232,plain,(
% 15.31/2.49    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | ~l1_pre_topc(X0))),
% 15.31/2.49    inference(ennf_transformation,[],[f102])).
% 15.31/2.49  
% 15.31/2.49  fof(f233,plain,(
% 15.31/2.49    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 15.31/2.49    inference(flattening,[],[f232])).
% 15.31/2.49  
% 15.31/2.49  fof(f359,plain,(
% 15.31/2.49    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) & (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0))) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 15.31/2.49    inference(nnf_transformation,[],[f233])).
% 15.31/2.49  
% 15.31/2.49  fof(f571,plain,(
% 15.31/2.49    ( ! [X2,X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 15.31/2.49    inference(cnf_transformation,[],[f359])).
% 15.31/2.49  
% 15.31/2.49  fof(f629,plain,(
% 15.31/2.49    ( ! [X2,X0] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~l1_pre_topc(X0)) )),
% 15.31/2.49    inference(equality_resolution,[],[f571])).
% 15.31/2.49  
% 15.31/2.49  fof(f77,axiom,(
% 15.31/2.49    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => v2_pre_topc(X0)))),
% 15.31/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.49  
% 15.31/2.49  fof(f204,plain,(
% 15.31/2.49    ! [X0] : ((v2_pre_topc(X0) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 15.31/2.49    inference(ennf_transformation,[],[f77])).
% 15.31/2.49  
% 15.31/2.49  fof(f205,plain,(
% 15.31/2.49    ! [X0] : (v2_pre_topc(X0) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 15.31/2.49    inference(flattening,[],[f204])).
% 15.31/2.49  
% 15.31/2.49  fof(f526,plain,(
% 15.31/2.49    ( ! [X0] : (v2_pre_topc(X0) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 15.31/2.49    inference(cnf_transformation,[],[f205])).
% 15.31/2.49  
% 15.31/2.49  fof(f58,axiom,(
% 15.31/2.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 15.31/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.49  
% 15.31/2.49  fof(f179,plain,(
% 15.31/2.49    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 15.31/2.49    inference(ennf_transformation,[],[f58])).
% 15.31/2.49  
% 15.31/2.49  fof(f180,plain,(
% 15.31/2.49    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.31/2.49    inference(flattening,[],[f179])).
% 15.31/2.49  
% 15.31/2.49  fof(f502,plain,(
% 15.31/2.49    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.31/2.49    inference(cnf_transformation,[],[f180])).
% 15.31/2.49  
% 15.31/2.49  fof(f109,axiom,(
% 15.31/2.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 15.31/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.49  
% 15.31/2.49  fof(f243,plain,(
% 15.31/2.49    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 15.31/2.49    inference(ennf_transformation,[],[f109])).
% 15.31/2.49  
% 15.31/2.49  fof(f244,plain,(
% 15.31/2.49    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.31/2.49    inference(flattening,[],[f243])).
% 15.31/2.49  
% 15.31/2.49  fof(f588,plain,(
% 15.31/2.49    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.31/2.49    inference(cnf_transformation,[],[f244])).
% 15.31/2.49  
% 15.31/2.49  fof(f105,axiom,(
% 15.31/2.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 15.31/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.49  
% 15.31/2.49  fof(f236,plain,(
% 15.31/2.49    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 15.31/2.49    inference(ennf_transformation,[],[f105])).
% 15.31/2.49  
% 15.31/2.49  fof(f574,plain,(
% 15.31/2.49    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 15.31/2.49    inference(cnf_transformation,[],[f236])).
% 15.31/2.49  
% 15.31/2.49  fof(f24,axiom,(
% 15.31/2.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 15.31/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.49  
% 15.31/2.49  fof(f276,plain,(
% 15.31/2.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 15.31/2.49    inference(nnf_transformation,[],[f24])).
% 15.31/2.49  
% 15.31/2.49  fof(f419,plain,(
% 15.31/2.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 15.31/2.49    inference(cnf_transformation,[],[f276])).
% 15.31/2.49  
% 15.31/2.49  fof(f107,axiom,(
% 15.31/2.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 15.31/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.49  
% 15.31/2.49  fof(f239,plain,(
% 15.31/2.49    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 15.31/2.49    inference(ennf_transformation,[],[f107])).
% 15.31/2.49  
% 15.31/2.49  fof(f240,plain,(
% 15.31/2.49    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.31/2.49    inference(flattening,[],[f239])).
% 15.31/2.49  
% 15.31/2.49  fof(f364,plain,(
% 15.31/2.49    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.31/2.49    inference(nnf_transformation,[],[f240])).
% 15.31/2.49  
% 15.31/2.49  fof(f579,plain,(
% 15.31/2.49    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.31/2.49    inference(cnf_transformation,[],[f364])).
% 15.31/2.49  
% 15.31/2.49  fof(f5,axiom,(
% 15.31/2.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 15.31/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.49  
% 15.31/2.49  fof(f261,plain,(
% 15.31/2.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.31/2.49    inference(nnf_transformation,[],[f5])).
% 15.31/2.49  
% 15.31/2.49  fof(f262,plain,(
% 15.31/2.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.31/2.49    inference(flattening,[],[f261])).
% 15.31/2.49  
% 15.31/2.49  fof(f388,plain,(
% 15.31/2.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 15.31/2.49    inference(cnf_transformation,[],[f262])).
% 15.31/2.49  
% 15.31/2.49  fof(f90,axiom,(
% 15.31/2.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 15.31/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.49  
% 15.31/2.49  fof(f221,plain,(
% 15.31/2.49    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 15.31/2.49    inference(ennf_transformation,[],[f90])).
% 15.31/2.49  
% 15.31/2.49  fof(f222,plain,(
% 15.31/2.49    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.31/2.49    inference(flattening,[],[f221])).
% 15.31/2.49  
% 15.31/2.49  fof(f547,plain,(
% 15.31/2.49    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.31/2.49    inference(cnf_transformation,[],[f222])).
% 15.31/2.49  
% 15.31/2.49  cnf(c_215,negated_conjecture,
% 15.31/2.49      ( m1_subset_1(sK54,u1_struct_0(sK52)) ),
% 15.31/2.49      inference(cnf_transformation,[],[f607]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_13539,plain,
% 15.31/2.49      ( m1_subset_1(sK54,u1_struct_0(sK52)) = iProver_top ),
% 15.31/2.49      inference(predicate_to_equality,[status(thm)],[c_215]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_35,plain,
% 15.31/2.49      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 15.31/2.49      inference(cnf_transformation,[],[f417]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_13682,plain,
% 15.31/2.49      ( m1_subset_1(X0,X1) != iProver_top
% 15.31/2.49      | r2_hidden(X0,X1) = iProver_top
% 15.31/2.49      | v1_xboole_0(X1) = iProver_top ),
% 15.31/2.49      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_32581,plain,
% 15.31/2.49      ( r2_hidden(sK54,u1_struct_0(sK52)) = iProver_top
% 15.31/2.49      | v1_xboole_0(u1_struct_0(sK52)) = iProver_top ),
% 15.31/2.49      inference(superposition,[status(thm)],[c_13539,c_13682]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_227,negated_conjecture,
% 15.31/2.49      ( l1_pre_topc(sK49) ),
% 15.31/2.49      inference(cnf_transformation,[],[f595]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_232,plain,
% 15.31/2.49      ( l1_pre_topc(sK49) = iProver_top ),
% 15.31/2.49      inference(predicate_to_equality,[status(thm)],[c_227]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_221,negated_conjecture,
% 15.31/2.49      ( ~ v2_struct_0(sK52) ),
% 15.31/2.49      inference(cnf_transformation,[],[f601]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_238,plain,
% 15.31/2.49      ( v2_struct_0(sK52) != iProver_top ),
% 15.31/2.49      inference(predicate_to_equality,[status(thm)],[c_221]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_220,negated_conjecture,
% 15.31/2.49      ( m1_pre_topc(sK52,sK49) ),
% 15.31/2.49      inference(cnf_transformation,[],[f602]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_239,plain,
% 15.31/2.49      ( m1_pre_topc(sK52,sK49) = iProver_top ),
% 15.31/2.49      inference(predicate_to_equality,[status(thm)],[c_220]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_124,plain,
% 15.31/2.49      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 15.31/2.49      inference(cnf_transformation,[],[f506]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_131,plain,
% 15.31/2.49      ( v2_struct_0(X0)
% 15.31/2.49      | ~ l1_struct_0(X0)
% 15.31/2.49      | ~ v1_xboole_0(k2_struct_0(X0)) ),
% 15.31/2.49      inference(cnf_transformation,[],[f513]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_2680,plain,
% 15.31/2.49      ( v2_struct_0(X0)
% 15.31/2.49      | ~ l1_pre_topc(X0)
% 15.31/2.49      | ~ v1_xboole_0(k2_struct_0(X0)) ),
% 15.31/2.49      inference(resolution,[status(thm)],[c_124,c_131]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_13984,plain,
% 15.31/2.49      ( v2_struct_0(sK52)
% 15.31/2.49      | ~ l1_pre_topc(sK52)
% 15.31/2.49      | ~ v1_xboole_0(k2_struct_0(sK52)) ),
% 15.31/2.49      inference(instantiation,[status(thm)],[c_2680]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_13985,plain,
% 15.31/2.49      ( v2_struct_0(sK52) = iProver_top
% 15.31/2.49      | l1_pre_topc(sK52) != iProver_top
% 15.31/2.49      | v1_xboole_0(k2_struct_0(sK52)) != iProver_top ),
% 15.31/2.49      inference(predicate_to_equality,[status(thm)],[c_13984]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_125,plain,
% 15.31/2.49      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 15.31/2.49      inference(cnf_transformation,[],[f507]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_14331,plain,
% 15.31/2.49      ( ~ m1_pre_topc(sK52,X0) | ~ l1_pre_topc(X0) | l1_pre_topc(sK52) ),
% 15.31/2.49      inference(instantiation,[status(thm)],[c_125]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_16931,plain,
% 15.31/2.49      ( ~ m1_pre_topc(sK52,sK49)
% 15.31/2.49      | ~ l1_pre_topc(sK49)
% 15.31/2.49      | l1_pre_topc(sK52) ),
% 15.31/2.49      inference(instantiation,[status(thm)],[c_14331]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_16932,plain,
% 15.31/2.49      ( m1_pre_topc(sK52,sK49) != iProver_top
% 15.31/2.49      | l1_pre_topc(sK49) != iProver_top
% 15.31/2.49      | l1_pre_topc(sK52) = iProver_top ),
% 15.31/2.49      inference(predicate_to_equality,[status(thm)],[c_16931]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_9615,plain,
% 15.31/2.49      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 15.31/2.49      theory(equality) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_18342,plain,
% 15.31/2.49      ( ~ v1_xboole_0(X0)
% 15.31/2.49      | v1_xboole_0(k2_struct_0(sK52))
% 15.31/2.49      | k2_struct_0(sK52) != X0 ),
% 15.31/2.49      inference(instantiation,[status(thm)],[c_9615]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_26440,plain,
% 15.31/2.49      ( v1_xboole_0(k2_struct_0(sK52))
% 15.31/2.49      | ~ v1_xboole_0(u1_struct_0(sK52))
% 15.31/2.49      | k2_struct_0(sK52) != u1_struct_0(sK52) ),
% 15.31/2.49      inference(instantiation,[status(thm)],[c_18342]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_26441,plain,
% 15.31/2.49      ( k2_struct_0(sK52) != u1_struct_0(sK52)
% 15.31/2.49      | v1_xboole_0(k2_struct_0(sK52)) = iProver_top
% 15.31/2.49      | v1_xboole_0(u1_struct_0(sK52)) != iProver_top ),
% 15.31/2.49      inference(predicate_to_equality,[status(thm)],[c_26440]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_13535,plain,
% 15.31/2.49      ( m1_pre_topc(sK52,sK49) = iProver_top ),
% 15.31/2.49      inference(predicate_to_equality,[status(thm)],[c_220]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_13621,plain,
% 15.31/2.49      ( m1_pre_topc(X0,X1) != iProver_top
% 15.31/2.49      | l1_pre_topc(X1) != iProver_top
% 15.31/2.49      | l1_pre_topc(X0) = iProver_top ),
% 15.31/2.49      inference(predicate_to_equality,[status(thm)],[c_125]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_32550,plain,
% 15.31/2.49      ( l1_pre_topc(sK49) != iProver_top
% 15.31/2.49      | l1_pre_topc(sK52) = iProver_top ),
% 15.31/2.49      inference(superposition,[status(thm)],[c_13535,c_13621]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_32766,plain,
% 15.31/2.49      ( l1_pre_topc(sK52) = iProver_top ),
% 15.31/2.49      inference(global_propositional_subsumption,
% 15.31/2.49                [status(thm)],
% 15.31/2.49                [c_32550,c_232,c_239,c_16932]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_122,plain,
% 15.31/2.49      ( ~ l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 15.31/2.49      inference(cnf_transformation,[],[f504]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_2705,plain,
% 15.31/2.49      ( ~ l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 15.31/2.49      inference(resolution,[status(thm)],[c_124,c_122]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_13515,plain,
% 15.31/2.49      ( k2_struct_0(X0) = u1_struct_0(X0)
% 15.31/2.49      | l1_pre_topc(X0) != iProver_top ),
% 15.31/2.49      inference(predicate_to_equality,[status(thm)],[c_2705]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_32771,plain,
% 15.31/2.49      ( k2_struct_0(sK52) = u1_struct_0(sK52) ),
% 15.31/2.49      inference(superposition,[status(thm)],[c_32766,c_13515]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_32856,plain,
% 15.31/2.49      ( r2_hidden(sK54,u1_struct_0(sK52)) = iProver_top ),
% 15.31/2.49      inference(global_propositional_subsumption,
% 15.31/2.49                [status(thm)],
% 15.31/2.49                [c_32581,c_232,c_238,c_239,c_13985,c_16932,c_26441,
% 15.31/2.49                 c_32771]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_190,plain,
% 15.31/2.49      ( ~ m1_pre_topc(X0,X1)
% 15.31/2.49      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 15.31/2.49      | ~ l1_pre_topc(X1) ),
% 15.31/2.49      inference(cnf_transformation,[],[f572]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_13563,plain,
% 15.31/2.49      ( m1_pre_topc(X0,X1) != iProver_top
% 15.31/2.49      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 15.31/2.49      | l1_pre_topc(X1) != iProver_top ),
% 15.31/2.49      inference(predicate_to_equality,[status(thm)],[c_190]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_212,negated_conjecture,
% 15.31/2.49      ( r1_tmap_1(sK51,sK50,k3_tmap_1(sK49,sK50,sK52,sK51,sK53),sK55) ),
% 15.31/2.49      inference(cnf_transformation,[],[f610]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_13541,plain,
% 15.31/2.49      ( r1_tmap_1(sK51,sK50,k3_tmap_1(sK49,sK50,sK52,sK51,sK53),sK55) = iProver_top ),
% 15.31/2.49      inference(predicate_to_equality,[status(thm)],[c_212]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_213,negated_conjecture,
% 15.31/2.49      ( sK54 = sK55 ),
% 15.31/2.49      inference(cnf_transformation,[],[f609]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_13708,plain,
% 15.31/2.49      ( r1_tmap_1(sK51,sK50,k3_tmap_1(sK49,sK50,sK52,sK51,sK53),sK54) = iProver_top ),
% 15.31/2.49      inference(light_normalisation,[status(thm)],[c_13541,c_213]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_207,plain,
% 15.31/2.49      ( r1_tmap_1(X0,X1,X2,X3)
% 15.31/2.49      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 15.31/2.49      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 15.31/2.49      | ~ v3_pre_topc(X6,X0)
% 15.31/2.49      | ~ m1_pre_topc(X4,X5)
% 15.31/2.49      | ~ m1_pre_topc(X0,X5)
% 15.31/2.49      | ~ m1_pre_topc(X4,X0)
% 15.31/2.49      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 15.31/2.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 15.31/2.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 15.31/2.49      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 15.31/2.49      | ~ r1_tarski(X6,u1_struct_0(X4))
% 15.31/2.49      | ~ r2_hidden(X3,X6)
% 15.31/2.49      | v2_struct_0(X5)
% 15.31/2.49      | v2_struct_0(X1)
% 15.31/2.49      | v2_struct_0(X0)
% 15.31/2.49      | v2_struct_0(X4)
% 15.31/2.49      | ~ l1_pre_topc(X5)
% 15.31/2.49      | ~ l1_pre_topc(X1)
% 15.31/2.49      | ~ v2_pre_topc(X5)
% 15.31/2.49      | ~ v2_pre_topc(X1)
% 15.31/2.49      | ~ v1_funct_1(X2) ),
% 15.31/2.49      inference(cnf_transformation,[],[f631]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_13546,plain,
% 15.31/2.49      ( r1_tmap_1(X0,X1,X2,X3) = iProver_top
% 15.31/2.49      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3) != iProver_top
% 15.31/2.49      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 15.31/2.49      | v3_pre_topc(X6,X0) != iProver_top
% 15.31/2.49      | m1_pre_topc(X4,X5) != iProver_top
% 15.31/2.49      | m1_pre_topc(X0,X5) != iProver_top
% 15.31/2.49      | m1_pre_topc(X4,X0) != iProver_top
% 15.31/2.49      | m1_subset_1(X3,u1_struct_0(X4)) != iProver_top
% 15.31/2.49      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 15.31/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 15.31/2.49      | m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 15.31/2.49      | r1_tarski(X6,u1_struct_0(X4)) != iProver_top
% 15.31/2.49      | r2_hidden(X3,X6) != iProver_top
% 15.31/2.49      | v2_struct_0(X1) = iProver_top
% 15.31/2.49      | v2_struct_0(X5) = iProver_top
% 15.31/2.49      | v2_struct_0(X0) = iProver_top
% 15.31/2.49      | v2_struct_0(X4) = iProver_top
% 15.31/2.49      | l1_pre_topc(X1) != iProver_top
% 15.31/2.49      | l1_pre_topc(X5) != iProver_top
% 15.31/2.49      | v2_pre_topc(X1) != iProver_top
% 15.31/2.49      | v2_pre_topc(X5) != iProver_top
% 15.31/2.49      | v1_funct_1(X2) != iProver_top ),
% 15.31/2.49      inference(predicate_to_equality,[status(thm)],[c_207]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_33462,plain,
% 15.31/2.49      ( r1_tmap_1(sK52,sK50,sK53,sK54) = iProver_top
% 15.31/2.49      | v1_funct_2(sK53,u1_struct_0(sK52),u1_struct_0(sK50)) != iProver_top
% 15.31/2.49      | v3_pre_topc(X0,sK52) != iProver_top
% 15.31/2.49      | m1_pre_topc(sK51,sK49) != iProver_top
% 15.31/2.49      | m1_pre_topc(sK51,sK52) != iProver_top
% 15.31/2.49      | m1_pre_topc(sK52,sK49) != iProver_top
% 15.31/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK52))) != iProver_top
% 15.31/2.49      | m1_subset_1(sK54,u1_struct_0(sK51)) != iProver_top
% 15.31/2.49      | m1_subset_1(sK54,u1_struct_0(sK52)) != iProver_top
% 15.31/2.49      | m1_subset_1(sK53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK52),u1_struct_0(sK50)))) != iProver_top
% 15.31/2.49      | r1_tarski(X0,u1_struct_0(sK51)) != iProver_top
% 15.31/2.49      | r2_hidden(sK54,X0) != iProver_top
% 15.31/2.49      | v2_struct_0(sK49) = iProver_top
% 15.31/2.49      | v2_struct_0(sK51) = iProver_top
% 15.31/2.49      | v2_struct_0(sK50) = iProver_top
% 15.31/2.49      | v2_struct_0(sK52) = iProver_top
% 15.31/2.49      | l1_pre_topc(sK49) != iProver_top
% 15.31/2.49      | l1_pre_topc(sK50) != iProver_top
% 15.31/2.49      | v2_pre_topc(sK49) != iProver_top
% 15.31/2.49      | v2_pre_topc(sK50) != iProver_top
% 15.31/2.49      | v1_funct_1(sK53) != iProver_top ),
% 15.31/2.49      inference(superposition,[status(thm)],[c_13708,c_13546]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_229,negated_conjecture,
% 15.31/2.49      ( ~ v2_struct_0(sK49) ),
% 15.31/2.49      inference(cnf_transformation,[],[f593]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_230,plain,
% 15.31/2.49      ( v2_struct_0(sK49) != iProver_top ),
% 15.31/2.49      inference(predicate_to_equality,[status(thm)],[c_229]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_228,negated_conjecture,
% 15.31/2.49      ( v2_pre_topc(sK49) ),
% 15.31/2.49      inference(cnf_transformation,[],[f594]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_231,plain,
% 15.31/2.49      ( v2_pre_topc(sK49) = iProver_top ),
% 15.31/2.49      inference(predicate_to_equality,[status(thm)],[c_228]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_226,negated_conjecture,
% 15.31/2.49      ( ~ v2_struct_0(sK50) ),
% 15.31/2.49      inference(cnf_transformation,[],[f596]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_233,plain,
% 15.31/2.49      ( v2_struct_0(sK50) != iProver_top ),
% 15.31/2.49      inference(predicate_to_equality,[status(thm)],[c_226]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_225,negated_conjecture,
% 15.31/2.49      ( v2_pre_topc(sK50) ),
% 15.31/2.49      inference(cnf_transformation,[],[f597]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_234,plain,
% 15.31/2.49      ( v2_pre_topc(sK50) = iProver_top ),
% 15.31/2.49      inference(predicate_to_equality,[status(thm)],[c_225]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_224,negated_conjecture,
% 15.31/2.49      ( l1_pre_topc(sK50) ),
% 15.31/2.49      inference(cnf_transformation,[],[f598]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_235,plain,
% 15.31/2.49      ( l1_pre_topc(sK50) = iProver_top ),
% 15.31/2.49      inference(predicate_to_equality,[status(thm)],[c_224]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_223,negated_conjecture,
% 15.31/2.49      ( ~ v2_struct_0(sK51) ),
% 15.31/2.49      inference(cnf_transformation,[],[f599]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_236,plain,
% 15.31/2.49      ( v2_struct_0(sK51) != iProver_top ),
% 15.31/2.49      inference(predicate_to_equality,[status(thm)],[c_223]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_222,negated_conjecture,
% 15.31/2.49      ( m1_pre_topc(sK51,sK49) ),
% 15.31/2.49      inference(cnf_transformation,[],[f600]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_237,plain,
% 15.31/2.49      ( m1_pre_topc(sK51,sK49) = iProver_top ),
% 15.31/2.49      inference(predicate_to_equality,[status(thm)],[c_222]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_219,negated_conjecture,
% 15.31/2.49      ( v1_funct_1(sK53) ),
% 15.31/2.49      inference(cnf_transformation,[],[f603]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_240,plain,
% 15.31/2.49      ( v1_funct_1(sK53) = iProver_top ),
% 15.31/2.49      inference(predicate_to_equality,[status(thm)],[c_219]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_218,negated_conjecture,
% 15.31/2.49      ( v1_funct_2(sK53,u1_struct_0(sK52),u1_struct_0(sK50)) ),
% 15.31/2.49      inference(cnf_transformation,[],[f604]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_241,plain,
% 15.31/2.49      ( v1_funct_2(sK53,u1_struct_0(sK52),u1_struct_0(sK50)) = iProver_top ),
% 15.31/2.49      inference(predicate_to_equality,[status(thm)],[c_218]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_217,negated_conjecture,
% 15.31/2.49      ( m1_subset_1(sK53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK52),u1_struct_0(sK50)))) ),
% 15.31/2.49      inference(cnf_transformation,[],[f605]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_242,plain,
% 15.31/2.49      ( m1_subset_1(sK53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK52),u1_struct_0(sK50)))) = iProver_top ),
% 15.31/2.49      inference(predicate_to_equality,[status(thm)],[c_217]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_243,plain,
% 15.31/2.49      ( m1_subset_1(sK54,u1_struct_0(sK52)) = iProver_top ),
% 15.31/2.49      inference(predicate_to_equality,[status(thm)],[c_215]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_211,negated_conjecture,
% 15.31/2.49      ( ~ r1_tmap_1(sK52,sK50,sK53,sK54) ),
% 15.31/2.49      inference(cnf_transformation,[],[f611]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_246,plain,
% 15.31/2.49      ( r1_tmap_1(sK52,sK50,sK53,sK54) != iProver_top ),
% 15.31/2.49      inference(predicate_to_equality,[status(thm)],[c_211]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_214,negated_conjecture,
% 15.31/2.49      ( m1_subset_1(sK55,u1_struct_0(sK51)) ),
% 15.31/2.49      inference(cnf_transformation,[],[f608]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_13540,plain,
% 15.31/2.49      ( m1_subset_1(sK55,u1_struct_0(sK51)) = iProver_top ),
% 15.31/2.49      inference(predicate_to_equality,[status(thm)],[c_214]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_13700,plain,
% 15.31/2.49      ( m1_subset_1(sK54,u1_struct_0(sK51)) = iProver_top ),
% 15.31/2.49      inference(light_normalisation,[status(thm)],[c_13540,c_213]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_14425,plain,
% 15.31/2.49      ( ~ m1_pre_topc(sK51,X0) | ~ l1_pre_topc(X0) | l1_pre_topc(sK51) ),
% 15.31/2.49      inference(instantiation,[status(thm)],[c_125]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_16969,plain,
% 15.31/2.49      ( ~ m1_pre_topc(sK51,sK49)
% 15.31/2.49      | ~ l1_pre_topc(sK49)
% 15.31/2.49      | l1_pre_topc(sK51) ),
% 15.31/2.49      inference(instantiation,[status(thm)],[c_14425]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_16970,plain,
% 15.31/2.49      ( m1_pre_topc(sK51,sK49) != iProver_top
% 15.31/2.49      | l1_pre_topc(sK49) != iProver_top
% 15.31/2.49      | l1_pre_topc(sK51) = iProver_top ),
% 15.31/2.49      inference(predicate_to_equality,[status(thm)],[c_16969]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_191,plain,
% 15.31/2.49      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 15.31/2.49      inference(cnf_transformation,[],[f573]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_13562,plain,
% 15.31/2.49      ( m1_pre_topc(X0,X0) = iProver_top
% 15.31/2.49      | l1_pre_topc(X0) != iProver_top ),
% 15.31/2.49      inference(predicate_to_equality,[status(thm)],[c_191]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_216,negated_conjecture,
% 15.31/2.49      ( g1_pre_topc(u1_struct_0(sK51),u1_pre_topc(sK51)) = sK52 ),
% 15.31/2.49      inference(cnf_transformation,[],[f606]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_159,plain,
% 15.31/2.49      ( ~ m1_pre_topc(X0,X1)
% 15.31/2.49      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 15.31/2.49      | ~ l1_pre_topc(X0)
% 15.31/2.49      | ~ l1_pre_topc(X1) ),
% 15.31/2.49      inference(cnf_transformation,[],[f540]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_1232,plain,
% 15.31/2.49      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 15.31/2.49      | ~ m1_pre_topc(X0,X1)
% 15.31/2.49      | ~ l1_pre_topc(X1) ),
% 15.31/2.49      inference(global_propositional_subsumption,
% 15.31/2.49                [status(thm)],
% 15.31/2.49                [c_159,c_125]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_1233,plain,
% 15.31/2.49      ( ~ m1_pre_topc(X0,X1)
% 15.31/2.49      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 15.31/2.49      | ~ l1_pre_topc(X1) ),
% 15.31/2.49      inference(renaming,[status(thm)],[c_1232]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_13523,plain,
% 15.31/2.49      ( m1_pre_topc(X0,X1) != iProver_top
% 15.31/2.49      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 15.31/2.49      | l1_pre_topc(X1) != iProver_top ),
% 15.31/2.49      inference(predicate_to_equality,[status(thm)],[c_1233]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_27301,plain,
% 15.31/2.49      ( m1_pre_topc(X0,sK51) != iProver_top
% 15.31/2.49      | m1_pre_topc(X0,sK52) = iProver_top
% 15.31/2.49      | l1_pre_topc(sK51) != iProver_top ),
% 15.31/2.49      inference(superposition,[status(thm)],[c_216,c_13523]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_27436,plain,
% 15.31/2.49      ( m1_pre_topc(X0,sK52) = iProver_top
% 15.31/2.49      | m1_pre_topc(X0,sK51) != iProver_top ),
% 15.31/2.49      inference(global_propositional_subsumption,
% 15.31/2.49                [status(thm)],
% 15.31/2.49                [c_27301,c_232,c_237,c_16970]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_27437,plain,
% 15.31/2.49      ( m1_pre_topc(X0,sK51) != iProver_top
% 15.31/2.49      | m1_pre_topc(X0,sK52) = iProver_top ),
% 15.31/2.49      inference(renaming,[status(thm)],[c_27436]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_27443,plain,
% 15.31/2.49      ( m1_pre_topc(sK51,sK52) = iProver_top
% 15.31/2.49      | l1_pre_topc(sK51) != iProver_top ),
% 15.31/2.49      inference(superposition,[status(thm)],[c_13562,c_27437]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_34225,plain,
% 15.31/2.49      ( r2_hidden(sK54,X0) != iProver_top
% 15.31/2.49      | r1_tarski(X0,u1_struct_0(sK51)) != iProver_top
% 15.31/2.49      | v3_pre_topc(X0,sK52) != iProver_top
% 15.31/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK52))) != iProver_top ),
% 15.31/2.49      inference(global_propositional_subsumption,
% 15.31/2.49                [status(thm)],
% 15.31/2.49                [c_33462,c_230,c_231,c_232,c_233,c_234,c_235,c_236,c_237,
% 15.31/2.49                 c_238,c_239,c_240,c_241,c_242,c_243,c_246,c_13700,
% 15.31/2.49                 c_16970,c_27443]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_34226,plain,
% 15.31/2.49      ( v3_pre_topc(X0,sK52) != iProver_top
% 15.31/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK52))) != iProver_top
% 15.31/2.49      | r1_tarski(X0,u1_struct_0(sK51)) != iProver_top
% 15.31/2.49      | r2_hidden(sK54,X0) != iProver_top ),
% 15.31/2.49      inference(renaming,[status(thm)],[c_34225]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_43748,plain,
% 15.31/2.49      ( v3_pre_topc(u1_struct_0(X0),sK52) != iProver_top
% 15.31/2.49      | m1_pre_topc(X0,sK52) != iProver_top
% 15.31/2.49      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK51)) != iProver_top
% 15.31/2.49      | r2_hidden(sK54,u1_struct_0(X0)) != iProver_top
% 15.31/2.49      | l1_pre_topc(sK52) != iProver_top ),
% 15.31/2.49      inference(superposition,[status(thm)],[c_13563,c_34226]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_188,plain,
% 15.31/2.49      ( ~ m1_pre_topc(X0,X1)
% 15.31/2.49      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 15.31/2.49      | ~ l1_pre_topc(X1)
% 15.31/2.49      | ~ l1_pre_topc(X0)
% 15.31/2.49      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 15.31/2.49      | ~ v2_pre_topc(X0)
% 15.31/2.49      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 15.31/2.49      inference(cnf_transformation,[],[f629]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_144,plain,
% 15.31/2.49      ( ~ l1_pre_topc(X0)
% 15.31/2.49      | v2_pre_topc(X0)
% 15.31/2.49      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 15.31/2.49      inference(cnf_transformation,[],[f526]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_1197,plain,
% 15.31/2.49      ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 15.31/2.49      | ~ m1_pre_topc(X0,X1)
% 15.31/2.49      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 15.31/2.49      | ~ l1_pre_topc(X1)
% 15.31/2.49      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 15.31/2.49      inference(global_propositional_subsumption,
% 15.31/2.49                [status(thm)],
% 15.31/2.49                [c_188,c_144,c_125]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_1198,plain,
% 15.31/2.49      ( ~ m1_pre_topc(X0,X1)
% 15.31/2.49      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 15.31/2.49      | ~ l1_pre_topc(X1)
% 15.31/2.49      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 15.31/2.49      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 15.31/2.49      inference(renaming,[status(thm)],[c_1197]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_13524,plain,
% 15.31/2.49      ( m1_pre_topc(X0,X1) != iProver_top
% 15.31/2.49      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
% 15.31/2.49      | l1_pre_topc(X1) != iProver_top
% 15.31/2.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
% 15.31/2.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
% 15.31/2.49      inference(predicate_to_equality,[status(thm)],[c_1198]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_27807,plain,
% 15.31/2.49      ( m1_pre_topc(sK51,X0) != iProver_top
% 15.31/2.49      | m1_pre_topc(sK52,X0) = iProver_top
% 15.31/2.49      | l1_pre_topc(X0) != iProver_top
% 15.31/2.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK51),u1_pre_topc(sK51))) != iProver_top
% 15.31/2.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK51),u1_pre_topc(sK51))) != iProver_top ),
% 15.31/2.49      inference(superposition,[status(thm)],[c_216,c_13524]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_27809,plain,
% 15.31/2.49      ( m1_pre_topc(sK51,X0) != iProver_top
% 15.31/2.49      | m1_pre_topc(sK52,X0) = iProver_top
% 15.31/2.49      | l1_pre_topc(X0) != iProver_top
% 15.31/2.49      | l1_pre_topc(sK52) != iProver_top
% 15.31/2.49      | v2_pre_topc(sK52) != iProver_top ),
% 15.31/2.49      inference(light_normalisation,[status(thm)],[c_27807,c_216]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_120,plain,
% 15.31/2.49      ( ~ m1_pre_topc(X0,X1)
% 15.31/2.49      | ~ l1_pre_topc(X1)
% 15.31/2.49      | ~ v2_pre_topc(X1)
% 15.31/2.49      | v2_pre_topc(X0) ),
% 15.31/2.49      inference(cnf_transformation,[],[f502]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_18312,plain,
% 15.31/2.49      ( ~ m1_pre_topc(sK52,X0)
% 15.31/2.49      | ~ l1_pre_topc(X0)
% 15.31/2.49      | ~ v2_pre_topc(X0)
% 15.31/2.49      | v2_pre_topc(sK52) ),
% 15.31/2.49      inference(instantiation,[status(thm)],[c_120]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_27042,plain,
% 15.31/2.49      ( ~ m1_pre_topc(sK52,sK49)
% 15.31/2.49      | ~ l1_pre_topc(sK49)
% 15.31/2.49      | ~ v2_pre_topc(sK49)
% 15.31/2.49      | v2_pre_topc(sK52) ),
% 15.31/2.49      inference(instantiation,[status(thm)],[c_18312]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_27043,plain,
% 15.31/2.49      ( m1_pre_topc(sK52,sK49) != iProver_top
% 15.31/2.49      | l1_pre_topc(sK49) != iProver_top
% 15.31/2.49      | v2_pre_topc(sK49) != iProver_top
% 15.31/2.49      | v2_pre_topc(sK52) = iProver_top ),
% 15.31/2.49      inference(predicate_to_equality,[status(thm)],[c_27042]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_28376,plain,
% 15.31/2.49      ( m1_pre_topc(sK51,X0) != iProver_top
% 15.31/2.49      | m1_pre_topc(sK52,X0) = iProver_top
% 15.31/2.49      | l1_pre_topc(X0) != iProver_top ),
% 15.31/2.49      inference(global_propositional_subsumption,
% 15.31/2.49                [status(thm)],
% 15.31/2.49                [c_27809,c_231,c_232,c_239,c_16932,c_27043]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_28383,plain,
% 15.31/2.49      ( m1_pre_topc(sK52,sK51) = iProver_top
% 15.31/2.49      | l1_pre_topc(sK51) != iProver_top ),
% 15.31/2.49      inference(superposition,[status(thm)],[c_13562,c_28376]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_28516,plain,
% 15.31/2.49      ( m1_pre_topc(sK52,sK51) = iProver_top ),
% 15.31/2.49      inference(global_propositional_subsumption,
% 15.31/2.49                [status(thm)],
% 15.31/2.49                [c_28383,c_232,c_237,c_16970]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_206,plain,
% 15.31/2.49      ( ~ m1_pre_topc(X0,X1)
% 15.31/2.49      | ~ m1_pre_topc(X2,X0)
% 15.31/2.49      | m1_pre_topc(X2,X1)
% 15.31/2.49      | ~ l1_pre_topc(X1)
% 15.31/2.49      | ~ v2_pre_topc(X1) ),
% 15.31/2.49      inference(cnf_transformation,[],[f588]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_13547,plain,
% 15.31/2.49      ( m1_pre_topc(X0,X1) != iProver_top
% 15.31/2.49      | m1_pre_topc(X2,X0) != iProver_top
% 15.31/2.49      | m1_pre_topc(X2,X1) = iProver_top
% 15.31/2.49      | l1_pre_topc(X1) != iProver_top
% 15.31/2.49      | v2_pre_topc(X1) != iProver_top ),
% 15.31/2.49      inference(predicate_to_equality,[status(thm)],[c_206]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_34714,plain,
% 15.31/2.49      ( m1_pre_topc(X0,sK51) = iProver_top
% 15.31/2.49      | m1_pre_topc(X0,sK52) != iProver_top
% 15.31/2.49      | l1_pre_topc(sK51) != iProver_top
% 15.31/2.49      | v2_pre_topc(sK51) != iProver_top ),
% 15.31/2.49      inference(superposition,[status(thm)],[c_28516,c_13547]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_18649,plain,
% 15.31/2.49      ( ~ m1_pre_topc(sK51,X0)
% 15.31/2.49      | ~ l1_pre_topc(X0)
% 15.31/2.49      | ~ v2_pre_topc(X0)
% 15.31/2.49      | v2_pre_topc(sK51) ),
% 15.31/2.49      inference(instantiation,[status(thm)],[c_120]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_27087,plain,
% 15.31/2.49      ( ~ m1_pre_topc(sK51,sK49)
% 15.31/2.49      | ~ l1_pre_topc(sK49)
% 15.31/2.49      | ~ v2_pre_topc(sK49)
% 15.31/2.49      | v2_pre_topc(sK51) ),
% 15.31/2.49      inference(instantiation,[status(thm)],[c_18649]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_27088,plain,
% 15.31/2.49      ( m1_pre_topc(sK51,sK49) != iProver_top
% 15.31/2.49      | l1_pre_topc(sK49) != iProver_top
% 15.31/2.49      | v2_pre_topc(sK49) != iProver_top
% 15.31/2.49      | v2_pre_topc(sK51) = iProver_top ),
% 15.31/2.49      inference(predicate_to_equality,[status(thm)],[c_27087]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_39588,plain,
% 15.31/2.49      ( m1_pre_topc(X0,sK51) = iProver_top
% 15.31/2.49      | m1_pre_topc(X0,sK52) != iProver_top ),
% 15.31/2.49      inference(global_propositional_subsumption,
% 15.31/2.49                [status(thm)],
% 15.31/2.49                [c_34714,c_231,c_232,c_237,c_16970,c_27088]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_192,plain,
% 15.31/2.49      ( ~ m1_pre_topc(X0,X1)
% 15.31/2.49      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 15.31/2.49      | ~ l1_pre_topc(X1) ),
% 15.31/2.49      inference(cnf_transformation,[],[f574]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_13561,plain,
% 15.31/2.49      ( m1_pre_topc(X0,X1) != iProver_top
% 15.31/2.49      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 15.31/2.49      | l1_pre_topc(X1) != iProver_top ),
% 15.31/2.49      inference(predicate_to_equality,[status(thm)],[c_192]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_36,plain,
% 15.31/2.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.31/2.49      inference(cnf_transformation,[],[f419]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_13674,plain,
% 15.31/2.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 15.31/2.49      | r1_tarski(X0,X1) != iProver_top ),
% 15.31/2.49      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_34233,plain,
% 15.31/2.49      ( v3_pre_topc(X0,sK52) != iProver_top
% 15.31/2.49      | r1_tarski(X0,u1_struct_0(sK51)) != iProver_top
% 15.31/2.49      | r1_tarski(X0,u1_struct_0(sK52)) != iProver_top
% 15.31/2.49      | r2_hidden(sK54,X0) != iProver_top ),
% 15.31/2.49      inference(superposition,[status(thm)],[c_13674,c_34226]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_40657,plain,
% 15.31/2.49      ( v3_pre_topc(u1_struct_0(X0),sK52) != iProver_top
% 15.31/2.49      | m1_pre_topc(X0,sK51) != iProver_top
% 15.31/2.49      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK52)) != iProver_top
% 15.31/2.49      | r2_hidden(sK54,u1_struct_0(X0)) != iProver_top
% 15.31/2.49      | l1_pre_topc(sK51) != iProver_top ),
% 15.31/2.49      inference(superposition,[status(thm)],[c_13561,c_34233]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_13533,plain,
% 15.31/2.49      ( m1_pre_topc(sK51,sK49) = iProver_top ),
% 15.31/2.49      inference(predicate_to_equality,[status(thm)],[c_222]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_196,plain,
% 15.31/2.49      ( ~ m1_pre_topc(X0,X1)
% 15.31/2.49      | ~ m1_pre_topc(X2,X1)
% 15.31/2.49      | ~ m1_pre_topc(X0,X2)
% 15.31/2.49      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 15.31/2.49      | ~ l1_pre_topc(X1)
% 15.31/2.49      | ~ v2_pre_topc(X1) ),
% 15.31/2.49      inference(cnf_transformation,[],[f579]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_13557,plain,
% 15.31/2.49      ( m1_pre_topc(X0,X1) != iProver_top
% 15.31/2.49      | m1_pre_topc(X2,X1) != iProver_top
% 15.31/2.49      | m1_pre_topc(X0,X2) != iProver_top
% 15.31/2.49      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) = iProver_top
% 15.31/2.49      | l1_pre_topc(X1) != iProver_top
% 15.31/2.49      | v2_pre_topc(X1) != iProver_top ),
% 15.31/2.49      inference(predicate_to_equality,[status(thm)],[c_196]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_43546,plain,
% 15.31/2.49      ( m1_pre_topc(X0,sK49) != iProver_top
% 15.31/2.49      | m1_pre_topc(sK51,X0) != iProver_top
% 15.31/2.49      | r1_tarski(u1_struct_0(sK51),u1_struct_0(X0)) = iProver_top
% 15.31/2.49      | l1_pre_topc(sK49) != iProver_top
% 15.31/2.49      | v2_pre_topc(sK49) != iProver_top ),
% 15.31/2.49      inference(superposition,[status(thm)],[c_13533,c_13557]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_44123,plain,
% 15.31/2.49      ( m1_pre_topc(X0,sK49) != iProver_top
% 15.31/2.49      | m1_pre_topc(sK51,X0) != iProver_top
% 15.31/2.49      | r1_tarski(u1_struct_0(sK51),u1_struct_0(X0)) = iProver_top ),
% 15.31/2.49      inference(global_propositional_subsumption,
% 15.31/2.49                [status(thm)],
% 15.31/2.49                [c_43546,c_231,c_232]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_43545,plain,
% 15.31/2.49      ( m1_pre_topc(X0,sK49) != iProver_top
% 15.31/2.49      | m1_pre_topc(sK52,X0) != iProver_top
% 15.31/2.49      | r1_tarski(u1_struct_0(sK52),u1_struct_0(X0)) = iProver_top
% 15.31/2.49      | l1_pre_topc(sK49) != iProver_top
% 15.31/2.49      | v2_pre_topc(sK49) != iProver_top ),
% 15.31/2.49      inference(superposition,[status(thm)],[c_13535,c_13557]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_44103,plain,
% 15.31/2.49      ( m1_pre_topc(X0,sK49) != iProver_top
% 15.31/2.49      | m1_pre_topc(sK52,X0) != iProver_top
% 15.31/2.49      | r1_tarski(u1_struct_0(sK52),u1_struct_0(X0)) = iProver_top ),
% 15.31/2.49      inference(global_propositional_subsumption,
% 15.31/2.49                [status(thm)],
% 15.31/2.49                [c_43545,c_231,c_232]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_4,plain,
% 15.31/2.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 15.31/2.49      inference(cnf_transformation,[],[f388]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_13695,plain,
% 15.31/2.49      ( X0 = X1
% 15.31/2.49      | r1_tarski(X1,X0) != iProver_top
% 15.31/2.49      | r1_tarski(X0,X1) != iProver_top ),
% 15.31/2.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_44109,plain,
% 15.31/2.49      ( u1_struct_0(X0) = u1_struct_0(sK52)
% 15.31/2.49      | m1_pre_topc(X0,sK49) != iProver_top
% 15.31/2.49      | m1_pre_topc(sK52,X0) != iProver_top
% 15.31/2.49      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK52)) != iProver_top ),
% 15.31/2.49      inference(superposition,[status(thm)],[c_44103,c_13695]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_44362,plain,
% 15.31/2.49      ( u1_struct_0(sK52) = u1_struct_0(sK51)
% 15.31/2.49      | m1_pre_topc(sK51,sK49) != iProver_top
% 15.31/2.49      | m1_pre_topc(sK51,sK52) != iProver_top
% 15.31/2.49      | m1_pre_topc(sK52,sK49) != iProver_top
% 15.31/2.49      | m1_pre_topc(sK52,sK51) != iProver_top ),
% 15.31/2.49      inference(superposition,[status(thm)],[c_44123,c_44109]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_45732,plain,
% 15.31/2.49      ( u1_struct_0(sK52) = u1_struct_0(sK51) ),
% 15.31/2.49      inference(global_propositional_subsumption,
% 15.31/2.49                [status(thm)],
% 15.31/2.49                [c_44362,c_232,c_237,c_239,c_16970,c_27443,c_28383]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_45814,plain,
% 15.31/2.49      ( m1_pre_topc(X0,sK51) != iProver_top
% 15.31/2.49      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK52)) = iProver_top
% 15.31/2.49      | l1_pre_topc(sK51) != iProver_top ),
% 15.31/2.49      inference(superposition,[status(thm)],[c_45732,c_13561]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_47274,plain,
% 15.31/2.49      ( r2_hidden(sK54,u1_struct_0(X0)) != iProver_top
% 15.31/2.49      | v3_pre_topc(u1_struct_0(X0),sK52) != iProver_top
% 15.31/2.49      | m1_pre_topc(X0,sK52) != iProver_top ),
% 15.31/2.49      inference(global_propositional_subsumption,
% 15.31/2.49                [status(thm)],
% 15.31/2.49                [c_43748,c_231,c_232,c_237,c_16970,c_27088,c_34714,
% 15.31/2.49                 c_40657,c_45814]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_47275,plain,
% 15.31/2.49      ( v3_pre_topc(u1_struct_0(X0),sK52) != iProver_top
% 15.31/2.49      | m1_pre_topc(X0,sK52) != iProver_top
% 15.31/2.49      | r2_hidden(sK54,u1_struct_0(X0)) != iProver_top ),
% 15.31/2.49      inference(renaming,[status(thm)],[c_47274]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_47280,plain,
% 15.31/2.49      ( v3_pre_topc(u1_struct_0(sK52),sK52) != iProver_top
% 15.31/2.49      | m1_pre_topc(sK52,sK52) != iProver_top ),
% 15.31/2.49      inference(superposition,[status(thm)],[c_32856,c_47275]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_165,plain,
% 15.31/2.49      ( v3_pre_topc(k2_struct_0(X0),X0)
% 15.31/2.49      | ~ l1_pre_topc(X0)
% 15.31/2.49      | ~ v2_pre_topc(X0) ),
% 15.31/2.49      inference(cnf_transformation,[],[f547]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_13589,plain,
% 15.31/2.49      ( v3_pre_topc(k2_struct_0(X0),X0) = iProver_top
% 15.31/2.49      | l1_pre_topc(X0) != iProver_top
% 15.31/2.49      | v2_pre_topc(X0) != iProver_top ),
% 15.31/2.49      inference(predicate_to_equality,[status(thm)],[c_165]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_37829,plain,
% 15.31/2.49      ( v3_pre_topc(u1_struct_0(sK52),sK52) = iProver_top
% 15.31/2.49      | l1_pre_topc(sK52) != iProver_top
% 15.31/2.49      | v2_pre_topc(sK52) != iProver_top ),
% 15.31/2.49      inference(superposition,[status(thm)],[c_32771,c_13589]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_28520,plain,
% 15.31/2.49      ( m1_pre_topc(sK52,sK52) = iProver_top ),
% 15.31/2.49      inference(superposition,[status(thm)],[c_28516,c_27437]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(contradiction,plain,
% 15.31/2.49      ( $false ),
% 15.31/2.49      inference(minisat,
% 15.31/2.49                [status(thm)],
% 15.31/2.49                [c_47280,c_37829,c_28520,c_27043,c_16932,c_239,c_232,
% 15.31/2.49                 c_231]) ).
% 15.31/2.49  
% 15.31/2.49  
% 15.31/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.31/2.49  
% 15.31/2.49  ------                               Statistics
% 15.31/2.49  
% 15.31/2.49  ------ General
% 15.31/2.49  
% 15.31/2.49  abstr_ref_over_cycles:                  0
% 15.31/2.49  abstr_ref_under_cycles:                 0
% 15.31/2.49  gc_basic_clause_elim:                   0
% 15.31/2.49  forced_gc_time:                         0
% 15.31/2.49  parsing_time:                           0.023
% 15.31/2.49  unif_index_cands_time:                  0.
% 15.31/2.49  unif_index_add_time:                    0.
% 15.31/2.49  orderings_time:                         0.
% 15.31/2.49  out_proof_time:                         0.037
% 15.31/2.49  total_time:                             1.609
% 15.31/2.49  num_of_symbols:                         136
% 15.31/2.49  num_of_terms:                           55474
% 15.31/2.49  
% 15.31/2.49  ------ Preprocessing
% 15.31/2.49  
% 15.31/2.49  num_of_splits:                          8
% 15.31/2.49  num_of_split_atoms:                     8
% 15.31/2.49  num_of_reused_defs:                     0
% 15.31/2.49  num_eq_ax_congr_red:                    158
% 15.31/2.49  num_of_sem_filtered_clauses:            3
% 15.31/2.49  num_of_subtypes:                        0
% 15.31/2.49  monotx_restored_types:                  0
% 15.31/2.49  sat_num_of_epr_types:                   0
% 15.31/2.49  sat_num_of_non_cyclic_types:            0
% 15.31/2.49  sat_guarded_non_collapsed_types:        0
% 15.31/2.49  num_pure_diseq_elim:                    0
% 15.31/2.49  simp_replaced_by:                       0
% 15.31/2.49  res_preprocessed:                       963
% 15.31/2.49  prep_upred:                             0
% 15.31/2.49  prep_unflattend:                        274
% 15.31/2.49  smt_new_axioms:                         0
% 15.31/2.49  pred_elim_cands:                        18
% 15.31/2.49  pred_elim:                              5
% 15.31/2.49  pred_elim_cl:                           0
% 15.31/2.49  pred_elim_cycles:                       12
% 15.31/2.49  merged_defs:                            8
% 15.31/2.49  merged_defs_ncl:                        0
% 15.31/2.49  bin_hyper_res:                          11
% 15.31/2.49  prep_cycles:                            4
% 15.31/2.49  pred_elim_time:                         0.103
% 15.31/2.49  splitting_time:                         0.
% 15.31/2.49  sem_filter_time:                        0.
% 15.31/2.49  monotx_time:                            0.001
% 15.31/2.49  subtype_inf_time:                       0.
% 15.31/2.49  
% 15.31/2.49  ------ Problem properties
% 15.31/2.49  
% 15.31/2.49  clauses:                                226
% 15.31/2.49  conjectures:                            19
% 15.31/2.49  epr:                                    64
% 15.31/2.49  horn:                                   182
% 15.31/2.49  ground:                                 71
% 15.31/2.49  unary:                                  77
% 15.31/2.49  binary:                                 38
% 15.31/2.49  lits:                                   723
% 15.31/2.49  lits_eq:                                67
% 15.31/2.49  fd_pure:                                0
% 15.31/2.49  fd_pseudo:                              0
% 15.31/2.49  fd_cond:                                5
% 15.31/2.49  fd_pseudo_cond:                         6
% 15.31/2.49  ac_symbols:                             0
% 15.31/2.49  
% 15.31/2.49  ------ Propositional Solver
% 15.31/2.49  
% 15.31/2.49  prop_solver_calls:                      30
% 15.31/2.49  prop_fast_solver_calls:                 8880
% 15.31/2.49  smt_solver_calls:                       0
% 15.31/2.49  smt_fast_solver_calls:                  0
% 15.31/2.49  prop_num_of_clauses:                    19051
% 15.31/2.49  prop_preprocess_simplified:             57494
% 15.31/2.49  prop_fo_subsumed:                       266
% 15.31/2.49  prop_solver_time:                       0.
% 15.31/2.49  smt_solver_time:                        0.
% 15.31/2.49  smt_fast_solver_time:                   0.
% 15.31/2.49  prop_fast_solver_time:                  0.
% 15.31/2.49  prop_unsat_core_time:                   0.002
% 15.31/2.49  
% 15.31/2.49  ------ QBF
% 15.31/2.49  
% 15.31/2.49  qbf_q_res:                              0
% 15.31/2.49  qbf_num_tautologies:                    0
% 15.31/2.49  qbf_prep_cycles:                        0
% 15.31/2.49  
% 15.31/2.49  ------ BMC1
% 15.31/2.49  
% 15.31/2.49  bmc1_current_bound:                     -1
% 15.31/2.49  bmc1_last_solved_bound:                 -1
% 15.31/2.49  bmc1_unsat_core_size:                   -1
% 15.31/2.49  bmc1_unsat_core_parents_size:           -1
% 15.31/2.49  bmc1_merge_next_fun:                    0
% 15.31/2.49  bmc1_unsat_core_clauses_time:           0.
% 15.31/2.49  
% 15.31/2.49  ------ Instantiation
% 15.31/2.49  
% 15.31/2.49  inst_num_of_clauses:                    5157
% 15.31/2.49  inst_num_in_passive:                    1890
% 15.31/2.49  inst_num_in_active:                     1429
% 15.31/2.49  inst_num_in_unprocessed:                1840
% 15.31/2.49  inst_num_of_loops:                      1700
% 15.31/2.49  inst_num_of_learning_restarts:          0
% 15.31/2.49  inst_num_moves_active_passive:          271
% 15.31/2.49  inst_lit_activity:                      0
% 15.31/2.49  inst_lit_activity_moves:                1
% 15.31/2.49  inst_num_tautologies:                   0
% 15.31/2.49  inst_num_prop_implied:                  0
% 15.31/2.49  inst_num_existing_simplified:           0
% 15.31/2.49  inst_num_eq_res_simplified:             0
% 15.31/2.49  inst_num_child_elim:                    0
% 15.31/2.49  inst_num_of_dismatching_blockings:      1394
% 15.31/2.49  inst_num_of_non_proper_insts:           4784
% 15.31/2.49  inst_num_of_duplicates:                 0
% 15.31/2.49  inst_inst_num_from_inst_to_res:         0
% 15.31/2.49  inst_dismatching_checking_time:         0.
% 15.31/2.49  
% 15.31/2.49  ------ Resolution
% 15.31/2.49  
% 15.31/2.49  res_num_of_clauses:                     0
% 15.31/2.49  res_num_in_passive:                     0
% 15.31/2.49  res_num_in_active:                      0
% 15.31/2.49  res_num_of_loops:                       967
% 15.31/2.49  res_forward_subset_subsumed:            273
% 15.31/2.49  res_backward_subset_subsumed:           8
% 15.31/2.49  res_forward_subsumed:                   16
% 15.31/2.49  res_backward_subsumed:                  19
% 15.31/2.49  res_forward_subsumption_resolution:     12
% 15.31/2.49  res_backward_subsumption_resolution:    0
% 15.31/2.49  res_clause_to_clause_subsumption:       4237
% 15.31/2.49  res_orphan_elimination:                 0
% 15.31/2.49  res_tautology_del:                      225
% 15.31/2.49  res_num_eq_res_simplified:              4
% 15.31/2.49  res_num_sel_changes:                    0
% 15.31/2.49  res_moves_from_active_to_pass:          0
% 15.31/2.49  
% 15.31/2.49  ------ Superposition
% 15.31/2.49  
% 15.31/2.49  sup_time_total:                         0.
% 15.31/2.49  sup_time_generating:                    0.
% 15.31/2.49  sup_time_sim_full:                      0.
% 15.31/2.49  sup_time_sim_immed:                     0.
% 15.31/2.49  
% 15.31/2.49  sup_num_of_clauses:                     716
% 15.31/2.49  sup_num_in_active:                      287
% 15.31/2.49  sup_num_in_passive:                     429
% 15.31/2.49  sup_num_of_loops:                       339
% 15.31/2.49  sup_fw_superposition:                   561
% 15.31/2.49  sup_bw_superposition:                   287
% 15.31/2.49  sup_immediate_simplified:               239
% 15.31/2.49  sup_given_eliminated:                   1
% 15.31/2.49  comparisons_done:                       0
% 15.31/2.49  comparisons_avoided:                    1
% 15.31/2.49  
% 15.31/2.49  ------ Simplifications
% 15.31/2.49  
% 15.31/2.49  
% 15.31/2.49  sim_fw_subset_subsumed:                 112
% 15.31/2.49  sim_bw_subset_subsumed:                 11
% 15.31/2.49  sim_fw_subsumed:                        75
% 15.31/2.49  sim_bw_subsumed:                        16
% 15.31/2.49  sim_fw_subsumption_res:                 0
% 15.31/2.49  sim_bw_subsumption_res:                 0
% 15.31/2.49  sim_tautology_del:                      51
% 15.31/2.49  sim_eq_tautology_del:                   19
% 15.31/2.49  sim_eq_res_simp:                        2
% 15.31/2.49  sim_fw_demodulated:                     3
% 15.31/2.49  sim_bw_demodulated:                     42
% 15.31/2.49  sim_light_normalised:                   63
% 15.31/2.49  sim_joinable_taut:                      0
% 15.31/2.49  sim_joinable_simp:                      0
% 15.31/2.49  sim_ac_normalised:                      0
% 15.31/2.49  sim_smt_subsumption:                    0
% 15.31/2.49  
%------------------------------------------------------------------------------
