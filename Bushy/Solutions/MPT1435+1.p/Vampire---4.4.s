%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : filter_1__t30_filter_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:08 EDT 2019

% Result     : Theorem 36.37s
% Output     : Refutation 36.37s
% Verified   : 
% Statistics : Number of formulae       :  299 (1251 expanded)
%              Number of leaves         :   27 ( 249 expanded)
%              Depth                    :   36
%              Number of atoms          : 1925 (14451 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   24 (   8 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21389,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1035,f1050,f1051,f3979,f5595,f19737,f19796,f19838,f19840,f20078,f20120,f20122,f20333,f20565,f20787,f21046,f21333,f21388])).

fof(f21388,plain,
    ( spl10_1
    | ~ spl10_122
    | ~ spl10_136 ),
    inference(avatar_contradiction_clause,[],[f21387])).

fof(f21387,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_122
    | ~ spl10_136 ),
    inference(subsumption_resolution,[],[f1025,f21377])).

fof(f21377,plain,
    ( r6_binop_1(sK0,sK2,sK3)
    | ~ spl10_122
    | ~ spl10_136 ),
    inference(subsumption_resolution,[],[f21376,f21359])).

fof(f21359,plain,
    ( r5_binop_1(sK0,sK2,sK3)
    | ~ spl10_136 ),
    inference(subsumption_resolution,[],[f21358,f58])).

fof(f58,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ( r6_binop_1(X1,X4,X5)
                              & r6_binop_1(X0,X2,X3) )
                          <~> r6_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                      & v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                  & v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ( r6_binop_1(X1,X4,X5)
                              & r6_binop_1(X0,X2,X3) )
                          <~> r6_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                      & v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                  & v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                  & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                      & v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                      & v1_funct_1(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          & v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                              & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                              & v1_funct_1(X5) )
                           => ( ( r6_binop_1(X1,X4,X5)
                                & r6_binop_1(X0,X2,X3) )
                            <=> r6_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                    & v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                        & v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                            & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                            & v1_funct_1(X5) )
                         => ( ( r6_binop_1(X1,X4,X5)
                              & r6_binop_1(X0,X2,X3) )
                          <=> r6_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t30_filter_1.p',t30_filter_1)).

fof(f21358,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r5_binop_1(sK0,sK2,sK3)
    | ~ spl10_136 ),
    inference(subsumption_resolution,[],[f21357,f57])).

fof(f57,plain,(
    v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f21357,plain,
    ( ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r5_binop_1(sK0,sK2,sK3)
    | ~ spl10_136 ),
    inference(subsumption_resolution,[],[f21356,f56])).

fof(f56,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f28])).

fof(f21356,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r5_binop_1(sK0,sK2,sK3)
    | ~ spl10_136 ),
    inference(subsumption_resolution,[],[f21355,f61])).

fof(f61,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f21355,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r5_binop_1(sK0,sK2,sK3)
    | ~ spl10_136 ),
    inference(subsumption_resolution,[],[f21354,f60])).

fof(f60,plain,(
    v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f21354,plain,
    ( ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r5_binop_1(sK0,sK2,sK3)
    | ~ spl10_136 ),
    inference(subsumption_resolution,[],[f21353,f59])).

fof(f59,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f21353,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r5_binop_1(sK0,sK2,sK3)
    | ~ spl10_136 ),
    inference(subsumption_resolution,[],[f21352,f64])).

fof(f64,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f21352,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r5_binop_1(sK0,sK2,sK3)
    | ~ spl10_136 ),
    inference(subsumption_resolution,[],[f21351,f63])).

fof(f63,plain,(
    v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f21351,plain,
    ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r5_binop_1(sK0,sK2,sK3)
    | ~ spl10_136 ),
    inference(subsumption_resolution,[],[f21350,f62])).

fof(f62,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f21350,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r5_binop_1(sK0,sK2,sK3)
    | ~ spl10_136 ),
    inference(subsumption_resolution,[],[f21349,f67])).

fof(f67,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f21349,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r5_binop_1(sK0,sK2,sK3)
    | ~ spl10_136 ),
    inference(subsumption_resolution,[],[f21348,f66])).

fof(f66,plain,(
    v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f21348,plain,
    ( ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r5_binop_1(sK0,sK2,sK3)
    | ~ spl10_136 ),
    inference(subsumption_resolution,[],[f21347,f65])).

fof(f65,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f21347,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r5_binop_1(sK0,sK2,sK3)
    | ~ spl10_136 ),
    inference(subsumption_resolution,[],[f21346,f68])).

fof(f68,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f21346,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r5_binop_1(sK0,sK2,sK3)
    | ~ spl10_136 ),
    inference(subsumption_resolution,[],[f21164,f69])).

fof(f69,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f21164,plain,
    ( v1_xboole_0(sK0)
    | v1_xboole_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r5_binop_1(sK0,sK2,sK3)
    | ~ spl10_136 ),
    inference(resolution,[],[f20564,f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ r5_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5))
      | r5_binop_1(X0,X2,X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r5_binop_1(X1,X4,X5)
                              & r5_binop_1(X0,X2,X3) )
                          <=> r5_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                      | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r5_binop_1(X1,X4,X5)
                              & r5_binop_1(X0,X2,X3) )
                          <=> r5_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                      | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                    & v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                        & v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                            & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                            & v1_funct_1(X5) )
                         => ( ( r5_binop_1(X1,X4,X5)
                              & r5_binop_1(X0,X2,X3) )
                          <=> r5_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t30_filter_1.p',t29_filter_1)).

fof(f20564,plain,
    ( r5_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ spl10_136 ),
    inference(avatar_component_clause,[],[f20563])).

fof(f20563,plain,
    ( spl10_136
  <=> r5_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_136])])).

fof(f21376,plain,
    ( ~ r5_binop_1(sK0,sK2,sK3)
    | r6_binop_1(sK0,sK2,sK3)
    | ~ spl10_122 ),
    inference(subsumption_resolution,[],[f21375,f21373])).

fof(f21373,plain,
    ( r4_binop_1(sK0,sK2,sK3)
    | ~ spl10_122 ),
    inference(subsumption_resolution,[],[f21372,f58])).

fof(f21372,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r4_binop_1(sK0,sK2,sK3)
    | ~ spl10_122 ),
    inference(subsumption_resolution,[],[f21371,f57])).

fof(f21371,plain,
    ( ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r4_binop_1(sK0,sK2,sK3)
    | ~ spl10_122 ),
    inference(subsumption_resolution,[],[f21370,f56])).

fof(f21370,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r4_binop_1(sK0,sK2,sK3)
    | ~ spl10_122 ),
    inference(subsumption_resolution,[],[f21369,f61])).

fof(f21369,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r4_binop_1(sK0,sK2,sK3)
    | ~ spl10_122 ),
    inference(subsumption_resolution,[],[f21368,f60])).

fof(f21368,plain,
    ( ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r4_binop_1(sK0,sK2,sK3)
    | ~ spl10_122 ),
    inference(subsumption_resolution,[],[f21367,f59])).

fof(f21367,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r4_binop_1(sK0,sK2,sK3)
    | ~ spl10_122 ),
    inference(subsumption_resolution,[],[f21366,f64])).

fof(f21366,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r4_binop_1(sK0,sK2,sK3)
    | ~ spl10_122 ),
    inference(subsumption_resolution,[],[f21365,f63])).

fof(f21365,plain,
    ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r4_binop_1(sK0,sK2,sK3)
    | ~ spl10_122 ),
    inference(subsumption_resolution,[],[f21364,f62])).

fof(f21364,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r4_binop_1(sK0,sK2,sK3)
    | ~ spl10_122 ),
    inference(subsumption_resolution,[],[f21363,f67])).

fof(f21363,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r4_binop_1(sK0,sK2,sK3)
    | ~ spl10_122 ),
    inference(subsumption_resolution,[],[f21362,f66])).

fof(f21362,plain,
    ( ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r4_binop_1(sK0,sK2,sK3)
    | ~ spl10_122 ),
    inference(subsumption_resolution,[],[f21361,f65])).

fof(f21361,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r4_binop_1(sK0,sK2,sK3)
    | ~ spl10_122 ),
    inference(subsumption_resolution,[],[f21360,f68])).

fof(f21360,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r4_binop_1(sK0,sK2,sK3)
    | ~ spl10_122 ),
    inference(subsumption_resolution,[],[f21116,f69])).

fof(f21116,plain,
    ( v1_xboole_0(sK0)
    | v1_xboole_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r4_binop_1(sK0,sK2,sK3)
    | ~ spl10_122 ),
    inference(resolution,[],[f19700,f72])).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ r4_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5))
      | r4_binop_1(X0,X2,X3) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r4_binop_1(X1,X4,X5)
                              & r4_binop_1(X0,X2,X3) )
                          <=> r4_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                      | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r4_binop_1(X1,X4,X5)
                              & r4_binop_1(X0,X2,X3) )
                          <=> r4_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                      | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                    & v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                        & v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                            & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                            & v1_funct_1(X5) )
                         => ( ( r4_binop_1(X1,X4,X5)
                              & r4_binop_1(X0,X2,X3) )
                          <=> r4_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t30_filter_1.p',t28_filter_1)).

fof(f19700,plain,
    ( r4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ spl10_122 ),
    inference(avatar_component_clause,[],[f19699])).

fof(f19699,plain,
    ( spl10_122
  <=> r4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_122])])).

fof(f21375,plain,
    ( ~ r4_binop_1(sK0,sK2,sK3)
    | ~ r5_binop_1(sK0,sK2,sK3)
    | r6_binop_1(sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f21374,f65])).

fof(f21374,plain,
    ( ~ v1_funct_1(sK2)
    | ~ r4_binop_1(sK0,sK2,sK3)
    | ~ r5_binop_1(sK0,sK2,sK3)
    | r6_binop_1(sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f2027,f66])).

fof(f2027,plain,
    ( ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | ~ r4_binop_1(sK0,sK2,sK3)
    | ~ r5_binop_1(sK0,sK2,sK3)
    | r6_binop_1(sK0,sK2,sK3) ),
    inference(resolution,[],[f699,f67])).

fof(f699,plain,(
    ! [X100] :
      ( ~ m1_subset_1(X100,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_2(X100,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(X100)
      | ~ r4_binop_1(sK0,X100,sK3)
      | ~ r5_binop_1(sK0,X100,sK3)
      | r6_binop_1(sK0,X100,sK3) ) ),
    inference(subsumption_resolution,[],[f698,f64])).

fof(f698,plain,(
    ! [X100] :
      ( ~ v1_funct_1(X100)
      | ~ v1_funct_2(X100,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ m1_subset_1(X100,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ r4_binop_1(sK0,X100,sK3)
      | ~ r5_binop_1(sK0,X100,sK3)
      | r6_binop_1(sK0,X100,sK3) ) ),
    inference(subsumption_resolution,[],[f608,f62])).

fof(f608,plain,(
    ! [X100] :
      ( ~ v1_funct_1(X100)
      | ~ v1_funct_2(X100,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ m1_subset_1(X100,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ r4_binop_1(sK0,X100,sK3)
      | ~ r5_binop_1(sK0,X100,sK3)
      | r6_binop_1(sK0,X100,sK3) ) ),
    inference(resolution,[],[f63,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ r4_binop_1(X0,X1,X2)
      | ~ r5_binop_1(X0,X1,X2)
      | r6_binop_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r6_binop_1(X0,X1,X2)
          <=> ( r5_binop_1(X0,X1,X2)
              & r4_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r6_binop_1(X0,X1,X2)
          <=> ( r5_binop_1(X0,X1,X2)
              & r4_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        & v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
         => ( r6_binop_1(X0,X1,X2)
          <=> ( r5_binop_1(X0,X1,X2)
              & r4_binop_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t30_filter_1.p',d11_binop_1)).

fof(f1025,plain,
    ( ~ r6_binop_1(sK0,sK2,sK3)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f1024])).

fof(f1024,plain,
    ( spl10_1
  <=> ~ r6_binop_1(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f21333,plain,
    ( spl10_85
    | ~ spl10_136 ),
    inference(avatar_contradiction_clause,[],[f21332])).

fof(f21332,plain,
    ( $false
    | ~ spl10_85
    | ~ spl10_136 ),
    inference(subsumption_resolution,[],[f21331,f3978])).

fof(f3978,plain,
    ( ~ r5_binop_1(sK1,sK4,sK5)
    | ~ spl10_85 ),
    inference(avatar_component_clause,[],[f3977])).

fof(f3977,plain,
    ( spl10_85
  <=> ~ r5_binop_1(sK1,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_85])])).

fof(f21331,plain,
    ( r5_binop_1(sK1,sK4,sK5)
    | ~ spl10_136 ),
    inference(subsumption_resolution,[],[f21330,f58])).

fof(f21330,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r5_binop_1(sK1,sK4,sK5)
    | ~ spl10_136 ),
    inference(subsumption_resolution,[],[f21329,f57])).

fof(f21329,plain,
    ( ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r5_binop_1(sK1,sK4,sK5)
    | ~ spl10_136 ),
    inference(subsumption_resolution,[],[f21328,f56])).

fof(f21328,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r5_binop_1(sK1,sK4,sK5)
    | ~ spl10_136 ),
    inference(subsumption_resolution,[],[f21327,f61])).

fof(f21327,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r5_binop_1(sK1,sK4,sK5)
    | ~ spl10_136 ),
    inference(subsumption_resolution,[],[f21326,f60])).

fof(f21326,plain,
    ( ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r5_binop_1(sK1,sK4,sK5)
    | ~ spl10_136 ),
    inference(subsumption_resolution,[],[f21325,f59])).

fof(f21325,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r5_binop_1(sK1,sK4,sK5)
    | ~ spl10_136 ),
    inference(subsumption_resolution,[],[f21324,f64])).

fof(f21324,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r5_binop_1(sK1,sK4,sK5)
    | ~ spl10_136 ),
    inference(subsumption_resolution,[],[f21323,f63])).

fof(f21323,plain,
    ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r5_binop_1(sK1,sK4,sK5)
    | ~ spl10_136 ),
    inference(subsumption_resolution,[],[f21322,f62])).

fof(f21322,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r5_binop_1(sK1,sK4,sK5)
    | ~ spl10_136 ),
    inference(subsumption_resolution,[],[f21321,f67])).

fof(f21321,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r5_binop_1(sK1,sK4,sK5)
    | ~ spl10_136 ),
    inference(subsumption_resolution,[],[f21320,f66])).

fof(f21320,plain,
    ( ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r5_binop_1(sK1,sK4,sK5)
    | ~ spl10_136 ),
    inference(subsumption_resolution,[],[f21319,f65])).

fof(f21319,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r5_binop_1(sK1,sK4,sK5)
    | ~ spl10_136 ),
    inference(subsumption_resolution,[],[f21318,f68])).

fof(f21318,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r5_binop_1(sK1,sK4,sK5)
    | ~ spl10_136 ),
    inference(subsumption_resolution,[],[f21165,f69])).

fof(f21165,plain,
    ( v1_xboole_0(sK0)
    | v1_xboole_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r5_binop_1(sK1,sK4,sK5)
    | ~ spl10_136 ),
    inference(resolution,[],[f20564,f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ r5_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5))
      | r5_binop_1(X1,X4,X5) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f21046,plain,
    ( ~ spl10_0
    | ~ spl10_4
    | spl10_123 ),
    inference(avatar_contradiction_clause,[],[f21045])).

fof(f21045,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_4
    | ~ spl10_123 ),
    inference(subsumption_resolution,[],[f21044,f20805])).

fof(f20805,plain,
    ( r4_binop_1(sK1,sK4,sK5)
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f20804,f58])).

fof(f20804,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r4_binop_1(sK1,sK4,sK5)
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f20803,f57])).

fof(f20803,plain,
    ( ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r4_binop_1(sK1,sK4,sK5)
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f20802,f56])).

fof(f20802,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r4_binop_1(sK1,sK4,sK5)
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f20801,f61])).

fof(f20801,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r4_binop_1(sK1,sK4,sK5)
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f20800,f60])).

fof(f20800,plain,
    ( ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r4_binop_1(sK1,sK4,sK5)
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f20582,f59])).

fof(f20582,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r4_binop_1(sK1,sK4,sK5)
    | ~ spl10_4 ),
    inference(resolution,[],[f1049,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | r4_binop_1(X0,X1,X2)
      | ~ r6_binop_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f1049,plain,
    ( r6_binop_1(sK1,sK4,sK5)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f1048])).

fof(f1048,plain,
    ( spl10_4
  <=> r6_binop_1(sK1,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f21044,plain,
    ( ~ r4_binop_1(sK1,sK4,sK5)
    | ~ spl10_0
    | ~ spl10_123 ),
    inference(subsumption_resolution,[],[f21043,f20811])).

fof(f20811,plain,
    ( r4_binop_1(sK0,sK2,sK3)
    | ~ spl10_0 ),
    inference(subsumption_resolution,[],[f20810,f64])).

fof(f20810,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | r4_binop_1(sK0,sK2,sK3)
    | ~ spl10_0 ),
    inference(subsumption_resolution,[],[f20809,f63])).

fof(f20809,plain,
    ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | r4_binop_1(sK0,sK2,sK3)
    | ~ spl10_0 ),
    inference(subsumption_resolution,[],[f20808,f62])).

fof(f20808,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | r4_binop_1(sK0,sK2,sK3)
    | ~ spl10_0 ),
    inference(subsumption_resolution,[],[f20807,f67])).

fof(f20807,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | r4_binop_1(sK0,sK2,sK3)
    | ~ spl10_0 ),
    inference(subsumption_resolution,[],[f20806,f66])).

fof(f20806,plain,
    ( ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | r4_binop_1(sK0,sK2,sK3)
    | ~ spl10_0 ),
    inference(subsumption_resolution,[],[f20580,f65])).

fof(f20580,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | r4_binop_1(sK0,sK2,sK3)
    | ~ spl10_0 ),
    inference(resolution,[],[f1028,f85])).

fof(f1028,plain,
    ( r6_binop_1(sK0,sK2,sK3)
    | ~ spl10_0 ),
    inference(avatar_component_clause,[],[f1027])).

fof(f1027,plain,
    ( spl10_0
  <=> r6_binop_1(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_0])])).

fof(f21043,plain,
    ( ~ r4_binop_1(sK0,sK2,sK3)
    | ~ r4_binop_1(sK1,sK4,sK5)
    | ~ spl10_123 ),
    inference(subsumption_resolution,[],[f21042,f58])).

fof(f21042,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ r4_binop_1(sK0,sK2,sK3)
    | ~ r4_binop_1(sK1,sK4,sK5)
    | ~ spl10_123 ),
    inference(subsumption_resolution,[],[f21041,f57])).

fof(f21041,plain,
    ( ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ r4_binop_1(sK0,sK2,sK3)
    | ~ r4_binop_1(sK1,sK4,sK5)
    | ~ spl10_123 ),
    inference(subsumption_resolution,[],[f21040,f56])).

fof(f21040,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ r4_binop_1(sK0,sK2,sK3)
    | ~ r4_binop_1(sK1,sK4,sK5)
    | ~ spl10_123 ),
    inference(subsumption_resolution,[],[f21039,f61])).

fof(f21039,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ r4_binop_1(sK0,sK2,sK3)
    | ~ r4_binop_1(sK1,sK4,sK5)
    | ~ spl10_123 ),
    inference(subsumption_resolution,[],[f21038,f60])).

fof(f21038,plain,
    ( ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ r4_binop_1(sK0,sK2,sK3)
    | ~ r4_binop_1(sK1,sK4,sK5)
    | ~ spl10_123 ),
    inference(subsumption_resolution,[],[f21037,f59])).

fof(f21037,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ r4_binop_1(sK0,sK2,sK3)
    | ~ r4_binop_1(sK1,sK4,sK5)
    | ~ spl10_123 ),
    inference(subsumption_resolution,[],[f21036,f64])).

fof(f21036,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ r4_binop_1(sK0,sK2,sK3)
    | ~ r4_binop_1(sK1,sK4,sK5)
    | ~ spl10_123 ),
    inference(subsumption_resolution,[],[f21035,f63])).

fof(f21035,plain,
    ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ r4_binop_1(sK0,sK2,sK3)
    | ~ r4_binop_1(sK1,sK4,sK5)
    | ~ spl10_123 ),
    inference(subsumption_resolution,[],[f21034,f62])).

fof(f21034,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ r4_binop_1(sK0,sK2,sK3)
    | ~ r4_binop_1(sK1,sK4,sK5)
    | ~ spl10_123 ),
    inference(subsumption_resolution,[],[f21033,f67])).

fof(f21033,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ r4_binop_1(sK0,sK2,sK3)
    | ~ r4_binop_1(sK1,sK4,sK5)
    | ~ spl10_123 ),
    inference(subsumption_resolution,[],[f21032,f66])).

fof(f21032,plain,
    ( ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ r4_binop_1(sK0,sK2,sK3)
    | ~ r4_binop_1(sK1,sK4,sK5)
    | ~ spl10_123 ),
    inference(subsumption_resolution,[],[f21031,f65])).

fof(f21031,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ r4_binop_1(sK0,sK2,sK3)
    | ~ r4_binop_1(sK1,sK4,sK5)
    | ~ spl10_123 ),
    inference(subsumption_resolution,[],[f21030,f68])).

fof(f21030,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ r4_binop_1(sK0,sK2,sK3)
    | ~ r4_binop_1(sK1,sK4,sK5)
    | ~ spl10_123 ),
    inference(subsumption_resolution,[],[f20867,f69])).

fof(f20867,plain,
    ( v1_xboole_0(sK0)
    | v1_xboole_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ r4_binop_1(sK0,sK2,sK3)
    | ~ r4_binop_1(sK1,sK4,sK5)
    | ~ spl10_123 ),
    inference(resolution,[],[f19697,f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | r4_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5))
      | ~ r4_binop_1(X0,X2,X3)
      | ~ r4_binop_1(X1,X4,X5) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f19697,plain,
    ( ~ r4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ spl10_123 ),
    inference(avatar_component_clause,[],[f19696])).

fof(f19696,plain,
    ( spl10_123
  <=> ~ r4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_123])])).

fof(f20787,plain,
    ( ~ spl10_0
    | spl10_3
    | ~ spl10_84
    | ~ spl10_122
    | ~ spl10_124
    | ~ spl10_126
    | ~ spl10_130
    | ~ spl10_132 ),
    inference(avatar_contradiction_clause,[],[f20786])).

fof(f20786,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_84
    | ~ spl10_122
    | ~ spl10_124
    | ~ spl10_126
    | ~ spl10_130
    | ~ spl10_132 ),
    inference(subsumption_resolution,[],[f20785,f3975])).

fof(f3975,plain,
    ( r5_binop_1(sK1,sK4,sK5)
    | ~ spl10_84 ),
    inference(avatar_component_clause,[],[f3974])).

fof(f3974,plain,
    ( spl10_84
  <=> r5_binop_1(sK1,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_84])])).

fof(f20785,plain,
    ( ~ r5_binop_1(sK1,sK4,sK5)
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_122
    | ~ spl10_124
    | ~ spl10_126
    | ~ spl10_130
    | ~ spl10_132 ),
    inference(subsumption_resolution,[],[f20784,f20579])).

fof(f20579,plain,
    ( r5_binop_1(sK0,sK2,sK3)
    | ~ spl10_0 ),
    inference(subsumption_resolution,[],[f20578,f1028])).

fof(f20578,plain,
    ( r5_binop_1(sK0,sK2,sK3)
    | ~ r6_binop_1(sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f20577,f65])).

fof(f20577,plain,
    ( ~ v1_funct_1(sK2)
    | r5_binop_1(sK0,sK2,sK3)
    | ~ r6_binop_1(sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f1727,f66])).

fof(f1727,plain,
    ( ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | r5_binop_1(sK0,sK2,sK3)
    | ~ r6_binop_1(sK0,sK2,sK3) ),
    inference(resolution,[],[f695,f67])).

fof(f695,plain,(
    ! [X98] :
      ( ~ m1_subset_1(X98,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_2(X98,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(X98)
      | r5_binop_1(sK0,X98,sK3)
      | ~ r6_binop_1(sK0,X98,sK3) ) ),
    inference(subsumption_resolution,[],[f694,f64])).

fof(f694,plain,(
    ! [X98] :
      ( ~ v1_funct_1(X98)
      | ~ v1_funct_2(X98,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ m1_subset_1(X98,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | r5_binop_1(sK0,X98,sK3)
      | ~ r6_binop_1(sK0,X98,sK3) ) ),
    inference(subsumption_resolution,[],[f606,f62])).

fof(f606,plain,(
    ! [X98] :
      ( ~ v1_funct_1(X98)
      | ~ v1_funct_2(X98,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ m1_subset_1(X98,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | r5_binop_1(sK0,X98,sK3)
      | ~ r6_binop_1(sK0,X98,sK3) ) ),
    inference(resolution,[],[f63,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | r5_binop_1(X0,X1,X2)
      | ~ r6_binop_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f20784,plain,
    ( ~ r5_binop_1(sK0,sK2,sK3)
    | ~ r5_binop_1(sK1,sK4,sK5)
    | ~ spl10_3
    | ~ spl10_122
    | ~ spl10_124
    | ~ spl10_126
    | ~ spl10_130
    | ~ spl10_132 ),
    inference(subsumption_resolution,[],[f20783,f58])).

fof(f20783,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ r5_binop_1(sK0,sK2,sK3)
    | ~ r5_binop_1(sK1,sK4,sK5)
    | ~ spl10_3
    | ~ spl10_122
    | ~ spl10_124
    | ~ spl10_126
    | ~ spl10_130
    | ~ spl10_132 ),
    inference(subsumption_resolution,[],[f20782,f57])).

fof(f20782,plain,
    ( ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ r5_binop_1(sK0,sK2,sK3)
    | ~ r5_binop_1(sK1,sK4,sK5)
    | ~ spl10_3
    | ~ spl10_122
    | ~ spl10_124
    | ~ spl10_126
    | ~ spl10_130
    | ~ spl10_132 ),
    inference(subsumption_resolution,[],[f20781,f56])).

fof(f20781,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ r5_binop_1(sK0,sK2,sK3)
    | ~ r5_binop_1(sK1,sK4,sK5)
    | ~ spl10_3
    | ~ spl10_122
    | ~ spl10_124
    | ~ spl10_126
    | ~ spl10_130
    | ~ spl10_132 ),
    inference(subsumption_resolution,[],[f20780,f61])).

fof(f20780,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ r5_binop_1(sK0,sK2,sK3)
    | ~ r5_binop_1(sK1,sK4,sK5)
    | ~ spl10_3
    | ~ spl10_122
    | ~ spl10_124
    | ~ spl10_126
    | ~ spl10_130
    | ~ spl10_132 ),
    inference(subsumption_resolution,[],[f20779,f60])).

fof(f20779,plain,
    ( ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ r5_binop_1(sK0,sK2,sK3)
    | ~ r5_binop_1(sK1,sK4,sK5)
    | ~ spl10_3
    | ~ spl10_122
    | ~ spl10_124
    | ~ spl10_126
    | ~ spl10_130
    | ~ spl10_132 ),
    inference(subsumption_resolution,[],[f20778,f59])).

fof(f20778,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ r5_binop_1(sK0,sK2,sK3)
    | ~ r5_binop_1(sK1,sK4,sK5)
    | ~ spl10_3
    | ~ spl10_122
    | ~ spl10_124
    | ~ spl10_126
    | ~ spl10_130
    | ~ spl10_132 ),
    inference(subsumption_resolution,[],[f20777,f64])).

fof(f20777,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ r5_binop_1(sK0,sK2,sK3)
    | ~ r5_binop_1(sK1,sK4,sK5)
    | ~ spl10_3
    | ~ spl10_122
    | ~ spl10_124
    | ~ spl10_126
    | ~ spl10_130
    | ~ spl10_132 ),
    inference(subsumption_resolution,[],[f20776,f63])).

fof(f20776,plain,
    ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ r5_binop_1(sK0,sK2,sK3)
    | ~ r5_binop_1(sK1,sK4,sK5)
    | ~ spl10_3
    | ~ spl10_122
    | ~ spl10_124
    | ~ spl10_126
    | ~ spl10_130
    | ~ spl10_132 ),
    inference(subsumption_resolution,[],[f20775,f62])).

fof(f20775,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ r5_binop_1(sK0,sK2,sK3)
    | ~ r5_binop_1(sK1,sK4,sK5)
    | ~ spl10_3
    | ~ spl10_122
    | ~ spl10_124
    | ~ spl10_126
    | ~ spl10_130
    | ~ spl10_132 ),
    inference(subsumption_resolution,[],[f20774,f67])).

fof(f20774,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ r5_binop_1(sK0,sK2,sK3)
    | ~ r5_binop_1(sK1,sK4,sK5)
    | ~ spl10_3
    | ~ spl10_122
    | ~ spl10_124
    | ~ spl10_126
    | ~ spl10_130
    | ~ spl10_132 ),
    inference(subsumption_resolution,[],[f20773,f66])).

fof(f20773,plain,
    ( ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ r5_binop_1(sK0,sK2,sK3)
    | ~ r5_binop_1(sK1,sK4,sK5)
    | ~ spl10_3
    | ~ spl10_122
    | ~ spl10_124
    | ~ spl10_126
    | ~ spl10_130
    | ~ spl10_132 ),
    inference(subsumption_resolution,[],[f20772,f65])).

fof(f20772,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ r5_binop_1(sK0,sK2,sK3)
    | ~ r5_binop_1(sK1,sK4,sK5)
    | ~ spl10_3
    | ~ spl10_122
    | ~ spl10_124
    | ~ spl10_126
    | ~ spl10_130
    | ~ spl10_132 ),
    inference(subsumption_resolution,[],[f20771,f68])).

fof(f20771,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ r5_binop_1(sK0,sK2,sK3)
    | ~ r5_binop_1(sK1,sK4,sK5)
    | ~ spl10_3
    | ~ spl10_122
    | ~ spl10_124
    | ~ spl10_126
    | ~ spl10_130
    | ~ spl10_132 ),
    inference(subsumption_resolution,[],[f20619,f69])).

fof(f20619,plain,
    ( v1_xboole_0(sK0)
    | v1_xboole_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ r5_binop_1(sK0,sK2,sK3)
    | ~ r5_binop_1(sK1,sK4,sK5)
    | ~ spl10_3
    | ~ spl10_122
    | ~ spl10_124
    | ~ spl10_126
    | ~ spl10_130
    | ~ spl10_132 ),
    inference(resolution,[],[f20591,f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | r5_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5))
      | ~ r5_binop_1(X0,X2,X3)
      | ~ r5_binop_1(X1,X4,X5) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f20591,plain,
    ( ~ r5_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ spl10_3
    | ~ spl10_122
    | ~ spl10_124
    | ~ spl10_126
    | ~ spl10_130
    | ~ spl10_132 ),
    inference(subsumption_resolution,[],[f20590,f19700])).

fof(f20590,plain,
    ( ~ r4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ r5_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ spl10_3
    | ~ spl10_124
    | ~ spl10_126
    | ~ spl10_130
    | ~ spl10_132 ),
    inference(subsumption_resolution,[],[f20589,f19703])).

fof(f19703,plain,
    ( m1_subset_1(k6_filter_1(sK0,sK1,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ spl10_124 ),
    inference(avatar_component_clause,[],[f19702])).

fof(f19702,plain,
    ( spl10_124
  <=> m1_subset_1(k6_filter_1(sK0,sK1,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_124])])).

fof(f20589,plain,
    ( ~ m1_subset_1(k6_filter_1(sK0,sK1,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ r4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ r5_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ spl10_3
    | ~ spl10_126
    | ~ spl10_130
    | ~ spl10_132 ),
    inference(subsumption_resolution,[],[f20588,f19709])).

fof(f19709,plain,
    ( v1_funct_2(k6_filter_1(sK0,sK1,sK3,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ spl10_126 ),
    inference(avatar_component_clause,[],[f19708])).

fof(f19708,plain,
    ( spl10_126
  <=> v1_funct_2(k6_filter_1(sK0,sK1,sK3,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_126])])).

fof(f20588,plain,
    ( ~ v1_funct_2(k6_filter_1(sK0,sK1,sK3,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ m1_subset_1(k6_filter_1(sK0,sK1,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ r4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ r5_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ spl10_3
    | ~ spl10_130
    | ~ spl10_132 ),
    inference(subsumption_resolution,[],[f20587,f1446])).

fof(f1446,plain,(
    v1_funct_1(k6_filter_1(sK0,sK1,sK3,sK5)) ),
    inference(subsumption_resolution,[],[f1445,f62])).

fof(f1445,plain,
    ( ~ v1_funct_1(sK3)
    | v1_funct_1(k6_filter_1(sK0,sK1,sK3,sK5)) ),
    inference(subsumption_resolution,[],[f1437,f63])).

fof(f1437,plain,
    ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | v1_funct_1(k6_filter_1(sK0,sK1,sK3,sK5)) ),
    inference(resolution,[],[f429,f64])).

fof(f429,plain,(
    ! [X105,X104] :
      ( ~ m1_subset_1(X104,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X105,X105),X105)))
      | ~ v1_funct_2(X104,k2_zfmisc_1(X105,X105),X105)
      | ~ v1_funct_1(X104)
      | v1_funct_1(k6_filter_1(X105,sK1,X104,sK5)) ) ),
    inference(subsumption_resolution,[],[f428,f58])).

fof(f428,plain,(
    ! [X105,X104] :
      ( ~ v1_funct_1(X104)
      | ~ v1_funct_2(X104,k2_zfmisc_1(X105,X105),X105)
      | ~ m1_subset_1(X104,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X105,X105),X105)))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
      | v1_funct_1(k6_filter_1(X105,sK1,X104,sK5)) ) ),
    inference(subsumption_resolution,[],[f335,f56])).

fof(f335,plain,(
    ! [X105,X104] :
      ( ~ v1_funct_1(X104)
      | ~ v1_funct_2(X104,k2_zfmisc_1(X105,X105),X105)
      | ~ m1_subset_1(X104,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X105,X105),X105)))
      | ~ v1_funct_1(sK5)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
      | v1_funct_1(k6_filter_1(X105,sK1,X104,sK5)) ) ),
    inference(resolution,[],[f57,f93])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | v1_funct_1(k6_filter_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k6_filter_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))))
        & v1_funct_2(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))
        & v1_funct_1(k6_filter_1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k6_filter_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))))
        & v1_funct_2(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))
        & v1_funct_1(k6_filter_1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
        & v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k6_filter_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))))
        & v1_funct_2(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))
        & v1_funct_1(k6_filter_1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t30_filter_1.p',dt_k6_filter_1)).

fof(f20587,plain,
    ( ~ v1_funct_1(k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ v1_funct_2(k6_filter_1(sK0,sK1,sK3,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ m1_subset_1(k6_filter_1(sK0,sK1,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ r4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ r5_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ spl10_3
    | ~ spl10_130
    | ~ spl10_132 ),
    inference(subsumption_resolution,[],[f20586,f19721])).

fof(f19721,plain,
    ( m1_subset_1(k6_filter_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ spl10_130 ),
    inference(avatar_component_clause,[],[f19720])).

fof(f19720,plain,
    ( spl10_130
  <=> m1_subset_1(k6_filter_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_130])])).

fof(f20586,plain,
    ( ~ m1_subset_1(k6_filter_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ v1_funct_1(k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ v1_funct_2(k6_filter_1(sK0,sK1,sK3,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ m1_subset_1(k6_filter_1(sK0,sK1,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ r4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ r5_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ spl10_3
    | ~ spl10_132 ),
    inference(subsumption_resolution,[],[f20585,f19727])).

fof(f19727,plain,
    ( v1_funct_2(k6_filter_1(sK0,sK1,sK2,sK4),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ spl10_132 ),
    inference(avatar_component_clause,[],[f19726])).

fof(f19726,plain,
    ( spl10_132
  <=> v1_funct_2(k6_filter_1(sK0,sK1,sK2,sK4),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_132])])).

fof(f20585,plain,
    ( ~ v1_funct_2(k6_filter_1(sK0,sK1,sK2,sK4),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ m1_subset_1(k6_filter_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ v1_funct_1(k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ v1_funct_2(k6_filter_1(sK0,sK1,sK3,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ m1_subset_1(k6_filter_1(sK0,sK1,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ r4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ r5_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f20584,f1478])).

fof(f1478,plain,(
    v1_funct_1(k6_filter_1(sK0,sK1,sK2,sK4)) ),
    inference(subsumption_resolution,[],[f1477,f65])).

fof(f1477,plain,
    ( ~ v1_funct_1(sK2)
    | v1_funct_1(k6_filter_1(sK0,sK1,sK2,sK4)) ),
    inference(subsumption_resolution,[],[f1470,f66])).

fof(f1470,plain,
    ( ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | v1_funct_1(k6_filter_1(sK0,sK1,sK2,sK4)) ),
    inference(resolution,[],[f567,f67])).

fof(f567,plain,(
    ! [X105,X104] :
      ( ~ m1_subset_1(X104,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X105,X105),X105)))
      | ~ v1_funct_2(X104,k2_zfmisc_1(X105,X105),X105)
      | ~ v1_funct_1(X104)
      | v1_funct_1(k6_filter_1(X105,sK1,X104,sK4)) ) ),
    inference(subsumption_resolution,[],[f566,f61])).

fof(f566,plain,(
    ! [X105,X104] :
      ( ~ v1_funct_1(X104)
      | ~ v1_funct_2(X104,k2_zfmisc_1(X105,X105),X105)
      | ~ m1_subset_1(X104,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X105,X105),X105)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
      | v1_funct_1(k6_filter_1(X105,sK1,X104,sK4)) ) ),
    inference(subsumption_resolution,[],[f473,f59])).

fof(f473,plain,(
    ! [X105,X104] :
      ( ~ v1_funct_1(X104)
      | ~ v1_funct_2(X104,k2_zfmisc_1(X105,X105),X105)
      | ~ m1_subset_1(X104,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X105,X105),X105)))
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
      | v1_funct_1(k6_filter_1(X105,sK1,X104,sK4)) ) ),
    inference(resolution,[],[f60,f93])).

fof(f20584,plain,
    ( ~ v1_funct_1(k6_filter_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k6_filter_1(sK0,sK1,sK2,sK4),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ m1_subset_1(k6_filter_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ v1_funct_1(k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ v1_funct_2(k6_filter_1(sK0,sK1,sK3,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ m1_subset_1(k6_filter_1(sK0,sK1,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ r4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ r5_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ spl10_3 ),
    inference(resolution,[],[f1031,f87])).

fof(f1031,plain,
    ( ~ r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f1030])).

fof(f1030,plain,
    ( spl10_3
  <=> ~ r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f20565,plain,
    ( spl10_136
    | ~ spl10_125
    | ~ spl10_127
    | ~ spl10_129
    | ~ spl10_131
    | ~ spl10_133
    | ~ spl10_135
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f1043,f1033,f19735,f19729,f19723,f19717,f19711,f19705,f20563])).

fof(f19705,plain,
    ( spl10_125
  <=> ~ m1_subset_1(k6_filter_1(sK0,sK1,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_125])])).

fof(f19711,plain,
    ( spl10_127
  <=> ~ v1_funct_2(k6_filter_1(sK0,sK1,sK3,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_127])])).

fof(f19717,plain,
    ( spl10_129
  <=> ~ v1_funct_1(k6_filter_1(sK0,sK1,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_129])])).

fof(f19723,plain,
    ( spl10_131
  <=> ~ m1_subset_1(k6_filter_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_131])])).

fof(f19729,plain,
    ( spl10_133
  <=> ~ v1_funct_2(k6_filter_1(sK0,sK1,sK2,sK4),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_133])])).

fof(f19735,plain,
    ( spl10_135
  <=> ~ v1_funct_1(k6_filter_1(sK0,sK1,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_135])])).

fof(f1033,plain,
    ( spl10_2
  <=> r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f1043,plain,
    ( ~ v1_funct_1(k6_filter_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k6_filter_1(sK0,sK1,sK2,sK4),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ m1_subset_1(k6_filter_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ v1_funct_1(k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ v1_funct_2(k6_filter_1(sK0,sK1,sK3,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ m1_subset_1(k6_filter_1(sK0,sK1,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | r5_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ spl10_2 ),
    inference(resolution,[],[f1034,f86])).

fof(f1034,plain,
    ( r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f1033])).

fof(f20333,plain,
    ( spl10_83
    | ~ spl10_122 ),
    inference(avatar_contradiction_clause,[],[f20332])).

fof(f20332,plain,
    ( $false
    | ~ spl10_83
    | ~ spl10_122 ),
    inference(subsumption_resolution,[],[f20331,f3961])).

fof(f3961,plain,
    ( ~ r4_binop_1(sK1,sK4,sK5)
    | ~ spl10_83 ),
    inference(avatar_component_clause,[],[f3960])).

fof(f3960,plain,
    ( spl10_83
  <=> ~ r4_binop_1(sK1,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_83])])).

fof(f20331,plain,
    ( r4_binop_1(sK1,sK4,sK5)
    | ~ spl10_122 ),
    inference(subsumption_resolution,[],[f20330,f58])).

fof(f20330,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r4_binop_1(sK1,sK4,sK5)
    | ~ spl10_122 ),
    inference(subsumption_resolution,[],[f20329,f57])).

fof(f20329,plain,
    ( ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r4_binop_1(sK1,sK4,sK5)
    | ~ spl10_122 ),
    inference(subsumption_resolution,[],[f20328,f56])).

fof(f20328,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r4_binop_1(sK1,sK4,sK5)
    | ~ spl10_122 ),
    inference(subsumption_resolution,[],[f20327,f61])).

fof(f20327,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r4_binop_1(sK1,sK4,sK5)
    | ~ spl10_122 ),
    inference(subsumption_resolution,[],[f20326,f60])).

fof(f20326,plain,
    ( ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r4_binop_1(sK1,sK4,sK5)
    | ~ spl10_122 ),
    inference(subsumption_resolution,[],[f20325,f59])).

fof(f20325,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r4_binop_1(sK1,sK4,sK5)
    | ~ spl10_122 ),
    inference(subsumption_resolution,[],[f20324,f64])).

fof(f20324,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r4_binop_1(sK1,sK4,sK5)
    | ~ spl10_122 ),
    inference(subsumption_resolution,[],[f20323,f63])).

fof(f20323,plain,
    ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r4_binop_1(sK1,sK4,sK5)
    | ~ spl10_122 ),
    inference(subsumption_resolution,[],[f20322,f62])).

fof(f20322,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r4_binop_1(sK1,sK4,sK5)
    | ~ spl10_122 ),
    inference(subsumption_resolution,[],[f20321,f67])).

fof(f20321,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r4_binop_1(sK1,sK4,sK5)
    | ~ spl10_122 ),
    inference(subsumption_resolution,[],[f20320,f66])).

fof(f20320,plain,
    ( ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r4_binop_1(sK1,sK4,sK5)
    | ~ spl10_122 ),
    inference(subsumption_resolution,[],[f20319,f65])).

fof(f20319,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r4_binop_1(sK1,sK4,sK5)
    | ~ spl10_122 ),
    inference(subsumption_resolution,[],[f20318,f68])).

fof(f20318,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r4_binop_1(sK1,sK4,sK5)
    | ~ spl10_122 ),
    inference(subsumption_resolution,[],[f20155,f69])).

fof(f20155,plain,
    ( v1_xboole_0(sK0)
    | v1_xboole_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r4_binop_1(sK1,sK4,sK5)
    | ~ spl10_122 ),
    inference(resolution,[],[f19700,f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ r4_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5))
      | r4_binop_1(X1,X4,X5) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f20122,plain,(
    spl10_135 ),
    inference(avatar_contradiction_clause,[],[f20121])).

fof(f20121,plain,
    ( $false
    | ~ spl10_135 ),
    inference(subsumption_resolution,[],[f19736,f1478])).

fof(f19736,plain,
    ( ~ v1_funct_1(k6_filter_1(sK0,sK1,sK2,sK4))
    | ~ spl10_135 ),
    inference(avatar_component_clause,[],[f19735])).

fof(f20120,plain,(
    spl10_133 ),
    inference(avatar_contradiction_clause,[],[f20119])).

fof(f20119,plain,
    ( $false
    | ~ spl10_133 ),
    inference(subsumption_resolution,[],[f20118,f61])).

fof(f20118,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ spl10_133 ),
    inference(subsumption_resolution,[],[f20117,f60])).

fof(f20117,plain,
    ( ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ spl10_133 ),
    inference(subsumption_resolution,[],[f20116,f59])).

fof(f20116,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ spl10_133 ),
    inference(subsumption_resolution,[],[f20115,f67])).

fof(f20115,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ spl10_133 ),
    inference(subsumption_resolution,[],[f20114,f66])).

fof(f20114,plain,
    ( ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ spl10_133 ),
    inference(subsumption_resolution,[],[f20088,f65])).

fof(f20088,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ spl10_133 ),
    inference(resolution,[],[f19730,f94])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | v1_funct_2(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f19730,plain,
    ( ~ v1_funct_2(k6_filter_1(sK0,sK1,sK2,sK4),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ spl10_133 ),
    inference(avatar_component_clause,[],[f19729])).

fof(f20078,plain,(
    spl10_131 ),
    inference(avatar_contradiction_clause,[],[f20077])).

fof(f20077,plain,
    ( $false
    | ~ spl10_131 ),
    inference(subsumption_resolution,[],[f20076,f61])).

fof(f20076,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ spl10_131 ),
    inference(subsumption_resolution,[],[f20075,f60])).

fof(f20075,plain,
    ( ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ spl10_131 ),
    inference(subsumption_resolution,[],[f20074,f59])).

fof(f20074,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ spl10_131 ),
    inference(subsumption_resolution,[],[f20073,f67])).

fof(f20073,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ spl10_131 ),
    inference(subsumption_resolution,[],[f20072,f66])).

fof(f20072,plain,
    ( ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ spl10_131 ),
    inference(subsumption_resolution,[],[f20044,f65])).

fof(f20044,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ spl10_131 ),
    inference(resolution,[],[f19724,f95])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | m1_subset_1(k6_filter_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1)))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f19724,plain,
    ( ~ m1_subset_1(k6_filter_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ spl10_131 ),
    inference(avatar_component_clause,[],[f19723])).

fof(f19840,plain,(
    spl10_129 ),
    inference(avatar_contradiction_clause,[],[f19839])).

fof(f19839,plain,
    ( $false
    | ~ spl10_129 ),
    inference(subsumption_resolution,[],[f19718,f1446])).

fof(f19718,plain,
    ( ~ v1_funct_1(k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ spl10_129 ),
    inference(avatar_component_clause,[],[f19717])).

fof(f19838,plain,(
    spl10_127 ),
    inference(avatar_contradiction_clause,[],[f19837])).

fof(f19837,plain,
    ( $false
    | ~ spl10_127 ),
    inference(subsumption_resolution,[],[f19836,f58])).

fof(f19836,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ spl10_127 ),
    inference(subsumption_resolution,[],[f19835,f57])).

fof(f19835,plain,
    ( ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ spl10_127 ),
    inference(subsumption_resolution,[],[f19834,f56])).

fof(f19834,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ spl10_127 ),
    inference(subsumption_resolution,[],[f19833,f64])).

fof(f19833,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ spl10_127 ),
    inference(subsumption_resolution,[],[f19832,f63])).

fof(f19832,plain,
    ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ spl10_127 ),
    inference(subsumption_resolution,[],[f19806,f62])).

fof(f19806,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ spl10_127 ),
    inference(resolution,[],[f19712,f94])).

fof(f19712,plain,
    ( ~ v1_funct_2(k6_filter_1(sK0,sK1,sK3,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ spl10_127 ),
    inference(avatar_component_clause,[],[f19711])).

fof(f19796,plain,(
    spl10_125 ),
    inference(avatar_contradiction_clause,[],[f19795])).

fof(f19795,plain,
    ( $false
    | ~ spl10_125 ),
    inference(subsumption_resolution,[],[f19794,f58])).

fof(f19794,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ spl10_125 ),
    inference(subsumption_resolution,[],[f19793,f57])).

fof(f19793,plain,
    ( ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ spl10_125 ),
    inference(subsumption_resolution,[],[f19792,f56])).

fof(f19792,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ spl10_125 ),
    inference(subsumption_resolution,[],[f19791,f64])).

fof(f19791,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ spl10_125 ),
    inference(subsumption_resolution,[],[f19790,f63])).

fof(f19790,plain,
    ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ spl10_125 ),
    inference(subsumption_resolution,[],[f19762,f62])).

fof(f19762,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ spl10_125 ),
    inference(resolution,[],[f19706,f95])).

fof(f19706,plain,
    ( ~ m1_subset_1(k6_filter_1(sK0,sK1,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ spl10_125 ),
    inference(avatar_component_clause,[],[f19705])).

fof(f19737,plain,
    ( spl10_122
    | ~ spl10_125
    | ~ spl10_127
    | ~ spl10_129
    | ~ spl10_131
    | ~ spl10_133
    | ~ spl10_135
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f1042,f1033,f19735,f19729,f19723,f19717,f19711,f19705,f19699])).

fof(f1042,plain,
    ( ~ v1_funct_1(k6_filter_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k6_filter_1(sK0,sK1,sK2,sK4),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ m1_subset_1(k6_filter_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ v1_funct_1(k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ v1_funct_2(k6_filter_1(sK0,sK1,sK3,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ m1_subset_1(k6_filter_1(sK0,sK1,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | r4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ spl10_2 ),
    inference(resolution,[],[f1034,f85])).

fof(f5595,plain,
    ( ~ spl10_5
    | spl10_84 ),
    inference(avatar_split_clause,[],[f1593,f3974,f1045])).

fof(f1045,plain,
    ( spl10_5
  <=> ~ r6_binop_1(sK1,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f1593,plain,
    ( r5_binop_1(sK1,sK4,sK5)
    | ~ r6_binop_1(sK1,sK4,sK5) ),
    inference(subsumption_resolution,[],[f1592,f59])).

fof(f1592,plain,
    ( ~ v1_funct_1(sK4)
    | r5_binop_1(sK1,sK4,sK5)
    | ~ r6_binop_1(sK1,sK4,sK5) ),
    inference(subsumption_resolution,[],[f1589,f60])).

fof(f1589,plain,
    ( ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK4)
    | r5_binop_1(sK1,sK4,sK5)
    | ~ r6_binop_1(sK1,sK4,sK5) ),
    inference(resolution,[],[f419,f61])).

fof(f419,plain,(
    ! [X98] :
      ( ~ m1_subset_1(X98,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
      | ~ v1_funct_2(X98,k2_zfmisc_1(sK1,sK1),sK1)
      | ~ v1_funct_1(X98)
      | r5_binop_1(sK1,X98,sK5)
      | ~ r6_binop_1(sK1,X98,sK5) ) ),
    inference(subsumption_resolution,[],[f418,f58])).

fof(f418,plain,(
    ! [X98] :
      ( ~ v1_funct_1(X98)
      | ~ v1_funct_2(X98,k2_zfmisc_1(sK1,sK1),sK1)
      | ~ m1_subset_1(X98,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
      | r5_binop_1(sK1,X98,sK5)
      | ~ r6_binop_1(sK1,X98,sK5) ) ),
    inference(subsumption_resolution,[],[f330,f56])).

fof(f330,plain,(
    ! [X98] :
      ( ~ v1_funct_1(X98)
      | ~ v1_funct_2(X98,k2_zfmisc_1(sK1,sK1),sK1)
      | ~ m1_subset_1(X98,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
      | ~ v1_funct_1(sK5)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
      | r5_binop_1(sK1,X98,sK5)
      | ~ r6_binop_1(sK1,X98,sK5) ) ),
    inference(resolution,[],[f57,f86])).

fof(f3979,plain,
    ( ~ spl10_85
    | ~ spl10_83
    | spl10_5 ),
    inference(avatar_split_clause,[],[f3972,f1045,f3960,f3977])).

fof(f3972,plain,
    ( ~ r4_binop_1(sK1,sK4,sK5)
    | ~ r5_binop_1(sK1,sK4,sK5)
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f3971,f58])).

fof(f3971,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ r4_binop_1(sK1,sK4,sK5)
    | ~ r5_binop_1(sK1,sK4,sK5)
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f3970,f57])).

fof(f3970,plain,
    ( ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ r4_binop_1(sK1,sK4,sK5)
    | ~ r5_binop_1(sK1,sK4,sK5)
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f3969,f56])).

fof(f3969,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ r4_binop_1(sK1,sK4,sK5)
    | ~ r5_binop_1(sK1,sK4,sK5)
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f3968,f61])).

fof(f3968,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ r4_binop_1(sK1,sK4,sK5)
    | ~ r5_binop_1(sK1,sK4,sK5)
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f3967,f60])).

fof(f3967,plain,
    ( ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ r4_binop_1(sK1,sK4,sK5)
    | ~ r5_binop_1(sK1,sK4,sK5)
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f3966,f59])).

fof(f3966,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ r4_binop_1(sK1,sK4,sK5)
    | ~ r5_binop_1(sK1,sK4,sK5)
    | ~ spl10_5 ),
    inference(resolution,[],[f1046,f87])).

fof(f1046,plain,
    ( ~ r6_binop_1(sK1,sK4,sK5)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f1045])).

fof(f1051,plain,
    ( ~ spl10_5
    | ~ spl10_1
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f53,f1030,f1024,f1045])).

fof(f53,plain,
    ( ~ r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ r6_binop_1(sK0,sK2,sK3)
    | ~ r6_binop_1(sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f28])).

fof(f1050,plain,
    ( spl10_4
    | spl10_2 ),
    inference(avatar_split_clause,[],[f55,f1033,f1048])).

fof(f55,plain,
    ( r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | r6_binop_1(sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f28])).

fof(f1035,plain,
    ( spl10_0
    | spl10_2 ),
    inference(avatar_split_clause,[],[f54,f1033,f1027])).

fof(f54,plain,
    ( r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | r6_binop_1(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
