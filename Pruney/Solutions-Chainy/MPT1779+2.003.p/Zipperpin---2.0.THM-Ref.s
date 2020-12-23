%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zMr4x22tDf

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:40 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :  210 ( 538 expanded)
%              Number of leaves         :   24 ( 163 expanded)
%              Depth                    :   21
%              Number of atoms          : 3326 (38417 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   27 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(t90_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ! [E: $i] :
                      ( ( ~ ( v2_struct_0 @ E )
                        & ( m1_pre_topc @ E @ A ) )
                     => ( ( ( m1_pre_topc @ C @ D )
                          & ( m1_pre_topc @ E @ C ) )
                       => ! [F: $i] :
                            ( ( ( v1_funct_1 @ F )
                              & ( v1_funct_2 @ F @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                              & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
                           => ( ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ D @ C @ F ) )
                                & ( v1_funct_2 @ ( k3_tmap_1 @ A @ B @ D @ C @ F ) @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                                & ( v5_pre_topc @ ( k3_tmap_1 @ A @ B @ D @ C @ F ) @ C @ B )
                                & ( m1_subset_1 @ ( k3_tmap_1 @ A @ B @ D @ C @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                             => ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ D @ E @ F ) )
                                & ( v1_funct_2 @ ( k3_tmap_1 @ A @ B @ D @ E @ F ) @ ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) )
                                & ( v5_pre_topc @ ( k3_tmap_1 @ A @ B @ D @ E @ F ) @ E @ B )
                                & ( m1_subset_1 @ ( k3_tmap_1 @ A @ B @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v2_pre_topc @ B )
              & ( l1_pre_topc @ B ) )
           => ! [C: $i] :
                ( ( ~ ( v2_struct_0 @ C )
                  & ( m1_pre_topc @ C @ A ) )
               => ! [D: $i] :
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( m1_pre_topc @ D @ A ) )
                   => ! [E: $i] :
                        ( ( ~ ( v2_struct_0 @ E )
                          & ( m1_pre_topc @ E @ A ) )
                       => ( ( ( m1_pre_topc @ C @ D )
                            & ( m1_pre_topc @ E @ C ) )
                         => ! [F: $i] :
                              ( ( ( v1_funct_1 @ F )
                                & ( v1_funct_2 @ F @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                                & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
                             => ( ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ D @ C @ F ) )
                                  & ( v1_funct_2 @ ( k3_tmap_1 @ A @ B @ D @ C @ F ) @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                                  & ( v5_pre_topc @ ( k3_tmap_1 @ A @ B @ D @ C @ F ) @ C @ B )
                                  & ( m1_subset_1 @ ( k3_tmap_1 @ A @ B @ D @ C @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                               => ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ D @ E @ F ) )
                                  & ( v1_funct_2 @ ( k3_tmap_1 @ A @ B @ D @ E @ F ) @ ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) )
                                  & ( v5_pre_topc @ ( k3_tmap_1 @ A @ B @ D @ E @ F ) @ E @ B )
                                  & ( m1_subset_1 @ ( k3_tmap_1 @ A @ B @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t90_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t79_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ! [E: $i] :
                      ( ( ~ ( v2_struct_0 @ E )
                        & ( m1_pre_topc @ E @ A ) )
                     => ( ( ( m1_pre_topc @ D @ C )
                          & ( m1_pre_topc @ E @ D ) )
                       => ! [F: $i] :
                            ( ( ( v1_funct_1 @ F )
                              & ( v1_funct_2 @ F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                              & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                           => ( r2_funct_2 @ ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ D @ E @ ( k3_tmap_1 @ A @ B @ C @ D @ F ) ) @ ( k3_tmap_1 @ A @ B @ C @ E @ F ) ) ) ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( m1_pre_topc @ X10 @ X12 )
      | ~ ( m1_pre_topc @ X13 @ X10 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_funct_2 @ X14 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X9 ) @ ( k3_tmap_1 @ X11 @ X9 @ X10 @ X13 @ ( k3_tmap_1 @ X11 @ X9 @ X12 @ X10 @ X14 ) ) @ ( k3_tmap_1 @ X11 @ X9 @ X12 @ X13 @ X14 ) )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ( v2_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t79_tmap_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ X0 @ sk_B @ X2 @ X1 @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X2 @ sk_F ) ) @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_F ) )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( m1_pre_topc @ X2 @ sk_D )
      | ~ ( m1_pre_topc @ X2 @ X0 )
      | ( v2_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ X0 @ sk_B @ X2 @ X1 @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X2 @ sk_F ) ) @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_F ) )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( m1_pre_topc @ X2 @ sk_D )
      | ~ ( m1_pre_topc @ X2 @ X0 )
      | ( v2_struct_0 @ X2 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','7','8','9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ X0 @ X1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F ) ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X1 @ sk_F ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ X0 @ X1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F ) ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X1 @ sk_F ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','15'])).

thf('17',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_E @ sk_C )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','18'])).

thf('20',plain,(
    m1_pre_topc @ sk_E @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_tmap_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( v2_pre_topc @ B )
        & ( l1_pre_topc @ B )
        & ( m1_pre_topc @ C @ A )
        & ( m1_pre_topc @ D @ A )
        & ( v1_funct_1 @ E )
        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
     => ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) )
        & ( v1_funct_2 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) )).

thf('25',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ~ ( m1_pre_topc @ X6 @ X5 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_funct_2 @ X8 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X7 ) ) ) )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X5 @ X7 @ X6 @ X4 @ X8 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X7 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['26','27','28','29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['23','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['22','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf(redefinition_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_funct_2 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_funct_2 @ X3 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ( X0 = X3 )
      | ~ ( r2_funct_2 @ X1 @ X2 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) @ X0 )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ~ ( m1_pre_topc @ X6 @ X5 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_funct_2 @ X8 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X7 ) ) ) )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X5 @ X7 @ X6 @ X4 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['47','48','49','50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) ) ) ),
    inference('sup-',[status(thm)],['44','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['43','56'])).

thf('58',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ~ ( m1_pre_topc @ X6 @ X5 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_funct_2 @ X8 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X7 ) ) ) )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X5 @ X7 @ X6 @ X4 @ X8 ) @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['66','67','68','69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['63','71'])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['62','75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) @ X0 )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['42','61','80'])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) )
      = ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['21','81'])).

thf('83',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ~ ( m1_pre_topc @ X6 @ X5 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_funct_2 @ X8 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X7 ) ) ) )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X5 @ X7 @ X6 @ X4 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_F ) )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_F )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_F ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['87','88','89','90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['84','92'])).

thf('94',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F ) ) ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['83','96'])).

thf('98',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ~ ( m1_pre_topc @ X6 @ X5 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_funct_2 @ X8 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X7 ) ) ) )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X5 @ X7 @ X6 @ X4 @ X8 ) @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_F ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_F )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_F ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['106','107','108','109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['103','111'])).

thf('113',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('116',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['102','115'])).

thf('117',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('119',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['118','119'])).

thf('121',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ~ ( m1_pre_topc @ X6 @ X5 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_funct_2 @ X8 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X7 ) ) ) )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X5 @ X7 @ X6 @ X4 @ X8 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X7 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_F )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['125','126','127','128','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['122','130'])).

thf('132',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['131','132','133'])).

thf('135',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['121','134'])).

thf('136',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['135','136'])).

thf('138',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['137','138'])).

thf('140',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) )
      = ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) ) ),
    inference(demod,[status(thm)],['82','101','120','139'])).

thf('141',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t89_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                        & ( v5_pre_topc @ E @ C @ B )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ( ( m1_pre_topc @ D @ C )
                       => ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) )
                          & ( v1_funct_2 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                          & ( v5_pre_topc @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ D @ B )
                          & ( m1_subset_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) )).

thf('144',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_pre_topc @ X16 @ X17 )
      | ~ ( m1_pre_topc @ X16 @ X18 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ X17 @ X15 @ X18 @ X16 @ X19 ) @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X15 ) ) ) )
      | ~ ( v5_pre_topc @ X19 @ X18 @ X15 )
      | ~ ( v1_funct_2 @ X19 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( m1_pre_topc @ X18 @ X17 )
      | ( v2_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t89_tmap_1])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ sk_C @ sk_B )
      | ( v5_pre_topc @ ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) @ X1 @ sk_B )
      | ~ ( m1_pre_topc @ X1 @ sk_C )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) @ X1 @ sk_B )
      | ~ ( m1_pre_topc @ X1 @ sk_C )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['145','146','147','148','149','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['142','151'])).

thf('153',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['152','153','154'])).

thf('156',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) @ sk_E @ sk_B )
    | ~ ( m1_pre_topc @ sk_E @ sk_C )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['141','155'])).

thf('157',plain,(
    m1_pre_topc @ sk_E @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) @ sk_E @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,
    ( ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ sk_E @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['140','158'])).

thf('160',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ sk_E @ sk_B ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,
    ( ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ sk_E @ sk_B )
    | ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,
    ( ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ sk_E @ sk_B )
   <= ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ sk_E @ sk_B ) ),
    inference(split,[status(esa)],['161'])).

thf('163',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['137','138'])).

thf('164',plain,
    ( ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['161'])).

thf('165',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('167',plain,
    ( ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) )
   <= ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) ) ),
    inference(split,[status(esa)],['161'])).

thf('168',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['118','119'])).

thf('170',plain,
    ( ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['161'])).

thf('171',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,
    ( ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ sk_E @ sk_B )
    | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) )
    | ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['161'])).

thf('173',plain,(
    ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ sk_E @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['165','168','171','172'])).

thf('174',plain,(
    ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ sk_E @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['162','173'])).

thf('175',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['160','174'])).

thf('176',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_E ) ),
    inference(clc,[status(thm)],['179','180'])).

thf('182',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    v2_struct_0 @ sk_E ),
    inference(clc,[status(thm)],['181','182'])).

thf('184',plain,(
    $false ),
    inference(demod,[status(thm)],['0','183'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zMr4x22tDf
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:59:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.36/1.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.36/1.56  % Solved by: fo/fo7.sh
% 1.36/1.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.36/1.56  % done 1155 iterations in 1.099s
% 1.36/1.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.36/1.56  % SZS output start Refutation
% 1.36/1.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.36/1.56  thf(sk_D_type, type, sk_D: $i).
% 1.36/1.56  thf(sk_B_type, type, sk_B: $i).
% 1.36/1.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.36/1.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.36/1.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.36/1.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.36/1.56  thf(sk_A_type, type, sk_A: $i).
% 1.36/1.56  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 1.36/1.56  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.36/1.56  thf(sk_F_type, type, sk_F: $i).
% 1.36/1.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.36/1.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.36/1.56  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 1.36/1.56  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 1.36/1.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.36/1.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.36/1.56  thf(sk_C_type, type, sk_C: $i).
% 1.36/1.56  thf(sk_E_type, type, sk_E: $i).
% 1.36/1.56  thf(t90_tmap_1, conjecture,
% 1.36/1.56    (![A:$i]:
% 1.36/1.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.36/1.56       ( ![B:$i]:
% 1.36/1.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.36/1.56             ( l1_pre_topc @ B ) ) =>
% 1.36/1.56           ( ![C:$i]:
% 1.36/1.56             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.36/1.56               ( ![D:$i]:
% 1.36/1.56                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.36/1.56                   ( ![E:$i]:
% 1.36/1.56                     ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 1.36/1.56                       ( ( ( m1_pre_topc @ C @ D ) & ( m1_pre_topc @ E @ C ) ) =>
% 1.36/1.56                         ( ![F:$i]:
% 1.36/1.56                           ( ( ( v1_funct_1 @ F ) & 
% 1.36/1.56                               ( v1_funct_2 @
% 1.36/1.56                                 F @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 1.36/1.56                               ( m1_subset_1 @
% 1.36/1.56                                 F @ 
% 1.36/1.56                                 ( k1_zfmisc_1 @
% 1.36/1.56                                   ( k2_zfmisc_1 @
% 1.36/1.56                                     ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.36/1.56                             ( ( ( v1_funct_1 @
% 1.36/1.56                                   ( k3_tmap_1 @ A @ B @ D @ C @ F ) ) & 
% 1.36/1.56                                 ( v1_funct_2 @
% 1.36/1.56                                   ( k3_tmap_1 @ A @ B @ D @ C @ F ) @ 
% 1.36/1.56                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.36/1.56                                 ( v5_pre_topc @
% 1.36/1.56                                   ( k3_tmap_1 @ A @ B @ D @ C @ F ) @ C @ B ) & 
% 1.36/1.56                                 ( m1_subset_1 @
% 1.36/1.56                                   ( k3_tmap_1 @ A @ B @ D @ C @ F ) @ 
% 1.36/1.56                                   ( k1_zfmisc_1 @
% 1.36/1.56                                     ( k2_zfmisc_1 @
% 1.36/1.56                                       ( u1_struct_0 @ C ) @ 
% 1.36/1.56                                       ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.36/1.56                               ( ( v1_funct_1 @
% 1.36/1.56                                   ( k3_tmap_1 @ A @ B @ D @ E @ F ) ) & 
% 1.36/1.56                                 ( v1_funct_2 @
% 1.36/1.56                                   ( k3_tmap_1 @ A @ B @ D @ E @ F ) @ 
% 1.36/1.56                                   ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) & 
% 1.36/1.56                                 ( v5_pre_topc @
% 1.36/1.56                                   ( k3_tmap_1 @ A @ B @ D @ E @ F ) @ E @ B ) & 
% 1.36/1.56                                 ( m1_subset_1 @
% 1.36/1.56                                   ( k3_tmap_1 @ A @ B @ D @ E @ F ) @ 
% 1.36/1.56                                   ( k1_zfmisc_1 @
% 1.36/1.56                                     ( k2_zfmisc_1 @
% 1.36/1.56                                       ( u1_struct_0 @ E ) @ 
% 1.36/1.56                                       ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.36/1.56  thf(zf_stmt_0, negated_conjecture,
% 1.36/1.56    (~( ![A:$i]:
% 1.36/1.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.36/1.56            ( l1_pre_topc @ A ) ) =>
% 1.36/1.56          ( ![B:$i]:
% 1.36/1.56            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.36/1.56                ( l1_pre_topc @ B ) ) =>
% 1.36/1.56              ( ![C:$i]:
% 1.36/1.56                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.36/1.56                  ( ![D:$i]:
% 1.36/1.56                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.36/1.56                      ( ![E:$i]:
% 1.36/1.56                        ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 1.36/1.56                          ( ( ( m1_pre_topc @ C @ D ) & ( m1_pre_topc @ E @ C ) ) =>
% 1.36/1.56                            ( ![F:$i]:
% 1.36/1.56                              ( ( ( v1_funct_1 @ F ) & 
% 1.36/1.56                                  ( v1_funct_2 @
% 1.36/1.56                                    F @ ( u1_struct_0 @ D ) @ 
% 1.36/1.56                                    ( u1_struct_0 @ B ) ) & 
% 1.36/1.56                                  ( m1_subset_1 @
% 1.36/1.56                                    F @ 
% 1.36/1.56                                    ( k1_zfmisc_1 @
% 1.36/1.56                                      ( k2_zfmisc_1 @
% 1.36/1.56                                        ( u1_struct_0 @ D ) @ 
% 1.36/1.56                                        ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.36/1.56                                ( ( ( v1_funct_1 @
% 1.36/1.56                                      ( k3_tmap_1 @ A @ B @ D @ C @ F ) ) & 
% 1.36/1.56                                    ( v1_funct_2 @
% 1.36/1.56                                      ( k3_tmap_1 @ A @ B @ D @ C @ F ) @ 
% 1.36/1.56                                      ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.36/1.56                                    ( v5_pre_topc @
% 1.36/1.56                                      ( k3_tmap_1 @ A @ B @ D @ C @ F ) @ C @ B ) & 
% 1.36/1.56                                    ( m1_subset_1 @
% 1.36/1.56                                      ( k3_tmap_1 @ A @ B @ D @ C @ F ) @ 
% 1.36/1.56                                      ( k1_zfmisc_1 @
% 1.36/1.56                                        ( k2_zfmisc_1 @
% 1.36/1.56                                          ( u1_struct_0 @ C ) @ 
% 1.36/1.56                                          ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.36/1.56                                  ( ( v1_funct_1 @
% 1.36/1.56                                      ( k3_tmap_1 @ A @ B @ D @ E @ F ) ) & 
% 1.36/1.56                                    ( v1_funct_2 @
% 1.36/1.56                                      ( k3_tmap_1 @ A @ B @ D @ E @ F ) @ 
% 1.36/1.56                                      ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) & 
% 1.36/1.56                                    ( v5_pre_topc @
% 1.36/1.56                                      ( k3_tmap_1 @ A @ B @ D @ E @ F ) @ E @ B ) & 
% 1.36/1.56                                    ( m1_subset_1 @
% 1.36/1.56                                      ( k3_tmap_1 @ A @ B @ D @ E @ F ) @ 
% 1.36/1.56                                      ( k1_zfmisc_1 @
% 1.36/1.56                                        ( k2_zfmisc_1 @
% 1.36/1.56                                          ( u1_struct_0 @ E ) @ 
% 1.36/1.56                                          ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.36/1.56    inference('cnf.neg', [status(esa)], [t90_tmap_1])).
% 1.36/1.56  thf('0', plain, (~ (v2_struct_0 @ sk_E)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('1', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('2', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('3', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('4', plain,
% 1.36/1.56      ((m1_subset_1 @ sk_F @ 
% 1.36/1.56        (k1_zfmisc_1 @ 
% 1.36/1.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf(t79_tmap_1, axiom,
% 1.36/1.56    (![A:$i]:
% 1.36/1.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.36/1.56       ( ![B:$i]:
% 1.36/1.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.36/1.56             ( l1_pre_topc @ B ) ) =>
% 1.36/1.56           ( ![C:$i]:
% 1.36/1.56             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.36/1.56               ( ![D:$i]:
% 1.36/1.56                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.36/1.56                   ( ![E:$i]:
% 1.36/1.56                     ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 1.36/1.56                       ( ( ( m1_pre_topc @ D @ C ) & ( m1_pre_topc @ E @ D ) ) =>
% 1.36/1.56                         ( ![F:$i]:
% 1.36/1.56                           ( ( ( v1_funct_1 @ F ) & 
% 1.36/1.56                               ( v1_funct_2 @
% 1.36/1.56                                 F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.36/1.56                               ( m1_subset_1 @
% 1.36/1.56                                 F @ 
% 1.36/1.56                                 ( k1_zfmisc_1 @
% 1.36/1.56                                   ( k2_zfmisc_1 @
% 1.36/1.56                                     ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.36/1.56                             ( r2_funct_2 @
% 1.36/1.56                               ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) @ 
% 1.36/1.56                               ( k3_tmap_1 @
% 1.36/1.56                                 A @ B @ D @ E @ 
% 1.36/1.56                                 ( k3_tmap_1 @ A @ B @ C @ D @ F ) ) @ 
% 1.36/1.56                               ( k3_tmap_1 @ A @ B @ C @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.36/1.56  thf('5', plain,
% 1.36/1.56      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 1.36/1.56         ((v2_struct_0 @ X9)
% 1.36/1.56          | ~ (v2_pre_topc @ X9)
% 1.36/1.56          | ~ (l1_pre_topc @ X9)
% 1.36/1.56          | (v2_struct_0 @ X10)
% 1.36/1.56          | ~ (m1_pre_topc @ X10 @ X11)
% 1.36/1.56          | ~ (m1_pre_topc @ X10 @ X12)
% 1.36/1.56          | ~ (m1_pre_topc @ X13 @ X10)
% 1.36/1.56          | ~ (v1_funct_1 @ X14)
% 1.36/1.56          | ~ (v1_funct_2 @ X14 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X9))
% 1.36/1.56          | ~ (m1_subset_1 @ X14 @ 
% 1.36/1.56               (k1_zfmisc_1 @ 
% 1.36/1.56                (k2_zfmisc_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X9))))
% 1.36/1.56          | (r2_funct_2 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X9) @ 
% 1.36/1.56             (k3_tmap_1 @ X11 @ X9 @ X10 @ X13 @ 
% 1.36/1.56              (k3_tmap_1 @ X11 @ X9 @ X12 @ X10 @ X14)) @ 
% 1.36/1.56             (k3_tmap_1 @ X11 @ X9 @ X12 @ X13 @ X14))
% 1.36/1.56          | ~ (m1_pre_topc @ X13 @ X11)
% 1.36/1.56          | (v2_struct_0 @ X13)
% 1.36/1.56          | ~ (m1_pre_topc @ X12 @ X11)
% 1.36/1.56          | (v2_struct_0 @ X12)
% 1.36/1.56          | ~ (l1_pre_topc @ X11)
% 1.36/1.56          | ~ (v2_pre_topc @ X11)
% 1.36/1.56          | (v2_struct_0 @ X11))),
% 1.36/1.56      inference('cnf', [status(esa)], [t79_tmap_1])).
% 1.36/1.56  thf('6', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.36/1.56         ((v2_struct_0 @ X0)
% 1.36/1.56          | ~ (v2_pre_topc @ X0)
% 1.36/1.56          | ~ (l1_pre_topc @ X0)
% 1.36/1.56          | (v2_struct_0 @ sk_D)
% 1.36/1.56          | ~ (m1_pre_topc @ sk_D @ X0)
% 1.36/1.56          | (v2_struct_0 @ X1)
% 1.36/1.56          | ~ (m1_pre_topc @ X1 @ X0)
% 1.36/1.56          | (r2_funct_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B) @ 
% 1.36/1.56             (k3_tmap_1 @ X0 @ sk_B @ X2 @ X1 @ 
% 1.36/1.56              (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X2 @ sk_F)) @ 
% 1.36/1.56             (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_F))
% 1.36/1.56          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.36/1.56          | ~ (v1_funct_1 @ sk_F)
% 1.36/1.56          | ~ (m1_pre_topc @ X1 @ X2)
% 1.36/1.56          | ~ (m1_pre_topc @ X2 @ sk_D)
% 1.36/1.56          | ~ (m1_pre_topc @ X2 @ X0)
% 1.36/1.56          | (v2_struct_0 @ X2)
% 1.36/1.56          | ~ (l1_pre_topc @ sk_B)
% 1.36/1.56          | ~ (v2_pre_topc @ sk_B)
% 1.36/1.56          | (v2_struct_0 @ sk_B))),
% 1.36/1.56      inference('sup-', [status(thm)], ['4', '5'])).
% 1.36/1.56  thf('7', plain,
% 1.36/1.56      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('8', plain, ((v1_funct_1 @ sk_F)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('9', plain, ((l1_pre_topc @ sk_B)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('10', plain, ((v2_pre_topc @ sk_B)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('11', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.36/1.56         ((v2_struct_0 @ X0)
% 1.36/1.56          | ~ (v2_pre_topc @ X0)
% 1.36/1.56          | ~ (l1_pre_topc @ X0)
% 1.36/1.56          | (v2_struct_0 @ sk_D)
% 1.36/1.56          | ~ (m1_pre_topc @ sk_D @ X0)
% 1.36/1.56          | (v2_struct_0 @ X1)
% 1.36/1.56          | ~ (m1_pre_topc @ X1 @ X0)
% 1.36/1.56          | (r2_funct_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B) @ 
% 1.36/1.56             (k3_tmap_1 @ X0 @ sk_B @ X2 @ X1 @ 
% 1.36/1.56              (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X2 @ sk_F)) @ 
% 1.36/1.56             (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_F))
% 1.36/1.56          | ~ (m1_pre_topc @ X1 @ X2)
% 1.36/1.56          | ~ (m1_pre_topc @ X2 @ sk_D)
% 1.36/1.56          | ~ (m1_pre_topc @ X2 @ X0)
% 1.36/1.56          | (v2_struct_0 @ X2)
% 1.36/1.56          | (v2_struct_0 @ sk_B))),
% 1.36/1.56      inference('demod', [status(thm)], ['6', '7', '8', '9', '10'])).
% 1.36/1.56  thf('12', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         ((v2_struct_0 @ sk_B)
% 1.36/1.56          | (v2_struct_0 @ X0)
% 1.36/1.56          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.36/1.56          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.36/1.56          | ~ (m1_pre_topc @ X1 @ X0)
% 1.36/1.56          | (r2_funct_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B) @ 
% 1.36/1.56             (k3_tmap_1 @ sk_A @ sk_B @ X0 @ X1 @ 
% 1.36/1.56              (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F)) @ 
% 1.36/1.56             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X1 @ sk_F))
% 1.36/1.56          | ~ (m1_pre_topc @ X1 @ sk_A)
% 1.36/1.56          | (v2_struct_0 @ X1)
% 1.36/1.56          | (v2_struct_0 @ sk_D)
% 1.36/1.56          | ~ (l1_pre_topc @ sk_A)
% 1.36/1.56          | ~ (v2_pre_topc @ sk_A)
% 1.36/1.56          | (v2_struct_0 @ sk_A))),
% 1.36/1.56      inference('sup-', [status(thm)], ['3', '11'])).
% 1.36/1.56  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('14', plain, ((v2_pre_topc @ sk_A)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('15', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         ((v2_struct_0 @ sk_B)
% 1.36/1.56          | (v2_struct_0 @ X0)
% 1.36/1.56          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.36/1.56          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.36/1.56          | ~ (m1_pre_topc @ X1 @ X0)
% 1.36/1.56          | (r2_funct_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B) @ 
% 1.36/1.56             (k3_tmap_1 @ sk_A @ sk_B @ X0 @ X1 @ 
% 1.36/1.56              (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F)) @ 
% 1.36/1.56             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X1 @ sk_F))
% 1.36/1.56          | ~ (m1_pre_topc @ X1 @ sk_A)
% 1.36/1.56          | (v2_struct_0 @ X1)
% 1.36/1.56          | (v2_struct_0 @ sk_D)
% 1.36/1.56          | (v2_struct_0 @ sk_A))),
% 1.36/1.56      inference('demod', [status(thm)], ['12', '13', '14'])).
% 1.36/1.56  thf('16', plain,
% 1.36/1.56      (![X0 : $i]:
% 1.36/1.56         ((v2_struct_0 @ sk_A)
% 1.36/1.56          | (v2_struct_0 @ sk_D)
% 1.36/1.56          | (v2_struct_0 @ X0)
% 1.36/1.56          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.36/1.56          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 1.36/1.56             (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ 
% 1.36/1.56              (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)) @ 
% 1.36/1.56             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F))
% 1.36/1.56          | ~ (m1_pre_topc @ X0 @ sk_C)
% 1.36/1.56          | ~ (m1_pre_topc @ sk_C @ sk_D)
% 1.36/1.56          | (v2_struct_0 @ sk_C)
% 1.36/1.56          | (v2_struct_0 @ sk_B))),
% 1.36/1.56      inference('sup-', [status(thm)], ['2', '15'])).
% 1.36/1.56  thf('17', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('18', plain,
% 1.36/1.56      (![X0 : $i]:
% 1.36/1.56         ((v2_struct_0 @ sk_A)
% 1.36/1.56          | (v2_struct_0 @ sk_D)
% 1.36/1.56          | (v2_struct_0 @ X0)
% 1.36/1.56          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.36/1.56          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 1.36/1.56             (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ 
% 1.36/1.56              (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)) @ 
% 1.36/1.56             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F))
% 1.36/1.56          | ~ (m1_pre_topc @ X0 @ sk_C)
% 1.36/1.56          | (v2_struct_0 @ sk_C)
% 1.36/1.56          | (v2_struct_0 @ sk_B))),
% 1.36/1.56      inference('demod', [status(thm)], ['16', '17'])).
% 1.36/1.56  thf('19', plain,
% 1.36/1.56      (((v2_struct_0 @ sk_B)
% 1.36/1.56        | (v2_struct_0 @ sk_C)
% 1.36/1.56        | ~ (m1_pre_topc @ sk_E @ sk_C)
% 1.36/1.56        | (r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 1.36/1.56           (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ 
% 1.36/1.56            (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)) @ 
% 1.36/1.56           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F))
% 1.36/1.56        | (v2_struct_0 @ sk_E)
% 1.36/1.56        | (v2_struct_0 @ sk_D)
% 1.36/1.56        | (v2_struct_0 @ sk_A))),
% 1.36/1.56      inference('sup-', [status(thm)], ['1', '18'])).
% 1.36/1.56  thf('20', plain, ((m1_pre_topc @ sk_E @ sk_C)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('21', plain,
% 1.36/1.56      (((v2_struct_0 @ sk_B)
% 1.36/1.56        | (v2_struct_0 @ sk_C)
% 1.36/1.56        | (r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 1.36/1.56           (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ 
% 1.36/1.56            (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)) @ 
% 1.36/1.56           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F))
% 1.36/1.56        | (v2_struct_0 @ sk_E)
% 1.36/1.56        | (v2_struct_0 @ sk_D)
% 1.36/1.56        | (v2_struct_0 @ sk_A))),
% 1.36/1.56      inference('demod', [status(thm)], ['19', '20'])).
% 1.36/1.56  thf('22', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('23', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('24', plain,
% 1.36/1.56      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 1.36/1.56        (k1_zfmisc_1 @ 
% 1.36/1.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf(dt_k3_tmap_1, axiom,
% 1.36/1.56    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.36/1.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.36/1.56         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 1.36/1.56         ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) & ( m1_pre_topc @ C @ A ) & 
% 1.36/1.56         ( m1_pre_topc @ D @ A ) & ( v1_funct_1 @ E ) & 
% 1.36/1.56         ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.36/1.56         ( m1_subset_1 @
% 1.36/1.56           E @ 
% 1.36/1.56           ( k1_zfmisc_1 @
% 1.36/1.56             ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.36/1.56       ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) ) & 
% 1.36/1.56         ( v1_funct_2 @
% 1.36/1.56           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ 
% 1.36/1.56           ( u1_struct_0 @ B ) ) & 
% 1.36/1.56         ( m1_subset_1 @
% 1.36/1.56           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 1.36/1.56           ( k1_zfmisc_1 @
% 1.36/1.56             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 1.36/1.56  thf('25', plain,
% 1.36/1.56      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 1.36/1.56         (~ (m1_pre_topc @ X4 @ X5)
% 1.36/1.56          | ~ (m1_pre_topc @ X6 @ X5)
% 1.36/1.56          | ~ (l1_pre_topc @ X7)
% 1.36/1.56          | ~ (v2_pre_topc @ X7)
% 1.36/1.56          | (v2_struct_0 @ X7)
% 1.36/1.56          | ~ (l1_pre_topc @ X5)
% 1.36/1.56          | ~ (v2_pre_topc @ X5)
% 1.36/1.56          | (v2_struct_0 @ X5)
% 1.36/1.56          | ~ (v1_funct_1 @ X8)
% 1.36/1.56          | ~ (v1_funct_2 @ X8 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X7))
% 1.36/1.56          | ~ (m1_subset_1 @ X8 @ 
% 1.36/1.56               (k1_zfmisc_1 @ 
% 1.36/1.56                (k2_zfmisc_1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X7))))
% 1.36/1.56          | (m1_subset_1 @ (k3_tmap_1 @ X5 @ X7 @ X6 @ X4 @ X8) @ 
% 1.36/1.56             (k1_zfmisc_1 @ 
% 1.36/1.56              (k2_zfmisc_1 @ (u1_struct_0 @ X4) @ (u1_struct_0 @ X7)))))),
% 1.36/1.56      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 1.36/1.56  thf('26', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         ((m1_subset_1 @ 
% 1.36/1.56           (k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ 
% 1.36/1.56            (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)) @ 
% 1.36/1.56           (k1_zfmisc_1 @ 
% 1.36/1.56            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.36/1.56          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 1.36/1.56               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.36/1.56          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F))
% 1.36/1.56          | (v2_struct_0 @ X1)
% 1.36/1.56          | ~ (v2_pre_topc @ X1)
% 1.36/1.56          | ~ (l1_pre_topc @ X1)
% 1.36/1.56          | (v2_struct_0 @ sk_B)
% 1.36/1.56          | ~ (v2_pre_topc @ sk_B)
% 1.36/1.56          | ~ (l1_pre_topc @ sk_B)
% 1.36/1.56          | ~ (m1_pre_topc @ sk_C @ X1)
% 1.36/1.56          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.36/1.56      inference('sup-', [status(thm)], ['24', '25'])).
% 1.36/1.56  thf('27', plain,
% 1.36/1.56      ((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 1.36/1.56        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('28', plain,
% 1.36/1.56      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F))),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('29', plain, ((v2_pre_topc @ sk_B)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('30', plain, ((l1_pre_topc @ sk_B)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('31', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         ((m1_subset_1 @ 
% 1.36/1.56           (k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ 
% 1.36/1.56            (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)) @ 
% 1.36/1.56           (k1_zfmisc_1 @ 
% 1.36/1.56            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.36/1.56          | (v2_struct_0 @ X1)
% 1.36/1.56          | ~ (v2_pre_topc @ X1)
% 1.36/1.56          | ~ (l1_pre_topc @ X1)
% 1.36/1.56          | (v2_struct_0 @ sk_B)
% 1.36/1.56          | ~ (m1_pre_topc @ sk_C @ X1)
% 1.36/1.56          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.36/1.56      inference('demod', [status(thm)], ['26', '27', '28', '29', '30'])).
% 1.36/1.56  thf('32', plain,
% 1.36/1.56      (![X0 : $i]:
% 1.36/1.56         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.36/1.56          | (v2_struct_0 @ sk_B)
% 1.36/1.56          | ~ (l1_pre_topc @ sk_A)
% 1.36/1.56          | ~ (v2_pre_topc @ sk_A)
% 1.36/1.56          | (v2_struct_0 @ sk_A)
% 1.36/1.56          | (m1_subset_1 @ 
% 1.36/1.56             (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ 
% 1.36/1.56              (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)) @ 
% 1.36/1.56             (k1_zfmisc_1 @ 
% 1.36/1.56              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 1.36/1.56      inference('sup-', [status(thm)], ['23', '31'])).
% 1.36/1.56  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('34', plain, ((v2_pre_topc @ sk_A)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('35', plain,
% 1.36/1.56      (![X0 : $i]:
% 1.36/1.56         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.36/1.56          | (v2_struct_0 @ sk_B)
% 1.36/1.56          | (v2_struct_0 @ sk_A)
% 1.36/1.56          | (m1_subset_1 @ 
% 1.36/1.56             (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ 
% 1.36/1.56              (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)) @ 
% 1.36/1.56             (k1_zfmisc_1 @ 
% 1.36/1.56              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 1.36/1.56      inference('demod', [status(thm)], ['32', '33', '34'])).
% 1.36/1.56  thf('36', plain,
% 1.36/1.56      (((m1_subset_1 @ 
% 1.36/1.56         (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ 
% 1.36/1.56          (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)) @ 
% 1.36/1.56         (k1_zfmisc_1 @ 
% 1.36/1.56          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 1.36/1.56        | (v2_struct_0 @ sk_A)
% 1.36/1.56        | (v2_struct_0 @ sk_B))),
% 1.36/1.56      inference('sup-', [status(thm)], ['22', '35'])).
% 1.36/1.56  thf('37', plain, (~ (v2_struct_0 @ sk_A)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('38', plain,
% 1.36/1.56      (((v2_struct_0 @ sk_B)
% 1.36/1.56        | (m1_subset_1 @ 
% 1.36/1.56           (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ 
% 1.36/1.56            (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)) @ 
% 1.36/1.56           (k1_zfmisc_1 @ 
% 1.36/1.56            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))),
% 1.36/1.56      inference('clc', [status(thm)], ['36', '37'])).
% 1.36/1.56  thf('39', plain, (~ (v2_struct_0 @ sk_B)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('40', plain,
% 1.36/1.56      ((m1_subset_1 @ 
% 1.36/1.56        (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ 
% 1.36/1.56         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)) @ 
% 1.36/1.56        (k1_zfmisc_1 @ 
% 1.36/1.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 1.36/1.56      inference('clc', [status(thm)], ['38', '39'])).
% 1.36/1.56  thf(redefinition_r2_funct_2, axiom,
% 1.36/1.56    (![A:$i,B:$i,C:$i,D:$i]:
% 1.36/1.56     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.36/1.56         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.36/1.56         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.36/1.56         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.36/1.56       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.36/1.56  thf('41', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.36/1.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 1.36/1.56          | ~ (v1_funct_2 @ X0 @ X1 @ X2)
% 1.36/1.56          | ~ (v1_funct_1 @ X0)
% 1.36/1.56          | ~ (v1_funct_1 @ X3)
% 1.36/1.56          | ~ (v1_funct_2 @ X3 @ X1 @ X2)
% 1.36/1.56          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 1.36/1.56          | ((X0) = (X3))
% 1.36/1.56          | ~ (r2_funct_2 @ X1 @ X2 @ X0 @ X3))),
% 1.36/1.56      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 1.36/1.56  thf('42', plain,
% 1.36/1.56      (![X0 : $i]:
% 1.36/1.56         (~ (r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 1.36/1.56             (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ 
% 1.36/1.56              (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)) @ 
% 1.36/1.56             X0)
% 1.36/1.56          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ 
% 1.36/1.56              (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)) = (X0))
% 1.36/1.56          | ~ (m1_subset_1 @ X0 @ 
% 1.36/1.56               (k1_zfmisc_1 @ 
% 1.36/1.56                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 1.36/1.56          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 1.36/1.56          | ~ (v1_funct_1 @ X0)
% 1.36/1.56          | ~ (v1_funct_1 @ 
% 1.36/1.56               (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ 
% 1.36/1.56                (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)))
% 1.36/1.56          | ~ (v1_funct_2 @ 
% 1.36/1.56               (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ 
% 1.36/1.56                (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)) @ 
% 1.36/1.56               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))),
% 1.36/1.56      inference('sup-', [status(thm)], ['40', '41'])).
% 1.36/1.56  thf('43', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('44', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('45', plain,
% 1.36/1.56      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 1.36/1.56        (k1_zfmisc_1 @ 
% 1.36/1.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('46', plain,
% 1.36/1.56      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 1.36/1.56         (~ (m1_pre_topc @ X4 @ X5)
% 1.36/1.56          | ~ (m1_pre_topc @ X6 @ X5)
% 1.36/1.56          | ~ (l1_pre_topc @ X7)
% 1.36/1.56          | ~ (v2_pre_topc @ X7)
% 1.36/1.56          | (v2_struct_0 @ X7)
% 1.36/1.56          | ~ (l1_pre_topc @ X5)
% 1.36/1.56          | ~ (v2_pre_topc @ X5)
% 1.36/1.56          | (v2_struct_0 @ X5)
% 1.36/1.56          | ~ (v1_funct_1 @ X8)
% 1.36/1.56          | ~ (v1_funct_2 @ X8 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X7))
% 1.36/1.56          | ~ (m1_subset_1 @ X8 @ 
% 1.36/1.56               (k1_zfmisc_1 @ 
% 1.36/1.56                (k2_zfmisc_1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X7))))
% 1.36/1.56          | (v1_funct_1 @ (k3_tmap_1 @ X5 @ X7 @ X6 @ X4 @ X8)))),
% 1.36/1.56      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 1.36/1.56  thf('47', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         ((v1_funct_1 @ 
% 1.36/1.56           (k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ 
% 1.36/1.56            (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)))
% 1.36/1.56          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 1.36/1.56               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.36/1.56          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F))
% 1.36/1.56          | (v2_struct_0 @ X1)
% 1.36/1.56          | ~ (v2_pre_topc @ X1)
% 1.36/1.56          | ~ (l1_pre_topc @ X1)
% 1.36/1.56          | (v2_struct_0 @ sk_B)
% 1.36/1.56          | ~ (v2_pre_topc @ sk_B)
% 1.36/1.56          | ~ (l1_pre_topc @ sk_B)
% 1.36/1.56          | ~ (m1_pre_topc @ sk_C @ X1)
% 1.36/1.56          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.36/1.56      inference('sup-', [status(thm)], ['45', '46'])).
% 1.36/1.56  thf('48', plain,
% 1.36/1.56      ((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 1.36/1.56        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('49', plain,
% 1.36/1.56      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F))),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('50', plain, ((v2_pre_topc @ sk_B)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('51', plain, ((l1_pre_topc @ sk_B)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('52', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         ((v1_funct_1 @ 
% 1.36/1.56           (k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ 
% 1.36/1.56            (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)))
% 1.36/1.56          | (v2_struct_0 @ X1)
% 1.36/1.56          | ~ (v2_pre_topc @ X1)
% 1.36/1.56          | ~ (l1_pre_topc @ X1)
% 1.36/1.56          | (v2_struct_0 @ sk_B)
% 1.36/1.56          | ~ (m1_pre_topc @ sk_C @ X1)
% 1.36/1.56          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.36/1.56      inference('demod', [status(thm)], ['47', '48', '49', '50', '51'])).
% 1.36/1.56  thf('53', plain,
% 1.36/1.56      (![X0 : $i]:
% 1.36/1.56         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.36/1.56          | (v2_struct_0 @ sk_B)
% 1.36/1.56          | ~ (l1_pre_topc @ sk_A)
% 1.36/1.56          | ~ (v2_pre_topc @ sk_A)
% 1.36/1.56          | (v2_struct_0 @ sk_A)
% 1.36/1.56          | (v1_funct_1 @ 
% 1.36/1.56             (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ 
% 1.36/1.56              (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F))))),
% 1.36/1.56      inference('sup-', [status(thm)], ['44', '52'])).
% 1.36/1.56  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('55', plain, ((v2_pre_topc @ sk_A)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('56', plain,
% 1.36/1.56      (![X0 : $i]:
% 1.36/1.56         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.36/1.56          | (v2_struct_0 @ sk_B)
% 1.36/1.56          | (v2_struct_0 @ sk_A)
% 1.36/1.56          | (v1_funct_1 @ 
% 1.36/1.56             (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ 
% 1.36/1.56              (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F))))),
% 1.36/1.56      inference('demod', [status(thm)], ['53', '54', '55'])).
% 1.36/1.56  thf('57', plain,
% 1.36/1.56      (((v1_funct_1 @ 
% 1.36/1.56         (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ 
% 1.36/1.56          (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)))
% 1.36/1.56        | (v2_struct_0 @ sk_A)
% 1.36/1.56        | (v2_struct_0 @ sk_B))),
% 1.36/1.56      inference('sup-', [status(thm)], ['43', '56'])).
% 1.36/1.56  thf('58', plain, (~ (v2_struct_0 @ sk_A)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('59', plain,
% 1.36/1.56      (((v2_struct_0 @ sk_B)
% 1.36/1.56        | (v1_funct_1 @ 
% 1.36/1.56           (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ 
% 1.36/1.56            (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F))))),
% 1.36/1.56      inference('clc', [status(thm)], ['57', '58'])).
% 1.36/1.56  thf('60', plain, (~ (v2_struct_0 @ sk_B)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('61', plain,
% 1.36/1.56      ((v1_funct_1 @ 
% 1.36/1.56        (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ 
% 1.36/1.56         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)))),
% 1.36/1.56      inference('clc', [status(thm)], ['59', '60'])).
% 1.36/1.56  thf('62', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('63', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('64', plain,
% 1.36/1.56      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 1.36/1.56        (k1_zfmisc_1 @ 
% 1.36/1.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('65', plain,
% 1.36/1.56      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 1.36/1.56         (~ (m1_pre_topc @ X4 @ X5)
% 1.36/1.56          | ~ (m1_pre_topc @ X6 @ X5)
% 1.36/1.56          | ~ (l1_pre_topc @ X7)
% 1.36/1.56          | ~ (v2_pre_topc @ X7)
% 1.36/1.56          | (v2_struct_0 @ X7)
% 1.36/1.56          | ~ (l1_pre_topc @ X5)
% 1.36/1.56          | ~ (v2_pre_topc @ X5)
% 1.36/1.56          | (v2_struct_0 @ X5)
% 1.36/1.56          | ~ (v1_funct_1 @ X8)
% 1.36/1.56          | ~ (v1_funct_2 @ X8 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X7))
% 1.36/1.56          | ~ (m1_subset_1 @ X8 @ 
% 1.36/1.56               (k1_zfmisc_1 @ 
% 1.36/1.56                (k2_zfmisc_1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X7))))
% 1.36/1.56          | (v1_funct_2 @ (k3_tmap_1 @ X5 @ X7 @ X6 @ X4 @ X8) @ 
% 1.36/1.56             (u1_struct_0 @ X4) @ (u1_struct_0 @ X7)))),
% 1.36/1.56      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 1.36/1.56  thf('66', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         ((v1_funct_2 @ 
% 1.36/1.56           (k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ 
% 1.36/1.56            (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)) @ 
% 1.36/1.56           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.36/1.56          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 1.36/1.56               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.36/1.56          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F))
% 1.36/1.56          | (v2_struct_0 @ X1)
% 1.36/1.56          | ~ (v2_pre_topc @ X1)
% 1.36/1.56          | ~ (l1_pre_topc @ X1)
% 1.36/1.56          | (v2_struct_0 @ sk_B)
% 1.36/1.56          | ~ (v2_pre_topc @ sk_B)
% 1.36/1.56          | ~ (l1_pre_topc @ sk_B)
% 1.36/1.56          | ~ (m1_pre_topc @ sk_C @ X1)
% 1.36/1.56          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.36/1.56      inference('sup-', [status(thm)], ['64', '65'])).
% 1.36/1.56  thf('67', plain,
% 1.36/1.56      ((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 1.36/1.56        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('68', plain,
% 1.36/1.56      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F))),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('69', plain, ((v2_pre_topc @ sk_B)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('70', plain, ((l1_pre_topc @ sk_B)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('71', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         ((v1_funct_2 @ 
% 1.36/1.56           (k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ 
% 1.36/1.56            (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)) @ 
% 1.36/1.56           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.36/1.56          | (v2_struct_0 @ X1)
% 1.36/1.56          | ~ (v2_pre_topc @ X1)
% 1.36/1.56          | ~ (l1_pre_topc @ X1)
% 1.36/1.56          | (v2_struct_0 @ sk_B)
% 1.36/1.56          | ~ (m1_pre_topc @ sk_C @ X1)
% 1.36/1.56          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.36/1.56      inference('demod', [status(thm)], ['66', '67', '68', '69', '70'])).
% 1.36/1.56  thf('72', plain,
% 1.36/1.56      (![X0 : $i]:
% 1.36/1.56         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.36/1.56          | (v2_struct_0 @ sk_B)
% 1.36/1.56          | ~ (l1_pre_topc @ sk_A)
% 1.36/1.56          | ~ (v2_pre_topc @ sk_A)
% 1.36/1.56          | (v2_struct_0 @ sk_A)
% 1.36/1.56          | (v1_funct_2 @ 
% 1.36/1.56             (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ 
% 1.36/1.56              (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)) @ 
% 1.36/1.56             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 1.36/1.56      inference('sup-', [status(thm)], ['63', '71'])).
% 1.36/1.56  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('74', plain, ((v2_pre_topc @ sk_A)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('75', plain,
% 1.36/1.56      (![X0 : $i]:
% 1.36/1.56         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.36/1.56          | (v2_struct_0 @ sk_B)
% 1.36/1.56          | (v2_struct_0 @ sk_A)
% 1.36/1.56          | (v1_funct_2 @ 
% 1.36/1.56             (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ 
% 1.36/1.56              (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)) @ 
% 1.36/1.56             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 1.36/1.56      inference('demod', [status(thm)], ['72', '73', '74'])).
% 1.36/1.56  thf('76', plain,
% 1.36/1.56      (((v1_funct_2 @ 
% 1.36/1.56         (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ 
% 1.36/1.56          (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)) @ 
% 1.36/1.56         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 1.36/1.56        | (v2_struct_0 @ sk_A)
% 1.36/1.56        | (v2_struct_0 @ sk_B))),
% 1.36/1.56      inference('sup-', [status(thm)], ['62', '75'])).
% 1.36/1.56  thf('77', plain, (~ (v2_struct_0 @ sk_A)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('78', plain,
% 1.36/1.56      (((v2_struct_0 @ sk_B)
% 1.36/1.56        | (v1_funct_2 @ 
% 1.36/1.56           (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ 
% 1.36/1.56            (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)) @ 
% 1.36/1.56           (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))),
% 1.36/1.56      inference('clc', [status(thm)], ['76', '77'])).
% 1.36/1.56  thf('79', plain, (~ (v2_struct_0 @ sk_B)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('80', plain,
% 1.36/1.56      ((v1_funct_2 @ 
% 1.36/1.56        (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ 
% 1.36/1.56         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)) @ 
% 1.36/1.56        (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))),
% 1.36/1.56      inference('clc', [status(thm)], ['78', '79'])).
% 1.36/1.56  thf('81', plain,
% 1.36/1.56      (![X0 : $i]:
% 1.36/1.56         (~ (r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 1.36/1.56             (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ 
% 1.36/1.56              (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)) @ 
% 1.36/1.56             X0)
% 1.36/1.56          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ 
% 1.36/1.56              (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)) = (X0))
% 1.36/1.56          | ~ (m1_subset_1 @ X0 @ 
% 1.36/1.56               (k1_zfmisc_1 @ 
% 1.36/1.56                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 1.36/1.56          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 1.36/1.56          | ~ (v1_funct_1 @ X0))),
% 1.36/1.56      inference('demod', [status(thm)], ['42', '61', '80'])).
% 1.36/1.56  thf('82', plain,
% 1.36/1.56      (((v2_struct_0 @ sk_A)
% 1.36/1.56        | (v2_struct_0 @ sk_D)
% 1.36/1.56        | (v2_struct_0 @ sk_E)
% 1.36/1.56        | (v2_struct_0 @ sk_C)
% 1.36/1.56        | (v2_struct_0 @ sk_B)
% 1.36/1.56        | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F))
% 1.36/1.56        | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 1.36/1.56             (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 1.36/1.56        | ~ (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 1.36/1.56             (k1_zfmisc_1 @ 
% 1.36/1.56              (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 1.36/1.56        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ 
% 1.36/1.56            (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F))
% 1.36/1.56            = (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F)))),
% 1.36/1.56      inference('sup-', [status(thm)], ['21', '81'])).
% 1.36/1.56  thf('83', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('84', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('85', plain,
% 1.36/1.56      ((m1_subset_1 @ sk_F @ 
% 1.36/1.56        (k1_zfmisc_1 @ 
% 1.36/1.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('86', plain,
% 1.36/1.56      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 1.36/1.56         (~ (m1_pre_topc @ X4 @ X5)
% 1.36/1.56          | ~ (m1_pre_topc @ X6 @ X5)
% 1.36/1.56          | ~ (l1_pre_topc @ X7)
% 1.36/1.56          | ~ (v2_pre_topc @ X7)
% 1.36/1.56          | (v2_struct_0 @ X7)
% 1.36/1.56          | ~ (l1_pre_topc @ X5)
% 1.36/1.56          | ~ (v2_pre_topc @ X5)
% 1.36/1.56          | (v2_struct_0 @ X5)
% 1.36/1.56          | ~ (v1_funct_1 @ X8)
% 1.36/1.56          | ~ (v1_funct_2 @ X8 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X7))
% 1.36/1.56          | ~ (m1_subset_1 @ X8 @ 
% 1.36/1.56               (k1_zfmisc_1 @ 
% 1.36/1.56                (k2_zfmisc_1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X7))))
% 1.36/1.56          | (v1_funct_1 @ (k3_tmap_1 @ X5 @ X7 @ X6 @ X4 @ X8)))),
% 1.36/1.56      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 1.36/1.56  thf('87', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_F))
% 1.36/1.56          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.36/1.56          | ~ (v1_funct_1 @ sk_F)
% 1.36/1.56          | (v2_struct_0 @ X1)
% 1.36/1.56          | ~ (v2_pre_topc @ X1)
% 1.36/1.56          | ~ (l1_pre_topc @ X1)
% 1.36/1.56          | (v2_struct_0 @ sk_B)
% 1.36/1.56          | ~ (v2_pre_topc @ sk_B)
% 1.36/1.56          | ~ (l1_pre_topc @ sk_B)
% 1.36/1.56          | ~ (m1_pre_topc @ sk_D @ X1)
% 1.36/1.56          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.36/1.56      inference('sup-', [status(thm)], ['85', '86'])).
% 1.36/1.56  thf('88', plain,
% 1.36/1.56      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('89', plain, ((v1_funct_1 @ sk_F)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('90', plain, ((v2_pre_topc @ sk_B)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('91', plain, ((l1_pre_topc @ sk_B)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('92', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_F))
% 1.36/1.56          | (v2_struct_0 @ X1)
% 1.36/1.56          | ~ (v2_pre_topc @ X1)
% 1.36/1.56          | ~ (l1_pre_topc @ X1)
% 1.36/1.56          | (v2_struct_0 @ sk_B)
% 1.36/1.56          | ~ (m1_pre_topc @ sk_D @ X1)
% 1.36/1.56          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.36/1.56      inference('demod', [status(thm)], ['87', '88', '89', '90', '91'])).
% 1.36/1.56  thf('93', plain,
% 1.36/1.56      (![X0 : $i]:
% 1.36/1.56         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.36/1.56          | (v2_struct_0 @ sk_B)
% 1.36/1.56          | ~ (l1_pre_topc @ sk_A)
% 1.36/1.56          | ~ (v2_pre_topc @ sk_A)
% 1.36/1.56          | (v2_struct_0 @ sk_A)
% 1.36/1.56          | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F)))),
% 1.36/1.56      inference('sup-', [status(thm)], ['84', '92'])).
% 1.36/1.56  thf('94', plain, ((l1_pre_topc @ sk_A)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('95', plain, ((v2_pre_topc @ sk_A)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('96', plain,
% 1.36/1.56      (![X0 : $i]:
% 1.36/1.56         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.36/1.56          | (v2_struct_0 @ sk_B)
% 1.36/1.56          | (v2_struct_0 @ sk_A)
% 1.36/1.56          | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F)))),
% 1.36/1.56      inference('demod', [status(thm)], ['93', '94', '95'])).
% 1.36/1.56  thf('97', plain,
% 1.36/1.56      (((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F))
% 1.36/1.56        | (v2_struct_0 @ sk_A)
% 1.36/1.56        | (v2_struct_0 @ sk_B))),
% 1.36/1.56      inference('sup-', [status(thm)], ['83', '96'])).
% 1.36/1.56  thf('98', plain, (~ (v2_struct_0 @ sk_A)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('99', plain,
% 1.36/1.56      (((v2_struct_0 @ sk_B)
% 1.36/1.56        | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F)))),
% 1.36/1.56      inference('clc', [status(thm)], ['97', '98'])).
% 1.36/1.56  thf('100', plain, (~ (v2_struct_0 @ sk_B)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('101', plain,
% 1.36/1.56      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F))),
% 1.36/1.56      inference('clc', [status(thm)], ['99', '100'])).
% 1.36/1.56  thf('102', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('103', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('104', plain,
% 1.36/1.56      ((m1_subset_1 @ sk_F @ 
% 1.36/1.56        (k1_zfmisc_1 @ 
% 1.36/1.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('105', plain,
% 1.36/1.56      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 1.36/1.56         (~ (m1_pre_topc @ X4 @ X5)
% 1.36/1.56          | ~ (m1_pre_topc @ X6 @ X5)
% 1.36/1.56          | ~ (l1_pre_topc @ X7)
% 1.36/1.56          | ~ (v2_pre_topc @ X7)
% 1.36/1.56          | (v2_struct_0 @ X7)
% 1.36/1.56          | ~ (l1_pre_topc @ X5)
% 1.36/1.56          | ~ (v2_pre_topc @ X5)
% 1.36/1.56          | (v2_struct_0 @ X5)
% 1.36/1.56          | ~ (v1_funct_1 @ X8)
% 1.36/1.56          | ~ (v1_funct_2 @ X8 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X7))
% 1.36/1.56          | ~ (m1_subset_1 @ X8 @ 
% 1.36/1.56               (k1_zfmisc_1 @ 
% 1.36/1.56                (k2_zfmisc_1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X7))))
% 1.36/1.56          | (v1_funct_2 @ (k3_tmap_1 @ X5 @ X7 @ X6 @ X4 @ X8) @ 
% 1.36/1.56             (u1_struct_0 @ X4) @ (u1_struct_0 @ X7)))),
% 1.36/1.56      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 1.36/1.56  thf('106', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_F) @ 
% 1.36/1.56           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.36/1.56          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.36/1.56          | ~ (v1_funct_1 @ sk_F)
% 1.36/1.56          | (v2_struct_0 @ X1)
% 1.36/1.56          | ~ (v2_pre_topc @ X1)
% 1.36/1.56          | ~ (l1_pre_topc @ X1)
% 1.36/1.56          | (v2_struct_0 @ sk_B)
% 1.36/1.56          | ~ (v2_pre_topc @ sk_B)
% 1.36/1.56          | ~ (l1_pre_topc @ sk_B)
% 1.36/1.56          | ~ (m1_pre_topc @ sk_D @ X1)
% 1.36/1.56          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.36/1.56      inference('sup-', [status(thm)], ['104', '105'])).
% 1.36/1.56  thf('107', plain,
% 1.36/1.56      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('108', plain, ((v1_funct_1 @ sk_F)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('109', plain, ((v2_pre_topc @ sk_B)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('110', plain, ((l1_pre_topc @ sk_B)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('111', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_F) @ 
% 1.36/1.56           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.36/1.56          | (v2_struct_0 @ X1)
% 1.36/1.56          | ~ (v2_pre_topc @ X1)
% 1.36/1.56          | ~ (l1_pre_topc @ X1)
% 1.36/1.56          | (v2_struct_0 @ sk_B)
% 1.36/1.56          | ~ (m1_pre_topc @ sk_D @ X1)
% 1.36/1.56          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.36/1.56      inference('demod', [status(thm)], ['106', '107', '108', '109', '110'])).
% 1.36/1.56  thf('112', plain,
% 1.36/1.56      (![X0 : $i]:
% 1.36/1.56         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.36/1.56          | (v2_struct_0 @ sk_B)
% 1.36/1.56          | ~ (l1_pre_topc @ sk_A)
% 1.36/1.56          | ~ (v2_pre_topc @ sk_A)
% 1.36/1.56          | (v2_struct_0 @ sk_A)
% 1.36/1.56          | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F) @ 
% 1.36/1.56             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 1.36/1.56      inference('sup-', [status(thm)], ['103', '111'])).
% 1.36/1.56  thf('113', plain, ((l1_pre_topc @ sk_A)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('114', plain, ((v2_pre_topc @ sk_A)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('115', plain,
% 1.36/1.56      (![X0 : $i]:
% 1.36/1.56         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.36/1.56          | (v2_struct_0 @ sk_B)
% 1.36/1.56          | (v2_struct_0 @ sk_A)
% 1.36/1.56          | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F) @ 
% 1.36/1.56             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 1.36/1.56      inference('demod', [status(thm)], ['112', '113', '114'])).
% 1.36/1.56  thf('116', plain,
% 1.36/1.56      (((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 1.36/1.56         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 1.36/1.56        | (v2_struct_0 @ sk_A)
% 1.36/1.56        | (v2_struct_0 @ sk_B))),
% 1.36/1.56      inference('sup-', [status(thm)], ['102', '115'])).
% 1.36/1.56  thf('117', plain, (~ (v2_struct_0 @ sk_A)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('118', plain,
% 1.36/1.56      (((v2_struct_0 @ sk_B)
% 1.36/1.56        | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 1.36/1.56           (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))),
% 1.36/1.56      inference('clc', [status(thm)], ['116', '117'])).
% 1.36/1.56  thf('119', plain, (~ (v2_struct_0 @ sk_B)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('120', plain,
% 1.36/1.56      ((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 1.36/1.56        (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))),
% 1.36/1.56      inference('clc', [status(thm)], ['118', '119'])).
% 1.36/1.56  thf('121', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('122', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('123', plain,
% 1.36/1.56      ((m1_subset_1 @ sk_F @ 
% 1.36/1.56        (k1_zfmisc_1 @ 
% 1.36/1.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('124', plain,
% 1.36/1.56      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 1.36/1.56         (~ (m1_pre_topc @ X4 @ X5)
% 1.36/1.56          | ~ (m1_pre_topc @ X6 @ X5)
% 1.36/1.56          | ~ (l1_pre_topc @ X7)
% 1.36/1.56          | ~ (v2_pre_topc @ X7)
% 1.36/1.56          | (v2_struct_0 @ X7)
% 1.36/1.56          | ~ (l1_pre_topc @ X5)
% 1.36/1.56          | ~ (v2_pre_topc @ X5)
% 1.36/1.56          | (v2_struct_0 @ X5)
% 1.36/1.56          | ~ (v1_funct_1 @ X8)
% 1.36/1.56          | ~ (v1_funct_2 @ X8 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X7))
% 1.36/1.56          | ~ (m1_subset_1 @ X8 @ 
% 1.36/1.56               (k1_zfmisc_1 @ 
% 1.36/1.56                (k2_zfmisc_1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X7))))
% 1.36/1.56          | (m1_subset_1 @ (k3_tmap_1 @ X5 @ X7 @ X6 @ X4 @ X8) @ 
% 1.36/1.56             (k1_zfmisc_1 @ 
% 1.36/1.56              (k2_zfmisc_1 @ (u1_struct_0 @ X4) @ (u1_struct_0 @ X7)))))),
% 1.36/1.56      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 1.36/1.56  thf('125', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_F) @ 
% 1.36/1.56           (k1_zfmisc_1 @ 
% 1.36/1.56            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.36/1.56          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.36/1.56          | ~ (v1_funct_1 @ sk_F)
% 1.36/1.56          | (v2_struct_0 @ X1)
% 1.36/1.56          | ~ (v2_pre_topc @ X1)
% 1.36/1.56          | ~ (l1_pre_topc @ X1)
% 1.36/1.56          | (v2_struct_0 @ sk_B)
% 1.36/1.56          | ~ (v2_pre_topc @ sk_B)
% 1.36/1.56          | ~ (l1_pre_topc @ sk_B)
% 1.36/1.56          | ~ (m1_pre_topc @ sk_D @ X1)
% 1.36/1.56          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.36/1.56      inference('sup-', [status(thm)], ['123', '124'])).
% 1.36/1.56  thf('126', plain,
% 1.36/1.56      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('127', plain, ((v1_funct_1 @ sk_F)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('128', plain, ((v2_pre_topc @ sk_B)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('129', plain, ((l1_pre_topc @ sk_B)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('130', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_F) @ 
% 1.36/1.56           (k1_zfmisc_1 @ 
% 1.36/1.56            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.36/1.56          | (v2_struct_0 @ X1)
% 1.36/1.56          | ~ (v2_pre_topc @ X1)
% 1.36/1.56          | ~ (l1_pre_topc @ X1)
% 1.36/1.56          | (v2_struct_0 @ sk_B)
% 1.36/1.56          | ~ (m1_pre_topc @ sk_D @ X1)
% 1.36/1.56          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.36/1.56      inference('demod', [status(thm)], ['125', '126', '127', '128', '129'])).
% 1.36/1.56  thf('131', plain,
% 1.36/1.56      (![X0 : $i]:
% 1.36/1.56         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.36/1.56          | (v2_struct_0 @ sk_B)
% 1.36/1.56          | ~ (l1_pre_topc @ sk_A)
% 1.36/1.56          | ~ (v2_pre_topc @ sk_A)
% 1.36/1.56          | (v2_struct_0 @ sk_A)
% 1.36/1.56          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F) @ 
% 1.36/1.56             (k1_zfmisc_1 @ 
% 1.36/1.56              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 1.36/1.56      inference('sup-', [status(thm)], ['122', '130'])).
% 1.36/1.56  thf('132', plain, ((l1_pre_topc @ sk_A)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('133', plain, ((v2_pre_topc @ sk_A)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('134', plain,
% 1.36/1.56      (![X0 : $i]:
% 1.36/1.56         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.36/1.56          | (v2_struct_0 @ sk_B)
% 1.36/1.56          | (v2_struct_0 @ sk_A)
% 1.36/1.56          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F) @ 
% 1.36/1.56             (k1_zfmisc_1 @ 
% 1.36/1.56              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 1.36/1.56      inference('demod', [status(thm)], ['131', '132', '133'])).
% 1.36/1.56  thf('135', plain,
% 1.36/1.56      (((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 1.36/1.56         (k1_zfmisc_1 @ 
% 1.36/1.56          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 1.36/1.56        | (v2_struct_0 @ sk_A)
% 1.36/1.56        | (v2_struct_0 @ sk_B))),
% 1.36/1.56      inference('sup-', [status(thm)], ['121', '134'])).
% 1.36/1.56  thf('136', plain, (~ (v2_struct_0 @ sk_A)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('137', plain,
% 1.36/1.56      (((v2_struct_0 @ sk_B)
% 1.36/1.56        | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 1.36/1.56           (k1_zfmisc_1 @ 
% 1.36/1.56            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))),
% 1.36/1.56      inference('clc', [status(thm)], ['135', '136'])).
% 1.36/1.56  thf('138', plain, (~ (v2_struct_0 @ sk_B)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('139', plain,
% 1.36/1.56      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 1.36/1.56        (k1_zfmisc_1 @ 
% 1.36/1.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 1.36/1.56      inference('clc', [status(thm)], ['137', '138'])).
% 1.36/1.56  thf('140', plain,
% 1.36/1.56      (((v2_struct_0 @ sk_A)
% 1.36/1.56        | (v2_struct_0 @ sk_D)
% 1.36/1.56        | (v2_struct_0 @ sk_E)
% 1.36/1.56        | (v2_struct_0 @ sk_C)
% 1.36/1.56        | (v2_struct_0 @ sk_B)
% 1.36/1.56        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ 
% 1.36/1.56            (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F))
% 1.36/1.56            = (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F)))),
% 1.36/1.56      inference('demod', [status(thm)], ['82', '101', '120', '139'])).
% 1.36/1.56  thf('141', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('142', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('143', plain,
% 1.36/1.56      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 1.36/1.56        (k1_zfmisc_1 @ 
% 1.36/1.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf(t89_tmap_1, axiom,
% 1.36/1.56    (![A:$i]:
% 1.36/1.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.36/1.56       ( ![B:$i]:
% 1.36/1.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.36/1.56             ( l1_pre_topc @ B ) ) =>
% 1.36/1.56           ( ![C:$i]:
% 1.36/1.56             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.36/1.56               ( ![D:$i]:
% 1.36/1.56                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.36/1.56                   ( ![E:$i]:
% 1.36/1.56                     ( ( ( v1_funct_1 @ E ) & 
% 1.36/1.56                         ( v1_funct_2 @
% 1.36/1.56                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.36/1.56                         ( v5_pre_topc @ E @ C @ B ) & 
% 1.36/1.56                         ( m1_subset_1 @
% 1.36/1.56                           E @ 
% 1.36/1.56                           ( k1_zfmisc_1 @
% 1.36/1.56                             ( k2_zfmisc_1 @
% 1.36/1.56                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.36/1.56                       ( ( m1_pre_topc @ D @ C ) =>
% 1.36/1.56                         ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) ) & 
% 1.36/1.56                           ( v1_funct_2 @
% 1.36/1.56                             ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 1.36/1.56                             ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 1.36/1.56                           ( v5_pre_topc @
% 1.36/1.56                             ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ D @ B ) & 
% 1.36/1.56                           ( m1_subset_1 @
% 1.36/1.56                             ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 1.36/1.56                             ( k1_zfmisc_1 @
% 1.36/1.56                               ( k2_zfmisc_1 @
% 1.36/1.56                                 ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.36/1.56  thf('144', plain,
% 1.36/1.56      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 1.36/1.56         ((v2_struct_0 @ X15)
% 1.36/1.56          | ~ (v2_pre_topc @ X15)
% 1.36/1.56          | ~ (l1_pre_topc @ X15)
% 1.36/1.56          | (v2_struct_0 @ X16)
% 1.36/1.56          | ~ (m1_pre_topc @ X16 @ X17)
% 1.36/1.56          | ~ (m1_pre_topc @ X16 @ X18)
% 1.36/1.56          | (v5_pre_topc @ (k3_tmap_1 @ X17 @ X15 @ X18 @ X16 @ X19) @ X16 @ 
% 1.36/1.56             X15)
% 1.36/1.56          | ~ (m1_subset_1 @ X19 @ 
% 1.36/1.56               (k1_zfmisc_1 @ 
% 1.36/1.56                (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X15))))
% 1.36/1.56          | ~ (v5_pre_topc @ X19 @ X18 @ X15)
% 1.36/1.56          | ~ (v1_funct_2 @ X19 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X15))
% 1.36/1.56          | ~ (v1_funct_1 @ X19)
% 1.36/1.56          | ~ (m1_pre_topc @ X18 @ X17)
% 1.36/1.56          | (v2_struct_0 @ X18)
% 1.36/1.56          | ~ (l1_pre_topc @ X17)
% 1.36/1.56          | ~ (v2_pre_topc @ X17)
% 1.36/1.56          | (v2_struct_0 @ X17))),
% 1.36/1.56      inference('cnf', [status(esa)], [t89_tmap_1])).
% 1.36/1.56  thf('145', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         ((v2_struct_0 @ X0)
% 1.36/1.56          | ~ (v2_pre_topc @ X0)
% 1.36/1.56          | ~ (l1_pre_topc @ X0)
% 1.36/1.56          | (v2_struct_0 @ sk_C)
% 1.36/1.56          | ~ (m1_pre_topc @ sk_C @ X0)
% 1.36/1.56          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F))
% 1.36/1.56          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 1.36/1.56               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.36/1.56          | ~ (v5_pre_topc @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 1.36/1.56               sk_C @ sk_B)
% 1.36/1.56          | (v5_pre_topc @ 
% 1.36/1.56             (k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ 
% 1.36/1.56              (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)) @ 
% 1.36/1.56             X1 @ sk_B)
% 1.36/1.56          | ~ (m1_pre_topc @ X1 @ sk_C)
% 1.36/1.56          | ~ (m1_pre_topc @ X1 @ X0)
% 1.36/1.56          | (v2_struct_0 @ X1)
% 1.36/1.56          | ~ (l1_pre_topc @ sk_B)
% 1.36/1.56          | ~ (v2_pre_topc @ sk_B)
% 1.36/1.56          | (v2_struct_0 @ sk_B))),
% 1.36/1.56      inference('sup-', [status(thm)], ['143', '144'])).
% 1.36/1.56  thf('146', plain,
% 1.36/1.56      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F))),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('147', plain,
% 1.36/1.56      ((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 1.36/1.56        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('148', plain,
% 1.36/1.56      ((v5_pre_topc @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ sk_C @ 
% 1.36/1.56        sk_B)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('149', plain, ((l1_pre_topc @ sk_B)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('150', plain, ((v2_pre_topc @ sk_B)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('151', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         ((v2_struct_0 @ X0)
% 1.36/1.56          | ~ (v2_pre_topc @ X0)
% 1.36/1.56          | ~ (l1_pre_topc @ X0)
% 1.36/1.56          | (v2_struct_0 @ sk_C)
% 1.36/1.56          | ~ (m1_pre_topc @ sk_C @ X0)
% 1.36/1.56          | (v5_pre_topc @ 
% 1.36/1.56             (k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ 
% 1.36/1.56              (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)) @ 
% 1.36/1.56             X1 @ sk_B)
% 1.36/1.56          | ~ (m1_pre_topc @ X1 @ sk_C)
% 1.36/1.56          | ~ (m1_pre_topc @ X1 @ X0)
% 1.36/1.56          | (v2_struct_0 @ X1)
% 1.36/1.56          | (v2_struct_0 @ sk_B))),
% 1.36/1.56      inference('demod', [status(thm)],
% 1.36/1.56                ['145', '146', '147', '148', '149', '150'])).
% 1.36/1.56  thf('152', plain,
% 1.36/1.56      (![X0 : $i]:
% 1.36/1.56         ((v2_struct_0 @ sk_B)
% 1.36/1.56          | (v2_struct_0 @ X0)
% 1.36/1.56          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.36/1.56          | ~ (m1_pre_topc @ X0 @ sk_C)
% 1.36/1.56          | (v5_pre_topc @ 
% 1.36/1.56             (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ 
% 1.36/1.56              (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)) @ 
% 1.36/1.56             X0 @ sk_B)
% 1.36/1.56          | (v2_struct_0 @ sk_C)
% 1.36/1.56          | ~ (l1_pre_topc @ sk_A)
% 1.36/1.56          | ~ (v2_pre_topc @ sk_A)
% 1.36/1.56          | (v2_struct_0 @ sk_A))),
% 1.36/1.56      inference('sup-', [status(thm)], ['142', '151'])).
% 1.36/1.56  thf('153', plain, ((l1_pre_topc @ sk_A)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('154', plain, ((v2_pre_topc @ sk_A)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('155', plain,
% 1.36/1.56      (![X0 : $i]:
% 1.36/1.56         ((v2_struct_0 @ sk_B)
% 1.36/1.56          | (v2_struct_0 @ X0)
% 1.36/1.56          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.36/1.56          | ~ (m1_pre_topc @ X0 @ sk_C)
% 1.36/1.56          | (v5_pre_topc @ 
% 1.36/1.56             (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ 
% 1.36/1.56              (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)) @ 
% 1.36/1.56             X0 @ sk_B)
% 1.36/1.56          | (v2_struct_0 @ sk_C)
% 1.36/1.56          | (v2_struct_0 @ sk_A))),
% 1.36/1.56      inference('demod', [status(thm)], ['152', '153', '154'])).
% 1.36/1.56  thf('156', plain,
% 1.36/1.56      (((v2_struct_0 @ sk_A)
% 1.36/1.56        | (v2_struct_0 @ sk_C)
% 1.36/1.56        | (v5_pre_topc @ 
% 1.36/1.56           (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ 
% 1.36/1.56            (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)) @ 
% 1.36/1.56           sk_E @ sk_B)
% 1.36/1.56        | ~ (m1_pre_topc @ sk_E @ sk_C)
% 1.36/1.56        | (v2_struct_0 @ sk_E)
% 1.36/1.56        | (v2_struct_0 @ sk_B))),
% 1.36/1.56      inference('sup-', [status(thm)], ['141', '155'])).
% 1.36/1.56  thf('157', plain, ((m1_pre_topc @ sk_E @ sk_C)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('158', plain,
% 1.36/1.56      (((v2_struct_0 @ sk_A)
% 1.36/1.56        | (v2_struct_0 @ sk_C)
% 1.36/1.56        | (v5_pre_topc @ 
% 1.36/1.56           (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ 
% 1.36/1.56            (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)) @ 
% 1.36/1.56           sk_E @ sk_B)
% 1.36/1.56        | (v2_struct_0 @ sk_E)
% 1.36/1.56        | (v2_struct_0 @ sk_B))),
% 1.36/1.56      inference('demod', [status(thm)], ['156', '157'])).
% 1.36/1.56  thf('159', plain,
% 1.36/1.56      (((v5_pre_topc @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ sk_E @ 
% 1.36/1.56         sk_B)
% 1.36/1.56        | (v2_struct_0 @ sk_B)
% 1.36/1.56        | (v2_struct_0 @ sk_C)
% 1.36/1.56        | (v2_struct_0 @ sk_E)
% 1.36/1.56        | (v2_struct_0 @ sk_D)
% 1.36/1.56        | (v2_struct_0 @ sk_A)
% 1.36/1.56        | (v2_struct_0 @ sk_B)
% 1.36/1.56        | (v2_struct_0 @ sk_E)
% 1.36/1.56        | (v2_struct_0 @ sk_C)
% 1.36/1.56        | (v2_struct_0 @ sk_A))),
% 1.36/1.56      inference('sup+', [status(thm)], ['140', '158'])).
% 1.36/1.56  thf('160', plain,
% 1.36/1.56      (((v2_struct_0 @ sk_A)
% 1.36/1.56        | (v2_struct_0 @ sk_D)
% 1.36/1.56        | (v2_struct_0 @ sk_E)
% 1.36/1.56        | (v2_struct_0 @ sk_C)
% 1.36/1.56        | (v2_struct_0 @ sk_B)
% 1.36/1.56        | (v5_pre_topc @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 1.36/1.56           sk_E @ sk_B))),
% 1.36/1.56      inference('simplify', [status(thm)], ['159'])).
% 1.36/1.56  thf('161', plain,
% 1.36/1.56      ((~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F))
% 1.36/1.56        | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 1.36/1.56             (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 1.36/1.56        | ~ (v5_pre_topc @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 1.36/1.56             sk_E @ sk_B)
% 1.36/1.56        | ~ (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 1.36/1.56             (k1_zfmisc_1 @ 
% 1.36/1.56              (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('162', plain,
% 1.36/1.56      ((~ (v5_pre_topc @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 1.36/1.56           sk_E @ sk_B))
% 1.36/1.56         <= (~
% 1.36/1.56             ((v5_pre_topc @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 1.36/1.56               sk_E @ sk_B)))),
% 1.36/1.56      inference('split', [status(esa)], ['161'])).
% 1.36/1.56  thf('163', plain,
% 1.36/1.56      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 1.36/1.56        (k1_zfmisc_1 @ 
% 1.36/1.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 1.36/1.56      inference('clc', [status(thm)], ['137', '138'])).
% 1.36/1.56  thf('164', plain,
% 1.36/1.56      ((~ (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 1.36/1.56           (k1_zfmisc_1 @ 
% 1.36/1.56            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))
% 1.36/1.56         <= (~
% 1.36/1.56             ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 1.36/1.56               (k1_zfmisc_1 @ 
% 1.36/1.56                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 1.36/1.56      inference('split', [status(esa)], ['161'])).
% 1.36/1.56  thf('165', plain,
% 1.36/1.56      (((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 1.36/1.56         (k1_zfmisc_1 @ 
% 1.36/1.56          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))),
% 1.36/1.56      inference('sup-', [status(thm)], ['163', '164'])).
% 1.36/1.56  thf('166', plain,
% 1.36/1.56      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F))),
% 1.36/1.56      inference('clc', [status(thm)], ['99', '100'])).
% 1.36/1.56  thf('167', plain,
% 1.36/1.56      ((~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F)))
% 1.36/1.56         <= (~ ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F))))),
% 1.36/1.56      inference('split', [status(esa)], ['161'])).
% 1.36/1.56  thf('168', plain,
% 1.36/1.56      (((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F)))),
% 1.36/1.56      inference('sup-', [status(thm)], ['166', '167'])).
% 1.36/1.56  thf('169', plain,
% 1.36/1.56      ((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 1.36/1.56        (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))),
% 1.36/1.56      inference('clc', [status(thm)], ['118', '119'])).
% 1.36/1.56  thf('170', plain,
% 1.36/1.56      ((~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 1.36/1.56           (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))
% 1.36/1.56         <= (~
% 1.36/1.56             ((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 1.36/1.56               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 1.36/1.56      inference('split', [status(esa)], ['161'])).
% 1.36/1.56  thf('171', plain,
% 1.36/1.56      (((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 1.36/1.56         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))),
% 1.36/1.56      inference('sup-', [status(thm)], ['169', '170'])).
% 1.36/1.56  thf('172', plain,
% 1.36/1.56      (~
% 1.36/1.56       ((v5_pre_topc @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ sk_E @ 
% 1.36/1.56         sk_B)) | 
% 1.36/1.56       ~
% 1.36/1.56       ((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 1.36/1.56         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) | 
% 1.36/1.56       ~ ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F))) | 
% 1.36/1.56       ~
% 1.36/1.56       ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 1.36/1.56         (k1_zfmisc_1 @ 
% 1.36/1.56          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))),
% 1.36/1.56      inference('split', [status(esa)], ['161'])).
% 1.36/1.56  thf('173', plain,
% 1.36/1.56      (~
% 1.36/1.56       ((v5_pre_topc @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ sk_E @ 
% 1.36/1.56         sk_B))),
% 1.36/1.56      inference('sat_resolution*', [status(thm)], ['165', '168', '171', '172'])).
% 1.36/1.56  thf('174', plain,
% 1.36/1.56      (~ (v5_pre_topc @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 1.36/1.56          sk_E @ sk_B)),
% 1.36/1.56      inference('simpl_trail', [status(thm)], ['162', '173'])).
% 1.36/1.56  thf('175', plain,
% 1.36/1.56      (((v2_struct_0 @ sk_B)
% 1.36/1.56        | (v2_struct_0 @ sk_C)
% 1.36/1.56        | (v2_struct_0 @ sk_E)
% 1.36/1.56        | (v2_struct_0 @ sk_D)
% 1.36/1.56        | (v2_struct_0 @ sk_A))),
% 1.36/1.56      inference('sup-', [status(thm)], ['160', '174'])).
% 1.36/1.56  thf('176', plain, (~ (v2_struct_0 @ sk_B)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('177', plain,
% 1.36/1.56      (((v2_struct_0 @ sk_A)
% 1.36/1.56        | (v2_struct_0 @ sk_D)
% 1.36/1.56        | (v2_struct_0 @ sk_E)
% 1.36/1.56        | (v2_struct_0 @ sk_C))),
% 1.36/1.56      inference('sup-', [status(thm)], ['175', '176'])).
% 1.36/1.56  thf('178', plain, (~ (v2_struct_0 @ sk_A)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('179', plain,
% 1.36/1.56      (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D))),
% 1.36/1.56      inference('sup-', [status(thm)], ['177', '178'])).
% 1.36/1.56  thf('180', plain, (~ (v2_struct_0 @ sk_C)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('181', plain, (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_E))),
% 1.36/1.56      inference('clc', [status(thm)], ['179', '180'])).
% 1.36/1.56  thf('182', plain, (~ (v2_struct_0 @ sk_D)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('183', plain, ((v2_struct_0 @ sk_E)),
% 1.36/1.56      inference('clc', [status(thm)], ['181', '182'])).
% 1.36/1.56  thf('184', plain, ($false), inference('demod', [status(thm)], ['0', '183'])).
% 1.36/1.56  
% 1.36/1.56  % SZS output end Refutation
% 1.36/1.56  
% 1.36/1.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
