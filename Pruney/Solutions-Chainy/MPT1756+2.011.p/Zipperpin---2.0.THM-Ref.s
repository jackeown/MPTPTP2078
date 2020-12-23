%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bEzIn2AN44

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 526 expanded)
%              Number of leaves         :   31 ( 158 expanded)
%              Depth                    :   22
%              Number of atoms          : 1975 (20429 expanded)
%              Number of equality atoms :   12 ( 262 expanded)
%              Maximal formula depth    :   28 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t66_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ B ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) )
                         => ! [G: $i] :
                              ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                             => ( ( ( v3_pre_topc @ E @ B )
                                  & ( r2_hidden @ F @ E )
                                  & ( r1_tarski @ E @ ( u1_struct_0 @ D ) )
                                  & ( F = G ) )
                               => ( ( r1_tmap_1 @ B @ A @ C @ F )
                                <=> ( r1_tmap_1 @ D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) )).

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
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
               => ! [D: $i] :
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( m1_pre_topc @ D @ B ) )
                   => ! [E: $i] :
                        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) )
                           => ! [G: $i] :
                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                               => ( ( ( v3_pre_topc @ E @ B )
                                    & ( r2_hidden @ F @ E )
                                    & ( r1_tarski @ E @ ( u1_struct_0 @ D ) )
                                    & ( F = G ) )
                                 => ( ( r1_tmap_1 @ B @ A @ C @ F )
                                  <=> ( r1_tmap_1 @ D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t66_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    m1_pre_topc @ sk_D_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_D_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t8_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m1_connsp_2 @ C @ A @ B )
              <=> ? [D: $i] :
                    ( ( r2_hidden @ B @ D )
                    & ( r1_tarski @ D @ C )
                    & ( v3_pre_topc @ D @ A )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ~ ( r2_hidden @ X6 @ X9 )
      | ~ ( r1_tarski @ X9 @ X8 )
      | ~ ( v3_pre_topc @ X9 @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( m1_connsp_2 @ X8 @ X7 @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( m1_connsp_2 @ X0 @ sk_B @ X1 )
      | ~ ( v3_pre_topc @ sk_E @ sk_B )
      | ~ ( r1_tarski @ sk_E @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_E )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v3_pre_topc @ sk_E @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( m1_connsp_2 @ X0 @ sk_B @ X1 )
      | ~ ( r1_tarski @ sk_E @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_E )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['11','12','13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_E )
      | ~ ( r1_tarski @ sk_E @ ( u1_struct_0 @ sk_D_2 ) )
      | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_2 ) @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf('17',plain,(
    r1_tarski @ sk_E @ ( u1_struct_0 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_E )
      | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_2 ) @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_2 ) @ sk_B @ sk_G )
    | ~ ( r2_hidden @ sk_G @ sk_E ) ),
    inference('sup-',[status(thm)],['3','18'])).

thf('20',plain,(
    r2_hidden @ sk_F @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    r2_hidden @ sk_G @ sk_E ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_2 ) @ sk_B @ sk_G ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_connsp_2 @ ( u1_struct_0 @ sk_D_2 ) @ sk_B @ sk_G ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t7_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ~ ( ( m1_connsp_2 @ C @ A @ B )
                  & ! [D: $i] :
                      ( ( ~ ( v1_xboole_0 @ D )
                        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
                     => ~ ( ( m1_connsp_2 @ D @ A @ B )
                          & ( v3_pre_topc @ D @ A )
                          & ( r1_tarski @ D @ C ) ) ) ) ) ) ) )).

thf('27',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ( m1_subset_1 @ ( sk_D @ X5 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( m1_connsp_2 @ X5 @ X4 @ X3 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_connsp_2])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_2 ) @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_D_2 ) @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_2 ) @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_D_2 ) @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,
    ( ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_D_2 ) @ sk_G @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['25','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('34',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_D_2 ) @ sk_G @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_D_2 ) @ sk_G @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( r1_tmap_1 @ sk_D_2 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_2 ) @ sk_G )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( r1_tmap_1 @ sk_D_2 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_2 ) @ sk_G )
   <= ( r1_tmap_1 @ sk_D_2 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_2 ) @ sk_G ) ),
    inference(split,[status(esa)],['37'])).

thf('39',plain,
    ( ~ ( r1_tmap_1 @ sk_D_2 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_2 ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ~ ( r1_tmap_1 @ sk_D_2 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_2 ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D_2 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_2 ) @ sk_G ) ),
    inference(split,[status(esa)],['41'])).

thf('43',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( r1_tmap_1 @ sk_D_2 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_2 ) @ sk_G )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( r1_tmap_1 @ sk_D_2 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_2 ) @ sk_G )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G ) ),
    inference(split,[status(esa)],['46'])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t64_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ B ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                         => ( ( ( E = F )
                              & ( r1_tmap_1 @ B @ A @ C @ E ) )
                           => ( r1_tmap_1 @ D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) )).

thf('49',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_pre_topc @ X13 @ X12 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ( r1_tmap_1 @ X13 @ X15 @ ( k2_tmap_1 @ X12 @ X15 @ X16 @ X13 ) @ X14 )
      | ( X17 != X14 )
      | ~ ( r1_tmap_1 @ X12 @ X15 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X12 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X15 ) ) ) )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t64_tmap_1])).

thf('50',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X15 ) ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X12 ) )
      | ~ ( r1_tmap_1 @ X12 @ X15 @ X16 @ X14 )
      | ( r1_tmap_1 @ X13 @ X15 @ ( k2_tmap_1 @ X12 @ X15 @ X16 @ X13 ) @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_pre_topc @ X13 @ X12 )
      | ( v2_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52','53','54','55','56','57'])).

thf('59',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ sk_G )
        | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G ) ),
    inference('sup-',[status(thm)],['47','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('61',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ sk_G )
        | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_2 )
      | ~ ( m1_pre_topc @ sk_D_2 @ sk_B )
      | ( r1_tmap_1 @ sk_D_2 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_2 ) @ sk_G )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G ) ),
    inference('sup-',[status(thm)],['43','61'])).

thf('63',plain,(
    m1_pre_topc @ sk_D_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_2 )
      | ( r1_tmap_1 @ sk_D_2 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_2 ) @ sk_G )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ~ ( r1_tmap_1 @ sk_D_2 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_2 ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ~ ( r1_tmap_1 @ sk_D_2 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_2 ) @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_D_2 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_2 ) @ sk_G ) ),
    inference(split,[status(esa)],['65'])).

thf('67',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_D_2 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_2 ) @ sk_G )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G ) ) ),
    inference('sup-',[status(thm)],['64','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_2 ) )
   <= ( ~ ( r1_tmap_1 @ sk_D_2 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_2 ) @ sk_G )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( v2_struct_0 @ sk_D_2 )
   <= ( ~ ( r1_tmap_1 @ sk_D_2 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_2 ) @ sk_G )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,(
    ~ ( v2_struct_0 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( r1_tmap_1 @ sk_D_2 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_2 ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( r1_tmap_1 @ sk_D_2 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_2 ) @ sk_G )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G ) ),
    inference(split,[status(esa)],['46'])).

thf('75',plain,(
    r1_tmap_1 @ sk_D_2 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_2 ) @ sk_G ),
    inference('sat_resolution*',[status(thm)],['42','73','74'])).

thf('76',plain,(
    r1_tmap_1 @ sk_D_2 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_2 ) @ sk_G ),
    inference(simpl_trail,[status(thm)],['38','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ B ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) )
                         => ! [G: $i] :
                              ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                             => ( ( ( r1_tarski @ E @ ( u1_struct_0 @ D ) )
                                  & ( m1_connsp_2 @ E @ B @ F )
                                  & ( F = G ) )
                               => ( ( r1_tmap_1 @ B @ A @ C @ F )
                                <=> ( r1_tmap_1 @ D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) )).

thf('78',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_pre_topc @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X18 ) )
      | ~ ( r1_tarski @ X21 @ ( u1_struct_0 @ X19 ) )
      | ~ ( m1_connsp_2 @ X21 @ X18 @ X20 )
      | ( X20 != X22 )
      | ~ ( r1_tmap_1 @ X19 @ X23 @ ( k2_tmap_1 @ X18 @ X23 @ X24 @ X19 ) @ X22 )
      | ( r1_tmap_1 @ X18 @ X23 @ X24 @ X20 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X19 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( v1_funct_2 @ X24 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t65_tmap_1])).

thf('79',plain,(
    ! [X18: $i,X19: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_2 @ X24 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X19 ) )
      | ( r1_tmap_1 @ X18 @ X23 @ X24 @ X22 )
      | ~ ( r1_tmap_1 @ X19 @ X23 @ ( k2_tmap_1 @ X18 @ X23 @ X24 @ X19 ) @ X22 )
      | ~ ( m1_connsp_2 @ X21 @ X18 @ X22 )
      | ~ ( r1_tarski @ X21 @ ( u1_struct_0 @ X19 ) )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_pre_topc @ X19 @ X18 )
      | ( v2_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ X2 @ sk_B @ X1 )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['77','79'])).

thf('81',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ X2 @ sk_B @ X1 )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','81','82','83','84','85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D_2 ) )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G )
      | ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_G )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D_2 ) )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_pre_topc @ sk_D_2 @ sk_B )
      | ( v2_struct_0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['76','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('91',plain,(
    m1_pre_topc @ sk_D_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G )
      | ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_G )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D_2 ) )
      | ( v2_struct_0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['88','89','90','91'])).

thf('93',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_2 )
    | ~ ( r1_tarski @ ( sk_D @ ( u1_struct_0 @ sk_D_2 ) @ sk_G @ sk_B ) @ ( u1_struct_0 @ sk_D_2 ) )
    | ~ ( m1_connsp_2 @ ( sk_D @ ( u1_struct_0 @ sk_D_2 ) @ sk_G @ sk_B ) @ sk_B @ sk_G )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','92'])).

thf('94',plain,(
    m1_connsp_2 @ ( u1_struct_0 @ sk_D_2 ) @ sk_B @ sk_G ),
    inference(clc,[status(thm)],['23','24'])).

thf('95',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('96',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ( r1_tarski @ ( sk_D @ X5 @ X3 @ X4 ) @ X5 )
      | ~ ( m1_connsp_2 @ X5 @ X4 @ X3 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_connsp_2])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_2 ) @ sk_B @ X0 )
      | ( r1_tarski @ ( sk_D @ ( u1_struct_0 @ sk_D_2 ) @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_D_2 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_2 ) @ sk_B @ X0 )
      | ( r1_tarski @ ( sk_D @ ( u1_struct_0 @ sk_D_2 ) @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_D_2 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,
    ( ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) )
    | ( r1_tarski @ ( sk_D @ ( u1_struct_0 @ sk_D_2 ) @ sk_G @ sk_B ) @ ( u1_struct_0 @ sk_D_2 ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['94','100'])).

thf('102',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('103',plain,
    ( ( r1_tarski @ ( sk_D @ ( u1_struct_0 @ sk_D_2 ) @ sk_G @ sk_B ) @ ( u1_struct_0 @ sk_D_2 ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    r1_tarski @ ( sk_D @ ( u1_struct_0 @ sk_D_2 ) @ sk_G @ sk_B ) @ ( u1_struct_0 @ sk_D_2 ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('106',plain,(
    m1_connsp_2 @ ( u1_struct_0 @ sk_D_2 ) @ sk_B @ sk_G ),
    inference(clc,[status(thm)],['23','24'])).

thf('107',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('108',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ( m1_connsp_2 @ ( sk_D @ X5 @ X3 @ X4 ) @ X4 @ X3 )
      | ~ ( m1_connsp_2 @ X5 @ X4 @ X3 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_connsp_2])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_2 ) @ sk_B @ X0 )
      | ( m1_connsp_2 @ ( sk_D @ ( u1_struct_0 @ sk_D_2 ) @ X0 @ sk_B ) @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_2 ) @ sk_B @ X0 )
      | ( m1_connsp_2 @ ( sk_D @ ( u1_struct_0 @ sk_D_2 ) @ X0 @ sk_B ) @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,
    ( ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) )
    | ( m1_connsp_2 @ ( sk_D @ ( u1_struct_0 @ sk_D_2 ) @ sk_G @ sk_B ) @ sk_B @ sk_G )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['106','112'])).

thf('114',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('115',plain,
    ( ( m1_connsp_2 @ ( sk_D @ ( u1_struct_0 @ sk_D_2 ) @ sk_G @ sk_B ) @ sk_B @ sk_G )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    m1_connsp_2 @ ( sk_D @ ( u1_struct_0 @ sk_D_2 ) @ sk_G @ sk_B ) @ sk_B @ sk_G ),
    inference(clc,[status(thm)],['115','116'])).

thf('118',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_2 )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['93','105','117'])).

thf('119',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F ) ),
    inference(split,[status(esa)],['65'])).

thf('120',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F ) ),
    inference(split,[status(esa)],['37'])).

thf('123',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G ) ),
    inference(split,[status(esa)],['41'])).

thf('126',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F ) ),
    inference('sat_resolution*',[status(thm)],['42','73','126'])).

thf('128',plain,(
    ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G ) ),
    inference(simpl_trail,[status(thm)],['121','127'])).

thf('129',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['118','128'])).

thf('130',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_2 ) ),
    inference(clc,[status(thm)],['129','130'])).

thf('132',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v2_struct_0 @ sk_D_2 ),
    inference(clc,[status(thm)],['131','132'])).

thf('134',plain,(
    $false ),
    inference(demod,[status(thm)],['0','133'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bEzIn2AN44
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:34:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.21/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.56  % Solved by: fo/fo7.sh
% 0.21/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.56  % done 147 iterations in 0.106s
% 0.21/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.56  % SZS output start Refutation
% 0.21/0.56  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.21/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.56  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.21/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.56  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.56  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.56  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.21/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.56  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.56  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.21/0.56  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.56  thf(sk_G_type, type, sk_G: $i).
% 0.21/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.56  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.56  thf(t66_tmap_1, conjecture,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.56             ( l1_pre_topc @ B ) ) =>
% 0.21/0.56           ( ![C:$i]:
% 0.21/0.56             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.56                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.56                 ( m1_subset_1 @
% 0.21/0.56                   C @ 
% 0.21/0.56                   ( k1_zfmisc_1 @
% 0.21/0.56                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.56               ( ![D:$i]:
% 0.21/0.56                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.21/0.56                   ( ![E:$i]:
% 0.21/0.56                     ( ( m1_subset_1 @
% 0.21/0.56                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.56                       ( ![F:$i]:
% 0.21/0.56                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.56                           ( ![G:$i]:
% 0.21/0.56                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.56                               ( ( ( v3_pre_topc @ E @ B ) & 
% 0.21/0.56                                   ( r2_hidden @ F @ E ) & 
% 0.21/0.56                                   ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.21/0.56                                   ( ( F ) = ( G ) ) ) =>
% 0.21/0.56                                 ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.21/0.56                                   ( r1_tmap_1 @
% 0.21/0.56                                     D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.56    (~( ![A:$i]:
% 0.21/0.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.56            ( l1_pre_topc @ A ) ) =>
% 0.21/0.56          ( ![B:$i]:
% 0.21/0.56            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.56                ( l1_pre_topc @ B ) ) =>
% 0.21/0.56              ( ![C:$i]:
% 0.21/0.56                ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.56                    ( v1_funct_2 @
% 0.21/0.56                      C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.56                    ( m1_subset_1 @
% 0.21/0.56                      C @ 
% 0.21/0.56                      ( k1_zfmisc_1 @
% 0.21/0.56                        ( k2_zfmisc_1 @
% 0.21/0.56                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.56                  ( ![D:$i]:
% 0.21/0.56                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.21/0.56                      ( ![E:$i]:
% 0.21/0.56                        ( ( m1_subset_1 @
% 0.21/0.56                            E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.56                          ( ![F:$i]:
% 0.21/0.56                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.56                              ( ![G:$i]:
% 0.21/0.56                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.56                                  ( ( ( v3_pre_topc @ E @ B ) & 
% 0.21/0.56                                      ( r2_hidden @ F @ E ) & 
% 0.21/0.56                                      ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.21/0.56                                      ( ( F ) = ( G ) ) ) =>
% 0.21/0.56                                    ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.21/0.56                                      ( r1_tmap_1 @
% 0.21/0.56                                        D @ A @ 
% 0.21/0.56                                        ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.56    inference('cnf.neg', [status(esa)], [t66_tmap_1])).
% 0.21/0.56  thf('0', plain, (~ (v2_struct_0 @ sk_D_2)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('1', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_B))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('2', plain, (((sk_F) = (sk_G))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('3', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.21/0.56      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.56  thf('4', plain, ((m1_pre_topc @ sk_D_2 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(t1_tsep_1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( l1_pre_topc @ A ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.56           ( m1_subset_1 @
% 0.21/0.56             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.56  thf('5', plain,
% 0.21/0.56      (![X10 : $i, X11 : $i]:
% 0.21/0.56         (~ (m1_pre_topc @ X10 @ X11)
% 0.21/0.56          | (m1_subset_1 @ (u1_struct_0 @ X10) @ 
% 0.21/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.21/0.56          | ~ (l1_pre_topc @ X11))),
% 0.21/0.56      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.21/0.56  thf('6', plain,
% 0.21/0.56      ((~ (l1_pre_topc @ sk_B)
% 0.21/0.56        | (m1_subset_1 @ (u1_struct_0 @ sk_D_2) @ 
% 0.21/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.56  thf('7', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('8', plain,
% 0.21/0.56      ((m1_subset_1 @ (u1_struct_0 @ sk_D_2) @ 
% 0.21/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.56      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.56  thf('9', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(t8_connsp_2, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.56           ( ![C:$i]:
% 0.21/0.56             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.56               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.21/0.56                 ( ?[D:$i]:
% 0.21/0.56                   ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.21/0.56                     ( v3_pre_topc @ D @ A ) & 
% 0.21/0.56                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.56  thf('10', plain,
% 0.21/0.56      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X7))
% 0.21/0.56          | ~ (r2_hidden @ X6 @ X9)
% 0.21/0.56          | ~ (r1_tarski @ X9 @ X8)
% 0.21/0.56          | ~ (v3_pre_topc @ X9 @ X7)
% 0.21/0.56          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.21/0.56          | (m1_connsp_2 @ X8 @ X7 @ X6)
% 0.21/0.56          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.21/0.56          | ~ (l1_pre_topc @ X7)
% 0.21/0.56          | ~ (v2_pre_topc @ X7)
% 0.21/0.56          | (v2_struct_0 @ X7))),
% 0.21/0.56      inference('cnf', [status(esa)], [t8_connsp_2])).
% 0.21/0.56  thf('11', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_B)
% 0.21/0.56          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.56          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.56          | (m1_connsp_2 @ X0 @ sk_B @ X1)
% 0.21/0.56          | ~ (v3_pre_topc @ sk_E @ sk_B)
% 0.21/0.56          | ~ (r1_tarski @ sk_E @ X0)
% 0.21/0.56          | ~ (r2_hidden @ X1 @ sk_E)
% 0.21/0.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.56  thf('12', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('13', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('14', plain, ((v3_pre_topc @ sk_E @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('15', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_B)
% 0.21/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.56          | (m1_connsp_2 @ X0 @ sk_B @ X1)
% 0.21/0.56          | ~ (r1_tarski @ sk_E @ X0)
% 0.21/0.56          | ~ (r2_hidden @ X1 @ sk_E)
% 0.21/0.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.56      inference('demod', [status(thm)], ['11', '12', '13', '14'])).
% 0.21/0.56  thf('16', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.21/0.56          | ~ (r2_hidden @ X0 @ sk_E)
% 0.21/0.56          | ~ (r1_tarski @ sk_E @ (u1_struct_0 @ sk_D_2))
% 0.21/0.56          | (m1_connsp_2 @ (u1_struct_0 @ sk_D_2) @ sk_B @ X0)
% 0.21/0.56          | (v2_struct_0 @ sk_B))),
% 0.21/0.56      inference('sup-', [status(thm)], ['8', '15'])).
% 0.21/0.56  thf('17', plain, ((r1_tarski @ sk_E @ (u1_struct_0 @ sk_D_2))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('18', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.21/0.56          | ~ (r2_hidden @ X0 @ sk_E)
% 0.21/0.56          | (m1_connsp_2 @ (u1_struct_0 @ sk_D_2) @ sk_B @ X0)
% 0.21/0.56          | (v2_struct_0 @ sk_B))),
% 0.21/0.56      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.56  thf('19', plain,
% 0.21/0.56      (((v2_struct_0 @ sk_B)
% 0.21/0.56        | (m1_connsp_2 @ (u1_struct_0 @ sk_D_2) @ sk_B @ sk_G)
% 0.21/0.56        | ~ (r2_hidden @ sk_G @ sk_E))),
% 0.21/0.56      inference('sup-', [status(thm)], ['3', '18'])).
% 0.21/0.56  thf('20', plain, ((r2_hidden @ sk_F @ sk_E)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('21', plain, (((sk_F) = (sk_G))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('22', plain, ((r2_hidden @ sk_G @ sk_E)),
% 0.21/0.56      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.56  thf('23', plain,
% 0.21/0.56      (((v2_struct_0 @ sk_B)
% 0.21/0.56        | (m1_connsp_2 @ (u1_struct_0 @ sk_D_2) @ sk_B @ sk_G))),
% 0.21/0.56      inference('demod', [status(thm)], ['19', '22'])).
% 0.21/0.56  thf('24', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('25', plain, ((m1_connsp_2 @ (u1_struct_0 @ sk_D_2) @ sk_B @ sk_G)),
% 0.21/0.56      inference('clc', [status(thm)], ['23', '24'])).
% 0.21/0.56  thf('26', plain,
% 0.21/0.56      ((m1_subset_1 @ (u1_struct_0 @ sk_D_2) @ 
% 0.21/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.56      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.56  thf(t7_connsp_2, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.56           ( ![C:$i]:
% 0.21/0.56             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.56               ( ~( ( m1_connsp_2 @ C @ A @ B ) & 
% 0.21/0.56                    ( ![D:$i]:
% 0.21/0.56                      ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.21/0.56                          ( m1_subset_1 @
% 0.21/0.56                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.56                        ( ~( ( m1_connsp_2 @ D @ A @ B ) & 
% 0.21/0.56                             ( v3_pre_topc @ D @ A ) & ( r1_tarski @ D @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.56  thf('27', plain,
% 0.21/0.56      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4))
% 0.21/0.56          | (m1_subset_1 @ (sk_D @ X5 @ X3 @ X4) @ 
% 0.21/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.21/0.56          | ~ (m1_connsp_2 @ X5 @ X4 @ X3)
% 0.21/0.56          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.21/0.56          | ~ (l1_pre_topc @ X4)
% 0.21/0.56          | ~ (v2_pre_topc @ X4)
% 0.21/0.56          | (v2_struct_0 @ X4))),
% 0.21/0.56      inference('cnf', [status(esa)], [t7_connsp_2])).
% 0.21/0.56  thf('28', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_B)
% 0.21/0.56          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.56          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.56          | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_D_2) @ sk_B @ X0)
% 0.21/0.56          | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ sk_D_2) @ X0 @ sk_B) @ 
% 0.21/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.56  thf('29', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('30', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('31', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_B)
% 0.21/0.56          | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_D_2) @ sk_B @ X0)
% 0.21/0.56          | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ sk_D_2) @ X0 @ sk_B) @ 
% 0.21/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.56      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.21/0.56  thf('32', plain,
% 0.21/0.56      ((~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))
% 0.21/0.56        | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ sk_D_2) @ sk_G @ sk_B) @ 
% 0.21/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.56        | (v2_struct_0 @ sk_B))),
% 0.21/0.56      inference('sup-', [status(thm)], ['25', '31'])).
% 0.21/0.56  thf('33', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.21/0.56      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.56  thf('34', plain,
% 0.21/0.56      (((m1_subset_1 @ (sk_D @ (u1_struct_0 @ sk_D_2) @ sk_G @ sk_B) @ 
% 0.21/0.56         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.56        | (v2_struct_0 @ sk_B))),
% 0.21/0.56      inference('demod', [status(thm)], ['32', '33'])).
% 0.21/0.56  thf('35', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('36', plain,
% 0.21/0.56      ((m1_subset_1 @ (sk_D @ (u1_struct_0 @ sk_D_2) @ sk_G @ sk_B) @ 
% 0.21/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.56      inference('clc', [status(thm)], ['34', '35'])).
% 0.21/0.56  thf('37', plain,
% 0.21/0.56      (((r1_tmap_1 @ sk_D_2 @ sk_A @ 
% 0.21/0.56         (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_2) @ sk_G)
% 0.21/0.56        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('38', plain,
% 0.21/0.56      (((r1_tmap_1 @ sk_D_2 @ sk_A @ 
% 0.21/0.56         (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_2) @ sk_G))
% 0.21/0.56         <= (((r1_tmap_1 @ sk_D_2 @ sk_A @ 
% 0.21/0.56               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_2) @ sk_G)))),
% 0.21/0.56      inference('split', [status(esa)], ['37'])).
% 0.21/0.56  thf('39', plain,
% 0.21/0.56      ((~ (r1_tmap_1 @ sk_D_2 @ sk_A @ 
% 0.21/0.56           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_2) @ sk_G)
% 0.21/0.56        | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('40', plain, (((sk_F) = (sk_G))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('41', plain,
% 0.21/0.56      ((~ (r1_tmap_1 @ sk_D_2 @ sk_A @ 
% 0.21/0.56           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_2) @ sk_G)
% 0.21/0.56        | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G))),
% 0.21/0.56      inference('demod', [status(thm)], ['39', '40'])).
% 0.21/0.56  thf('42', plain,
% 0.21/0.56      (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G)) | 
% 0.21/0.56       ~
% 0.21/0.56       ((r1_tmap_1 @ sk_D_2 @ sk_A @ 
% 0.21/0.56         (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_2) @ sk_G))),
% 0.21/0.56      inference('split', [status(esa)], ['41'])).
% 0.21/0.56  thf('43', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D_2))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('44', plain,
% 0.21/0.56      (((r1_tmap_1 @ sk_D_2 @ sk_A @ 
% 0.21/0.56         (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_2) @ sk_G)
% 0.21/0.56        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('45', plain, (((sk_F) = (sk_G))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('46', plain,
% 0.21/0.56      (((r1_tmap_1 @ sk_D_2 @ sk_A @ 
% 0.21/0.56         (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_2) @ sk_G)
% 0.21/0.56        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G))),
% 0.21/0.56      inference('demod', [status(thm)], ['44', '45'])).
% 0.21/0.56  thf('47', plain,
% 0.21/0.56      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G))
% 0.21/0.56         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G)))),
% 0.21/0.56      inference('split', [status(esa)], ['46'])).
% 0.21/0.56  thf('48', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C @ 
% 0.21/0.56        (k1_zfmisc_1 @ 
% 0.21/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(t64_tmap_1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.56             ( l1_pre_topc @ B ) ) =>
% 0.21/0.56           ( ![C:$i]:
% 0.21/0.56             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.56                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.56                 ( m1_subset_1 @
% 0.21/0.56                   C @ 
% 0.21/0.56                   ( k1_zfmisc_1 @
% 0.21/0.56                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.56               ( ![D:$i]:
% 0.21/0.56                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.21/0.56                   ( ![E:$i]:
% 0.21/0.56                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.56                       ( ![F:$i]:
% 0.21/0.56                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.56                           ( ( ( ( E ) = ( F ) ) & 
% 0.21/0.56                               ( r1_tmap_1 @ B @ A @ C @ E ) ) =>
% 0.21/0.56                             ( r1_tmap_1 @
% 0.21/0.56                               D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.56  thf('49', plain,
% 0.21/0.56      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.56         ((v2_struct_0 @ X12)
% 0.21/0.56          | ~ (v2_pre_topc @ X12)
% 0.21/0.56          | ~ (l1_pre_topc @ X12)
% 0.21/0.56          | (v2_struct_0 @ X13)
% 0.21/0.56          | ~ (m1_pre_topc @ X13 @ X12)
% 0.21/0.56          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.21/0.56          | (r1_tmap_1 @ X13 @ X15 @ (k2_tmap_1 @ X12 @ X15 @ X16 @ X13) @ X14)
% 0.21/0.56          | ((X17) != (X14))
% 0.21/0.56          | ~ (r1_tmap_1 @ X12 @ X15 @ X16 @ X17)
% 0.21/0.56          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X12))
% 0.21/0.56          | ~ (m1_subset_1 @ X16 @ 
% 0.21/0.56               (k1_zfmisc_1 @ 
% 0.21/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X15))))
% 0.21/0.56          | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X15))
% 0.21/0.56          | ~ (v1_funct_1 @ X16)
% 0.21/0.56          | ~ (l1_pre_topc @ X15)
% 0.21/0.56          | ~ (v2_pre_topc @ X15)
% 0.21/0.56          | (v2_struct_0 @ X15))),
% 0.21/0.56      inference('cnf', [status(esa)], [t64_tmap_1])).
% 0.21/0.56  thf('50', plain,
% 0.21/0.56      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.56         ((v2_struct_0 @ X15)
% 0.21/0.56          | ~ (v2_pre_topc @ X15)
% 0.21/0.56          | ~ (l1_pre_topc @ X15)
% 0.21/0.56          | ~ (v1_funct_1 @ X16)
% 0.21/0.56          | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X15))
% 0.21/0.56          | ~ (m1_subset_1 @ X16 @ 
% 0.21/0.56               (k1_zfmisc_1 @ 
% 0.21/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X15))))
% 0.21/0.56          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X12))
% 0.21/0.56          | ~ (r1_tmap_1 @ X12 @ X15 @ X16 @ X14)
% 0.21/0.56          | (r1_tmap_1 @ X13 @ X15 @ (k2_tmap_1 @ X12 @ X15 @ X16 @ X13) @ X14)
% 0.21/0.56          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.21/0.56          | ~ (m1_pre_topc @ X13 @ X12)
% 0.21/0.56          | (v2_struct_0 @ X13)
% 0.21/0.56          | ~ (l1_pre_topc @ X12)
% 0.21/0.56          | ~ (v2_pre_topc @ X12)
% 0.21/0.56          | (v2_struct_0 @ X12))),
% 0.21/0.56      inference('simplify', [status(thm)], ['49'])).
% 0.21/0.56  thf('51', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_B)
% 0.21/0.56          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.56          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.56          | (v2_struct_0 @ X0)
% 0.21/0.56          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.56          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ X1)
% 0.21/0.56          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1)
% 0.21/0.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.21/0.56          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.21/0.56          | ~ (v1_funct_1 @ sk_C)
% 0.21/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.56          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.56          | (v2_struct_0 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['48', '50'])).
% 0.21/0.56  thf('52', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('53', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('54', plain,
% 0.21/0.56      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('55', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('57', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('58', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_B)
% 0.21/0.56          | (v2_struct_0 @ X0)
% 0.21/0.56          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.56          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ X1)
% 0.21/0.56          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1)
% 0.21/0.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.21/0.56          | (v2_struct_0 @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)],
% 0.21/0.56                ['51', '52', '53', '54', '55', '56', '57'])).
% 0.21/0.56  thf('59', plain,
% 0.21/0.56      ((![X0 : $i]:
% 0.21/0.56          ((v2_struct_0 @ sk_A)
% 0.21/0.56           | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))
% 0.21/0.56           | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.21/0.56              sk_G)
% 0.21/0.56           | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ X0))
% 0.21/0.56           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.56           | (v2_struct_0 @ X0)
% 0.21/0.56           | (v2_struct_0 @ sk_B)))
% 0.21/0.56         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['47', '58'])).
% 0.21/0.56  thf('60', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.21/0.56      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.56  thf('61', plain,
% 0.21/0.56      ((![X0 : $i]:
% 0.21/0.56          ((v2_struct_0 @ sk_A)
% 0.21/0.56           | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.21/0.56              sk_G)
% 0.21/0.56           | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ X0))
% 0.21/0.56           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.56           | (v2_struct_0 @ X0)
% 0.21/0.56           | (v2_struct_0 @ sk_B)))
% 0.21/0.56         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G)))),
% 0.21/0.56      inference('demod', [status(thm)], ['59', '60'])).
% 0.21/0.56  thf('62', plain,
% 0.21/0.56      ((((v2_struct_0 @ sk_B)
% 0.21/0.56         | (v2_struct_0 @ sk_D_2)
% 0.21/0.56         | ~ (m1_pre_topc @ sk_D_2 @ sk_B)
% 0.21/0.56         | (r1_tmap_1 @ sk_D_2 @ sk_A @ 
% 0.21/0.56            (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_2) @ sk_G)
% 0.21/0.56         | (v2_struct_0 @ sk_A)))
% 0.21/0.56         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['43', '61'])).
% 0.21/0.56  thf('63', plain, ((m1_pre_topc @ sk_D_2 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('64', plain,
% 0.21/0.56      ((((v2_struct_0 @ sk_B)
% 0.21/0.56         | (v2_struct_0 @ sk_D_2)
% 0.21/0.56         | (r1_tmap_1 @ sk_D_2 @ sk_A @ 
% 0.21/0.56            (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_2) @ sk_G)
% 0.21/0.56         | (v2_struct_0 @ sk_A)))
% 0.21/0.56         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G)))),
% 0.21/0.56      inference('demod', [status(thm)], ['62', '63'])).
% 0.21/0.56  thf('65', plain,
% 0.21/0.56      ((~ (r1_tmap_1 @ sk_D_2 @ sk_A @ 
% 0.21/0.56           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_2) @ sk_G)
% 0.21/0.56        | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('66', plain,
% 0.21/0.56      ((~ (r1_tmap_1 @ sk_D_2 @ sk_A @ 
% 0.21/0.56           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_2) @ sk_G))
% 0.21/0.56         <= (~
% 0.21/0.56             ((r1_tmap_1 @ sk_D_2 @ sk_A @ 
% 0.21/0.56               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_2) @ sk_G)))),
% 0.21/0.56      inference('split', [status(esa)], ['65'])).
% 0.21/0.56  thf('67', plain,
% 0.21/0.56      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D_2) | (v2_struct_0 @ sk_B)))
% 0.21/0.56         <= (~
% 0.21/0.56             ((r1_tmap_1 @ sk_D_2 @ sk_A @ 
% 0.21/0.56               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_2) @ sk_G)) & 
% 0.21/0.56             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['64', '66'])).
% 0.21/0.56  thf('68', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('69', plain,
% 0.21/0.56      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D_2)))
% 0.21/0.56         <= (~
% 0.21/0.56             ((r1_tmap_1 @ sk_D_2 @ sk_A @ 
% 0.21/0.56               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_2) @ sk_G)) & 
% 0.21/0.56             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G)))),
% 0.21/0.56      inference('clc', [status(thm)], ['67', '68'])).
% 0.21/0.56  thf('70', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('71', plain,
% 0.21/0.56      (((v2_struct_0 @ sk_D_2))
% 0.21/0.56         <= (~
% 0.21/0.56             ((r1_tmap_1 @ sk_D_2 @ sk_A @ 
% 0.21/0.56               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_2) @ sk_G)) & 
% 0.21/0.56             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G)))),
% 0.21/0.56      inference('clc', [status(thm)], ['69', '70'])).
% 0.21/0.56  thf('72', plain, (~ (v2_struct_0 @ sk_D_2)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('73', plain,
% 0.21/0.56      (((r1_tmap_1 @ sk_D_2 @ sk_A @ 
% 0.21/0.56         (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_2) @ sk_G)) | 
% 0.21/0.56       ~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G))),
% 0.21/0.56      inference('sup-', [status(thm)], ['71', '72'])).
% 0.21/0.56  thf('74', plain,
% 0.21/0.56      (((r1_tmap_1 @ sk_D_2 @ sk_A @ 
% 0.21/0.56         (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_2) @ sk_G)) | 
% 0.21/0.56       ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G))),
% 0.21/0.56      inference('split', [status(esa)], ['46'])).
% 0.21/0.56  thf('75', plain,
% 0.21/0.56      (((r1_tmap_1 @ sk_D_2 @ sk_A @ 
% 0.21/0.56         (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_2) @ sk_G))),
% 0.21/0.56      inference('sat_resolution*', [status(thm)], ['42', '73', '74'])).
% 0.21/0.56  thf('76', plain,
% 0.21/0.56      ((r1_tmap_1 @ sk_D_2 @ sk_A @ 
% 0.21/0.56        (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_2) @ sk_G)),
% 0.21/0.56      inference('simpl_trail', [status(thm)], ['38', '75'])).
% 0.21/0.56  thf('77', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C @ 
% 0.21/0.56        (k1_zfmisc_1 @ 
% 0.21/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(t65_tmap_1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.56             ( l1_pre_topc @ B ) ) =>
% 0.21/0.56           ( ![C:$i]:
% 0.21/0.56             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.56                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.56                 ( m1_subset_1 @
% 0.21/0.56                   C @ 
% 0.21/0.56                   ( k1_zfmisc_1 @
% 0.21/0.56                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.56               ( ![D:$i]:
% 0.21/0.56                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.21/0.56                   ( ![E:$i]:
% 0.21/0.56                     ( ( m1_subset_1 @
% 0.21/0.56                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.56                       ( ![F:$i]:
% 0.21/0.56                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.56                           ( ![G:$i]:
% 0.21/0.56                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.56                               ( ( ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.21/0.56                                   ( m1_connsp_2 @ E @ B @ F ) & 
% 0.21/0.56                                   ( ( F ) = ( G ) ) ) =>
% 0.21/0.56                                 ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.21/0.56                                   ( r1_tmap_1 @
% 0.21/0.56                                     D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.56  thf('78', plain,
% 0.21/0.56      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.56         ((v2_struct_0 @ X18)
% 0.21/0.56          | ~ (v2_pre_topc @ X18)
% 0.21/0.56          | ~ (l1_pre_topc @ X18)
% 0.21/0.56          | (v2_struct_0 @ X19)
% 0.21/0.56          | ~ (m1_pre_topc @ X19 @ X18)
% 0.21/0.56          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X18))
% 0.21/0.56          | ~ (r1_tarski @ X21 @ (u1_struct_0 @ X19))
% 0.21/0.56          | ~ (m1_connsp_2 @ X21 @ X18 @ X20)
% 0.21/0.56          | ((X20) != (X22))
% 0.21/0.56          | ~ (r1_tmap_1 @ X19 @ X23 @ (k2_tmap_1 @ X18 @ X23 @ X24 @ X19) @ 
% 0.21/0.56               X22)
% 0.21/0.56          | (r1_tmap_1 @ X18 @ X23 @ X24 @ X20)
% 0.21/0.56          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X19))
% 0.21/0.56          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.21/0.56          | ~ (m1_subset_1 @ X24 @ 
% 0.21/0.56               (k1_zfmisc_1 @ 
% 0.21/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X23))))
% 0.21/0.56          | ~ (v1_funct_2 @ X24 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X23))
% 0.21/0.56          | ~ (v1_funct_1 @ X24)
% 0.21/0.56          | ~ (l1_pre_topc @ X23)
% 0.21/0.56          | ~ (v2_pre_topc @ X23)
% 0.21/0.56          | (v2_struct_0 @ X23))),
% 0.21/0.56      inference('cnf', [status(esa)], [t65_tmap_1])).
% 0.21/0.56  thf('79', plain,
% 0.21/0.56      (![X18 : $i, X19 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.56         ((v2_struct_0 @ X23)
% 0.21/0.56          | ~ (v2_pre_topc @ X23)
% 0.21/0.56          | ~ (l1_pre_topc @ X23)
% 0.21/0.56          | ~ (v1_funct_1 @ X24)
% 0.21/0.56          | ~ (v1_funct_2 @ X24 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X23))
% 0.21/0.56          | ~ (m1_subset_1 @ X24 @ 
% 0.21/0.56               (k1_zfmisc_1 @ 
% 0.21/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X23))))
% 0.21/0.56          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.21/0.56          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X19))
% 0.21/0.56          | (r1_tmap_1 @ X18 @ X23 @ X24 @ X22)
% 0.21/0.56          | ~ (r1_tmap_1 @ X19 @ X23 @ (k2_tmap_1 @ X18 @ X23 @ X24 @ X19) @ 
% 0.21/0.56               X22)
% 0.21/0.56          | ~ (m1_connsp_2 @ X21 @ X18 @ X22)
% 0.21/0.56          | ~ (r1_tarski @ X21 @ (u1_struct_0 @ X19))
% 0.21/0.56          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X18))
% 0.21/0.56          | ~ (m1_pre_topc @ X19 @ X18)
% 0.21/0.56          | (v2_struct_0 @ X19)
% 0.21/0.56          | ~ (l1_pre_topc @ X18)
% 0.21/0.56          | ~ (v2_pre_topc @ X18)
% 0.21/0.56          | (v2_struct_0 @ X18))),
% 0.21/0.56      inference('simplify', [status(thm)], ['78'])).
% 0.21/0.56  thf('80', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_B)
% 0.21/0.56          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.56          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.56          | (v2_struct_0 @ X0)
% 0.21/0.56          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.21/0.56          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.56          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.21/0.56          | ~ (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.21/0.56               X1)
% 0.21/0.56          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1)
% 0.21/0.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.56          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.56          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.21/0.56          | ~ (v1_funct_1 @ sk_C)
% 0.21/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.56          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.56          | (v2_struct_0 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['77', '79'])).
% 0.21/0.56  thf('81', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('82', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('83', plain,
% 0.21/0.56      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('84', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('86', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('87', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_B)
% 0.21/0.56          | (v2_struct_0 @ X0)
% 0.21/0.56          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.21/0.56          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.56          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.21/0.56          | ~ (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.21/0.56               X1)
% 0.21/0.56          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1)
% 0.21/0.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.56          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.56          | (v2_struct_0 @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)],
% 0.21/0.56                ['80', '81', '82', '83', '84', '85', '86'])).
% 0.21/0.56  thf('88', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_A)
% 0.21/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.56          | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D_2))
% 0.21/0.56          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G)
% 0.21/0.56          | ~ (m1_connsp_2 @ X0 @ sk_B @ sk_G)
% 0.21/0.56          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D_2))
% 0.21/0.56          | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))
% 0.21/0.56          | ~ (m1_pre_topc @ sk_D_2 @ sk_B)
% 0.21/0.56          | (v2_struct_0 @ sk_D_2)
% 0.21/0.56          | (v2_struct_0 @ sk_B))),
% 0.21/0.56      inference('sup-', [status(thm)], ['76', '87'])).
% 0.21/0.56  thf('89', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D_2))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('90', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.21/0.56      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.56  thf('91', plain, ((m1_pre_topc @ sk_D_2 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('92', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_A)
% 0.21/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.56          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G)
% 0.21/0.56          | ~ (m1_connsp_2 @ X0 @ sk_B @ sk_G)
% 0.21/0.56          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D_2))
% 0.21/0.56          | (v2_struct_0 @ sk_D_2)
% 0.21/0.56          | (v2_struct_0 @ sk_B))),
% 0.21/0.56      inference('demod', [status(thm)], ['88', '89', '90', '91'])).
% 0.21/0.56  thf('93', plain,
% 0.21/0.56      (((v2_struct_0 @ sk_B)
% 0.21/0.56        | (v2_struct_0 @ sk_D_2)
% 0.21/0.56        | ~ (r1_tarski @ (sk_D @ (u1_struct_0 @ sk_D_2) @ sk_G @ sk_B) @ 
% 0.21/0.56             (u1_struct_0 @ sk_D_2))
% 0.21/0.56        | ~ (m1_connsp_2 @ (sk_D @ (u1_struct_0 @ sk_D_2) @ sk_G @ sk_B) @ 
% 0.21/0.56             sk_B @ sk_G)
% 0.21/0.56        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G)
% 0.21/0.56        | (v2_struct_0 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['36', '92'])).
% 0.21/0.56  thf('94', plain, ((m1_connsp_2 @ (u1_struct_0 @ sk_D_2) @ sk_B @ sk_G)),
% 0.21/0.56      inference('clc', [status(thm)], ['23', '24'])).
% 0.21/0.56  thf('95', plain,
% 0.21/0.56      ((m1_subset_1 @ (u1_struct_0 @ sk_D_2) @ 
% 0.21/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.56      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.56  thf('96', plain,
% 0.21/0.56      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4))
% 0.21/0.56          | (r1_tarski @ (sk_D @ X5 @ X3 @ X4) @ X5)
% 0.21/0.56          | ~ (m1_connsp_2 @ X5 @ X4 @ X3)
% 0.21/0.56          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.21/0.56          | ~ (l1_pre_topc @ X4)
% 0.21/0.56          | ~ (v2_pre_topc @ X4)
% 0.21/0.56          | (v2_struct_0 @ X4))),
% 0.21/0.56      inference('cnf', [status(esa)], [t7_connsp_2])).
% 0.21/0.56  thf('97', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_B)
% 0.21/0.56          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.56          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.56          | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_D_2) @ sk_B @ X0)
% 0.21/0.56          | (r1_tarski @ (sk_D @ (u1_struct_0 @ sk_D_2) @ X0 @ sk_B) @ 
% 0.21/0.56             (u1_struct_0 @ sk_D_2))
% 0.21/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['95', '96'])).
% 0.21/0.56  thf('98', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('99', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('100', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_B)
% 0.21/0.56          | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_D_2) @ sk_B @ X0)
% 0.21/0.56          | (r1_tarski @ (sk_D @ (u1_struct_0 @ sk_D_2) @ X0 @ sk_B) @ 
% 0.21/0.56             (u1_struct_0 @ sk_D_2))
% 0.21/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.56      inference('demod', [status(thm)], ['97', '98', '99'])).
% 0.21/0.56  thf('101', plain,
% 0.21/0.56      ((~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))
% 0.21/0.56        | (r1_tarski @ (sk_D @ (u1_struct_0 @ sk_D_2) @ sk_G @ sk_B) @ 
% 0.21/0.56           (u1_struct_0 @ sk_D_2))
% 0.21/0.56        | (v2_struct_0 @ sk_B))),
% 0.21/0.56      inference('sup-', [status(thm)], ['94', '100'])).
% 0.21/0.56  thf('102', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.21/0.56      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.56  thf('103', plain,
% 0.21/0.56      (((r1_tarski @ (sk_D @ (u1_struct_0 @ sk_D_2) @ sk_G @ sk_B) @ 
% 0.21/0.56         (u1_struct_0 @ sk_D_2))
% 0.21/0.56        | (v2_struct_0 @ sk_B))),
% 0.21/0.56      inference('demod', [status(thm)], ['101', '102'])).
% 0.21/0.56  thf('104', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('105', plain,
% 0.21/0.56      ((r1_tarski @ (sk_D @ (u1_struct_0 @ sk_D_2) @ sk_G @ sk_B) @ 
% 0.21/0.56        (u1_struct_0 @ sk_D_2))),
% 0.21/0.56      inference('clc', [status(thm)], ['103', '104'])).
% 0.21/0.56  thf('106', plain, ((m1_connsp_2 @ (u1_struct_0 @ sk_D_2) @ sk_B @ sk_G)),
% 0.21/0.56      inference('clc', [status(thm)], ['23', '24'])).
% 0.21/0.56  thf('107', plain,
% 0.21/0.56      ((m1_subset_1 @ (u1_struct_0 @ sk_D_2) @ 
% 0.21/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.56      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.56  thf('108', plain,
% 0.21/0.56      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4))
% 0.21/0.56          | (m1_connsp_2 @ (sk_D @ X5 @ X3 @ X4) @ X4 @ X3)
% 0.21/0.56          | ~ (m1_connsp_2 @ X5 @ X4 @ X3)
% 0.21/0.56          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.21/0.56          | ~ (l1_pre_topc @ X4)
% 0.21/0.56          | ~ (v2_pre_topc @ X4)
% 0.21/0.56          | (v2_struct_0 @ X4))),
% 0.21/0.56      inference('cnf', [status(esa)], [t7_connsp_2])).
% 0.21/0.56  thf('109', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_B)
% 0.21/0.56          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.56          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.56          | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_D_2) @ sk_B @ X0)
% 0.21/0.56          | (m1_connsp_2 @ (sk_D @ (u1_struct_0 @ sk_D_2) @ X0 @ sk_B) @ 
% 0.21/0.56             sk_B @ X0)
% 0.21/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['107', '108'])).
% 0.21/0.56  thf('110', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('111', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('112', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_B)
% 0.21/0.56          | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_D_2) @ sk_B @ X0)
% 0.21/0.56          | (m1_connsp_2 @ (sk_D @ (u1_struct_0 @ sk_D_2) @ X0 @ sk_B) @ 
% 0.21/0.56             sk_B @ X0)
% 0.21/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.56      inference('demod', [status(thm)], ['109', '110', '111'])).
% 0.21/0.56  thf('113', plain,
% 0.21/0.56      ((~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))
% 0.21/0.56        | (m1_connsp_2 @ (sk_D @ (u1_struct_0 @ sk_D_2) @ sk_G @ sk_B) @ 
% 0.21/0.56           sk_B @ sk_G)
% 0.21/0.56        | (v2_struct_0 @ sk_B))),
% 0.21/0.56      inference('sup-', [status(thm)], ['106', '112'])).
% 0.21/0.56  thf('114', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.21/0.56      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.56  thf('115', plain,
% 0.21/0.56      (((m1_connsp_2 @ (sk_D @ (u1_struct_0 @ sk_D_2) @ sk_G @ sk_B) @ sk_B @ 
% 0.21/0.56         sk_G)
% 0.21/0.56        | (v2_struct_0 @ sk_B))),
% 0.21/0.56      inference('demod', [status(thm)], ['113', '114'])).
% 0.21/0.56  thf('116', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('117', plain,
% 0.21/0.56      ((m1_connsp_2 @ (sk_D @ (u1_struct_0 @ sk_D_2) @ sk_G @ sk_B) @ sk_B @ 
% 0.21/0.56        sk_G)),
% 0.21/0.56      inference('clc', [status(thm)], ['115', '116'])).
% 0.21/0.56  thf('118', plain,
% 0.21/0.56      (((v2_struct_0 @ sk_B)
% 0.21/0.56        | (v2_struct_0 @ sk_D_2)
% 0.21/0.56        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G)
% 0.21/0.56        | (v2_struct_0 @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['93', '105', '117'])).
% 0.21/0.56  thf('119', plain,
% 0.21/0.56      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F))
% 0.21/0.56         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F)))),
% 0.21/0.56      inference('split', [status(esa)], ['65'])).
% 0.21/0.56  thf('120', plain, (((sk_F) = (sk_G))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('121', plain,
% 0.21/0.56      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G))
% 0.21/0.56         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F)))),
% 0.21/0.56      inference('demod', [status(thm)], ['119', '120'])).
% 0.21/0.56  thf('122', plain,
% 0.21/0.56      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F))
% 0.21/0.56         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F)))),
% 0.21/0.56      inference('split', [status(esa)], ['37'])).
% 0.21/0.56  thf('123', plain, (((sk_F) = (sk_G))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('124', plain,
% 0.21/0.56      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G))
% 0.21/0.56         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F)))),
% 0.21/0.56      inference('demod', [status(thm)], ['122', '123'])).
% 0.21/0.56  thf('125', plain,
% 0.21/0.56      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G))
% 0.21/0.56         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G)))),
% 0.21/0.56      inference('split', [status(esa)], ['41'])).
% 0.21/0.56  thf('126', plain,
% 0.21/0.56      (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F)) | 
% 0.21/0.56       ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G))),
% 0.21/0.56      inference('sup-', [status(thm)], ['124', '125'])).
% 0.21/0.56  thf('127', plain, (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F))),
% 0.21/0.56      inference('sat_resolution*', [status(thm)], ['42', '73', '126'])).
% 0.21/0.56  thf('128', plain, (~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G)),
% 0.21/0.56      inference('simpl_trail', [status(thm)], ['121', '127'])).
% 0.21/0.56  thf('129', plain,
% 0.21/0.56      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D_2) | (v2_struct_0 @ sk_B))),
% 0.21/0.56      inference('sup-', [status(thm)], ['118', '128'])).
% 0.21/0.56  thf('130', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('131', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D_2))),
% 0.21/0.56      inference('clc', [status(thm)], ['129', '130'])).
% 0.21/0.56  thf('132', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('133', plain, ((v2_struct_0 @ sk_D_2)),
% 0.21/0.56      inference('clc', [status(thm)], ['131', '132'])).
% 0.21/0.56  thf('134', plain, ($false), inference('demod', [status(thm)], ['0', '133'])).
% 0.21/0.56  
% 0.21/0.56  % SZS output end Refutation
% 0.21/0.56  
% 0.21/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
